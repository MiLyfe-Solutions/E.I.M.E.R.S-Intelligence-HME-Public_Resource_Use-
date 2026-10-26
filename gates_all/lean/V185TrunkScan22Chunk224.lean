import V185TrunkScan22Chunk223

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1997406 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1997406 : Nat := 118140960795 + 1997406 * 2 ^ 59
def prefixEnd_1997406 : Nat := 4983230072969 + 3 ^ 40 * 1997406 * 2
def baseEnd_1997406 : Nat := 683752893449678249026069

theorem tailTrace_1997406 : CollatzResearch.WordTrace tailWord_1997406 prefixEnd_1997406 683752893449678249026069 := by
  unfold tailWord_1997406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9106422725218333328897509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48567587867831111087453381 9106422725218333328897509)
  ·
    refine ⟨1707454260978437499168283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9106422725218333328897509 1707454260978437499168283)
    ·
      refine ⟨2561181391467656248752425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707454260978437499168283 2561181391467656248752425)
      ·
        refine ⟨1920886043600742186564319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2561181391467656248752425 1920886043600742186564319)
        ·
          refine ⟨2881329065401113279846479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920886043600742186564319 2881329065401113279846479)
          ·
            refine ⟨4321993598101669919769719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881329065401113279846479 4321993598101669919769719)
            ·
              refine ⟨6482990397152504879654579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321993598101669919769719 6482990397152504879654579)
              ·
                refine ⟨9724485595728757319481869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482990397152504879654579 9724485595728757319481869)
                ·
                  refine ⟨3646682098398283994805701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9724485595728757319481869 3646682098398283994805701)
                  ·
                    refine ⟨683752893449678249026069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3646682098398283994805701 683752893449678249026069)
                    ·
                      rfl

theorem cell22_1997406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1997406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997406 prefixEnd_1997406 := by exact prefixLift 1997406
  have htrace : WordTrace (prefixWord ++ tailWord_1997406) baseStart_1997406 baseEnd_1997406 := by
    simpa [prefixWord, tailWord_1997406, baseEnd_1997406] using wordTrace_append hprefix tailTrace_1997406
  have hstable : (prefixWord ++ tailWord_1997406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997406).length < 2 ^ (prefixWord ++ tailWord_1997406).sum := by decide
  have hdescent : baseEnd_1997406 < baseStart_1997406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997443 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 7]
def baseStart_1997443 : Nat := 118140960795 + 1997443 * 2 ^ 59
def prefixEnd_1997443 : Nat := 4983230072969 + 3 ^ 40 * 1997443 * 2
def baseEnd_1997443 : Nat := 227921853101940828616985

theorem tailTrace_1997443 : CollatzResearch.WordTrace tailWord_1997443 prefixEnd_1997443 227921853101940828616985 := by
  unfold tailWord_1997443
  simp only [CollatzResearch.WordTrace]
  refine ⟨72852731302612621950276983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48568487535075081300184655 72852731302612621950276983)
  ·
    refine ⟨109279096953918932925415475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72852731302612621950276983 109279096953918932925415475)
    ·
      refine ⟨163918645430878399388123213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109279096953918932925415475 163918645430878399388123213)
      ·
        refine ⟨61469492036579399770546205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163918645430878399388123213 61469492036579399770546205)
        ·
          refine ⟨23051059513717274913954827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61469492036579399770546205 23051059513717274913954827)
          ·
            refine ⟨34576589270575912370932241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23051059513717274913954827 34576589270575912370932241)
            ·
              refine ⟨25932441952931934278199181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34576589270575912370932241 25932441952931934278199181)
              ·
                refine ⟨9724665732349475354324693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25932441952931934278199181 9724665732349475354324693)
                ·
                  refine ⟨227921853101940828616985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9724665732349475354324693 227921853101940828616985)
                  ·
                    rfl

theorem cell22_1997443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 7].length) (baseStart_1997443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997443 prefixEnd_1997443 := by exact prefixLift 1997443
  have htrace : WordTrace (prefixWord ++ tailWord_1997443) baseStart_1997443 baseEnd_1997443 := by
    simpa [prefixWord, tailWord_1997443, baseEnd_1997443] using wordTrace_append hprefix tailTrace_1997443
  have hstable : (prefixWord ++ tailWord_1997443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997443).length < 2 ^ (prefixWord ++ tailWord_1997443).sum := by decide
  have hdescent : baseEnd_1997443 < baseStart_1997443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997488 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 10]
def baseStart_1997488 : Nat := 118140960795 + 1997488 * 2 ^ 59
def prefixEnd_1997488 : Nat := 4983230072969 + 3 ^ 40 * 1997488 * 2
def baseEnd_1997488 : Nat := 227926987908485789491939

theorem tailTrace_1997488 : CollatzResearch.WordTrace tailWord_1997488 prefixEnd_1997488 227926987908485789491939 := by
  unfold tailWord_1997488
  simp only [CollatzResearch.WordTrace]
  refine ⟨36427186293724797317832559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48569581724966396423776745 36427186293724797317832559)
  ·
    refine ⟨54640779440587195976748839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36427186293724797317832559 54640779440587195976748839)
    ·
      refine ⟨81961169160880793965123259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54640779440587195976748839 81961169160880793965123259)
      ·
        refine ⟨122941753741321190947684889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81961169160880793965123259 122941753741321190947684889)
        ·
          refine ⟨92206315305990893210763667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122941753741321190947684889 92206315305990893210763667)
          ·
            refine ⟨138309472958986339816145501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92206315305990893210763667 138309472958986339816145501)
            ·
              refine ⟨51866052359619877431054563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138309472958986339816145501 51866052359619877431054563)
              ·
                refine ⟨77799078539429816146581845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51866052359619877431054563 77799078539429816146581845)
                ·
                  refine ⟨227926987908485789491939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 77799078539429816146581845 227926987908485789491939)
                  ·
                    rfl

theorem cell22_1997488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_1997488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997488 prefixEnd_1997488 := by exact prefixLift 1997488
  have htrace : WordTrace (prefixWord ++ tailWord_1997488) baseStart_1997488 baseEnd_1997488 := by
    simpa [prefixWord, tailWord_1997488, baseEnd_1997488] using wordTrace_append hprefix tailTrace_1997488
  have hstable : (prefixWord ++ tailWord_1997488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997488).length < 2 ^ (prefixWord ++ tailWord_1997488).sum := by decide
  have hdescent : baseEnd_1997488 < baseStart_1997488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997494 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1997494 : Nat := 118140960795 + 1997494 * 2 ^ 59
def prefixEnd_1997494 : Nat := 4983230072969 + 3 ^ 40 * 1997494 * 2
def baseEnd_1997494 : Nat := 227927672549358450941933

theorem tailTrace_1997494 : CollatzResearch.WordTrace tailWord_1997494 prefixEnd_1997494 227927672549358450941933 := by
  unfold tailWord_1997494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553411964089241103773971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48569727616951905106922357 4553411964089241103773971)
  ·
    refine ⟨6830117946133861655660957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4553411964089241103773971 6830117946133861655660957)
    ·
      refine ⟨2561294229800198120872859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6830117946133861655660957 2561294229800198120872859)
      ·
        refine ⟨3841941344700297181309289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561294229800198120872859 3841941344700297181309289)
        ·
          refine ⟨2881456008525222885981967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3841941344700297181309289 2881456008525222885981967)
          ·
            refine ⟨4322184012787834328972951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881456008525222885981967 4322184012787834328972951)
            ·
              refine ⟨6483276019181751493459427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322184012787834328972951 6483276019181751493459427)
              ·
                refine ⟨9724914028772627240189141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483276019181751493459427 9724914028772627240189141)
                ·
                  refine ⟨227927672549358450941933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9724914028772627240189141 227927672549358450941933)
                  ·
                    rfl

theorem cell22_1997494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1997494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997494 prefixEnd_1997494 := by exact prefixLift 1997494
  have htrace : WordTrace (prefixWord ++ tailWord_1997494) baseStart_1997494 baseEnd_1997494 := by
    simpa [prefixWord, tailWord_1997494, baseEnd_1997494] using wordTrace_append hprefix tailTrace_1997494
  have hstable : (prefixWord ++ tailWord_1997494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997494).length < 2 ^ (prefixWord ++ tailWord_1997494).sum := by decide
  have hdescent : baseEnd_1997494 < baseStart_1997494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997535 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 1, 6]
def baseStart_1997535 : Nat := 118140960795 + 1997535 * 2 ^ 59
def prefixEnd_1997535 : Nat := 4983230072969 + 3 ^ 40 * 1997535 * 2
def baseEnd_1997535 : Nat := 683797052785964912550673

theorem tailTrace_1997535 : CollatzResearch.WordTrace tailWord_1997535 prefixEnd_1997535 683797052785964912550673 := by
  unfold tailWord_1997535
  simp only [CollatzResearch.WordTrace]
  refine ⟨72856086818279321662626059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48570724545519547775084039 72856086818279321662626059)
  ·
    refine ⟨109284130227418982493939089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72856086818279321662626059 109284130227418982493939089)
    ·
      refine ⟨81963097670564236870454317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109284130227418982493939089 81963097670564236870454317)
      ·
        refine ⟨30736161626461588826420369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81963097670564236870454317 30736161626461588826420369)
        ·
          refine ⟨23052121219846191619815277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30736161626461588826420369 23052121219846191619815277)
          ·
            refine ⟨8644545457442321857430729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23052121219846191619815277 8644545457442321857430729)
            ·
              refine ⟨6483409093081741393073047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8644545457442321857430729 6483409093081741393073047)
              ·
                refine ⟨9725113639622612089609571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483409093081741393073047 9725113639622612089609571)
                ·
                  refine ⟨14587670459433918134414357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9725113639622612089609571 14587670459433918134414357)
                  ·
                    refine ⟨683797052785964912550673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14587670459433918134414357 683797052785964912550673)
                    ·
                      rfl

theorem cell22_1997535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_1997535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997535 prefixEnd_1997535 := by exact prefixLift 1997535
  have htrace : WordTrace (prefixWord ++ tailWord_1997535) baseStart_1997535 baseEnd_1997535 := by
    simpa [prefixWord, tailWord_1997535, baseEnd_1997535] using wordTrace_append hprefix tailTrace_1997535
  have hstable : (prefixWord ++ tailWord_1997535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997535).length < 2 ^ (prefixWord ++ tailWord_1997535).sum := by decide
  have hdescent : baseEnd_1997535 < baseStart_1997535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997537 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 4, 3]
def baseStart_1997537 : Nat := 118140960795 + 1997537 * 2 ^ 59
def prefixEnd_1997537 : Nat := 4983230072969 + 3 ^ 40 * 1997537 * 2
def baseEnd_1997537 : Nat := 683797737426837574000667

theorem tailTrace_1997537 : CollatzResearch.WordTrace tailWord_1997537 prefixEnd_1997537 683797737426837574000667 := by
  unfold tailWord_1997537
  simp only [CollatzResearch.WordTrace]
  refine ⟨72856159764272076004198865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48570773176181384002799243 72856159764272076004198865)
  ·
    refine ⟨54642119823204057003149149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72856159764272076004198865 54642119823204057003149149)
    ·
      refine ⟨20490794933701521376180931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54642119823204057003149149 20490794933701521376180931)
      ·
        refine ⟨30736192400552282064271397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20490794933701521376180931 30736192400552282064271397)
        ·
          refine ⟨5763036075103552887050887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30736192400552282064271397 5763036075103552887050887)
          ·
            refine ⟨8644554112655329330576331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5763036075103552887050887 8644554112655329330576331)
            ·
              refine ⟨12966831168982993995864497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8644554112655329330576331 12966831168982993995864497)
              ·
                refine ⟨9725123376737245496898373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12966831168982993995864497 9725123376737245496898373)
                ·
                  refine ⟨1823460633138233530668445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9725123376737245496898373 1823460633138233530668445)
                  ·
                    refine ⟨683797737426837574000667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1823460633138233530668445 683797737426837574000667)
                    ·
                      rfl

theorem cell22_1997537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_1997537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997537 prefixEnd_1997537 := by exact prefixLift 1997537
  have htrace : WordTrace (prefixWord ++ tailWord_1997537) baseStart_1997537 baseEnd_1997537 := by
    simpa [prefixWord, tailWord_1997537, baseEnd_1997537] using wordTrace_append hprefix tailTrace_1997537
  have hstable : (prefixWord ++ tailWord_1997537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997537).length < 2 ^ (prefixWord ++ tailWord_1997537).sum := by decide
  have hdescent : baseEnd_1997537 < baseStart_1997537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997539 : List Nat := [1, 1, 1, 7, 1, 1, 3, 3, 4]
def baseStart_1997539 : Nat := 118140960795 + 1997539 * 2 ^ 59
def prefixEnd_1997539 : Nat := 4983230072969 + 3 ^ 40 * 1997539 * 2
def baseEnd_1997539 : Nat := 227932807355903411816887

theorem tailTrace_1997539 : CollatzResearch.WordTrace tailWord_1997539 prefixEnd_1997539 227932807355903411816887 := by
  unfold tailWord_1997539
  simp only [CollatzResearch.WordTrace]
  refine ⟨72856232710264830345771671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48570821806843220230514447 72856232710264830345771671)
  ·
    refine ⟨109284349065397245518657507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72856232710264830345771671 109284349065397245518657507)
    ·
      refine ⟨163926523598095868277986261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109284349065397245518657507 163926523598095868277986261)
      ·
        refine ⟨3842027896830371912765303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 163926523598095868277986261 3842027896830371912765303)
        ·
          refine ⟨5763041845245557869147955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842027896830371912765303 5763041845245557869147955)
          ·
            refine ⟨8644562767868336803721933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5763041845245557869147955 8644562767868336803721933)
            ·
              refine ⟨3241711037950626301395725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8644562767868336803721933 3241711037950626301395725)
              ·
                refine ⟨1215641639231484863023397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3241711037950626301395725 1215641639231484863023397)
                ·
                  refine ⟨227932807355903411816887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215641639231484863023397 227932807355903411816887)
                  ·
                    rfl

theorem cell22_1997539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 4].length) (baseStart_1997539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997539 prefixEnd_1997539 := by exact prefixLift 1997539
  have htrace : WordTrace (prefixWord ++ tailWord_1997539) baseStart_1997539 baseEnd_1997539 := by
    simpa [prefixWord, tailWord_1997539, baseEnd_1997539] using wordTrace_append hprefix tailTrace_1997539
  have hstable : (prefixWord ++ tailWord_1997539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997539).length < 2 ^ (prefixWord ++ tailWord_1997539).sum := by decide
  have hdescent : baseEnd_1997539 < baseStart_1997539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997550 : List Nat := [4, 1, 2, 1, 1, 3, 10]
def baseStart_1997550 : Nat := 118140960795 + 1997550 * 2 ^ 59
def prefixEnd_1997550 : Nat := 4983230072969 + 3 ^ 40 * 1997550 * 2
def baseEnd_1997550 : Nat := 25326006947870736052801

theorem tailTrace_1997550 : CollatzResearch.WordTrace tailWord_1997550 prefixEnd_1997550 25326006947870736052801 := by
  unfold tailWord_1997550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9107079239153122403052763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48571089275483319482948069 9107079239153122403052763)
  ·
    refine ⟨13660618858729683604579145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9107079239153122403052763 13660618858729683604579145)
    ·
      refine ⟨10245464144047262703434359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13660618858729683604579145 10245464144047262703434359)
      ·
        refine ⟨15368196216070894055151539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245464144047262703434359 15368196216070894055151539)
        ·
          refine ⟨23052294324106341082727309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15368196216070894055151539 23052294324106341082727309)
          ·
            refine ⟨8644610371539877906022741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23052294324106341082727309 8644610371539877906022741)
            ·
              refine ⟨25326006947870736052801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8644610371539877906022741 25326006947870736052801)
              ·
                rfl

theorem cell22_1997550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 10].length) (baseStart_1997550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997550 prefixEnd_1997550 := by exact prefixLift 1997550
  have htrace : WordTrace (prefixWord ++ tailWord_1997550) baseStart_1997550 baseEnd_1997550 := by
    simpa [prefixWord, tailWord_1997550, baseEnd_1997550] using wordTrace_append hprefix tailTrace_1997550
  have hstable : (prefixWord ++ tailWord_1997550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997550).length < 2 ^ (prefixWord ++ tailWord_1997550).sum := by decide
  have hdescent : baseEnd_1997550 < baseStart_1997550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997582 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_1997582 : Nat := 118140960795 + 1997582 * 2 ^ 59
def prefixEnd_1997582 : Nat := 4983230072969 + 3 ^ 40 * 1997582 * 2
def baseEnd_1997582 : Nat := 683813141846472456625529

theorem tailTrace_1997582 : CollatzResearch.WordTrace tailWord_1997582 prefixEnd_1997582 683813141846472456625529 := by
  unfold tailWord_1997582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9107225131138631086198375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48571867366072699126391333 9107225131138631086198375)
  ·
    refine ⟨13660837696707946629297563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9107225131138631086198375 13660837696707946629297563)
    ·
      refine ⟨20491256545061919943946345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13660837696707946629297563 20491256545061919943946345)
      ·
        refine ⟨15368442408796439957959759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20491256545061919943946345 15368442408796439957959759)
        ·
          refine ⟨23052663613194659936939639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15368442408796439957959759 23052663613194659936939639)
          ·
            refine ⟨34578995419791989905409459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23052663613194659936939639 34578995419791989905409459)
            ·
              refine ⟨51868493129687984858114189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34578995419791989905409459 51868493129687984858114189)
              ·
                refine ⟨19450684923632994321792821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51868493129687984858114189 19450684923632994321792821)
                ·
                  refine ⟨1823501711590593217668077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19450684923632994321792821 1823501711590593217668077)
                  ·
                    refine ⟨683813141846472456625529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1823501711590593217668077 683813141846472456625529)
                    ·
                      rfl

theorem cell22_1997582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_1997582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997582 prefixEnd_1997582 := by exact prefixLift 1997582
  have htrace : WordTrace (prefixWord ++ tailWord_1997582) baseStart_1997582 baseEnd_1997582 := by
    simpa [prefixWord, tailWord_1997582, baseEnd_1997582] using wordTrace_append hprefix tailTrace_1997582
  have hstable : (prefixWord ++ tailWord_1997582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997582).length < 2 ^ (prefixWord ++ tailWord_1997582).sum := by decide
  have hdescent : baseEnd_1997582 < baseStart_1997582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997586 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1997586 : Nat := 118140960795 + 1997586 * 2 ^ 59
def prefixEnd_1997586 : Nat := 4983230072969 + 3 ^ 40 * 1997586 * 2
def baseEnd_1997586 : Nat := 683814511128217779525517

theorem tailTrace_1997586 : CollatzResearch.WordTrace tailWord_1997586 prefixEnd_1997586 683814511128217779525517 := by
  unfold tailWord_1997586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18214486735273639343183153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48571964627396371581821741 18214486735273639343183153)
  ·
    refine ⟨13660865051455229507387365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18214486735273639343183153 13660865051455229507387365)
    ·
      refine ⟨2561412197147855532635131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13660865051455229507387365 2561412197147855532635131)
      ·
        refine ⟨3842118295721783298952697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561412197147855532635131 3842118295721783298952697)
        ·
          refine ⟨2881588721791337474214523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3842118295721783298952697 2881588721791337474214523)
          ·
            refine ⟨4322383082687006211321785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881588721791337474214523 4322383082687006211321785)
            ·
              refine ⟨3241787312015254658491339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322383082687006211321785 3241787312015254658491339)
              ·
                refine ⟨4862680968022881987737009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241787312015254658491339 4862680968022881987737009)
                ·
                  refine ⟨3647010726017161490802757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4862680968022881987737009 3647010726017161490802757)
                  ·
                    refine ⟨683814511128217779525517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3647010726017161490802757 683814511128217779525517)
                    ·
                      rfl

theorem cell22_1997586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1997586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997586 prefixEnd_1997586 := by exact prefixLift 1997586
  have htrace : WordTrace (prefixWord ++ tailWord_1997586) baseStart_1997586 baseEnd_1997586 := by
    simpa [prefixWord, tailWord_1997586, baseEnd_1997586] using wordTrace_append hprefix tailTrace_1997586
  have hstable : (prefixWord ++ tailWord_1997586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997586).length < 2 ^ (prefixWord ++ tailWord_1997586).sum := by decide
  have hdescent : baseEnd_1997586 < baseStart_1997586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997612 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 5]
def baseStart_1997612 : Nat := 118140960795 + 1997612 * 2 ^ 59
def prefixEnd_1997612 : Nat := 4983230072969 + 3 ^ 40 * 1997612 * 2
def baseEnd_1997612 : Nat := 227941137153187459458479

theorem tailTrace_1997612 : CollatzResearch.WordTrace tailWord_1997612 prefixEnd_1997612 227941137153187459458479 := by
  unfold tailWord_1997612
  simp only [CollatzResearch.WordTrace]
  refine ⟨36429447619500181906589545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48572596826000242542119393 36429447619500181906589545)
  ·
    refine ⟨27322085714625136429942159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36429447619500181906589545 27322085714625136429942159)
    ·
      refine ⟨40983128571937704644913239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27322085714625136429942159 40983128571937704644913239)
      ·
        refine ⟨61474692857906556967369859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40983128571937704644913239 61474692857906556967369859)
        ·
          refine ⟨92212039286859835451054789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61474692857906556967369859 92212039286859835451054789)
          ·
            refine ⟨17289757366286219147072773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92212039286859835451054789 17289757366286219147072773)
            ·
              refine ⟨3241829506178666090076145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17289757366286219147072773 3241829506178666090076145)
              ·
                refine ⟨2431372129633999567557109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3241829506178666090076145 2431372129633999567557109)
                ·
                  refine ⟨227941137153187459458479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2431372129633999567557109 227941137153187459458479)
                  ·
                    rfl

theorem cell22_1997612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_1997612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997612 prefixEnd_1997612 := by exact prefixLift 1997612
  have htrace : WordTrace (prefixWord ++ tailWord_1997612) baseStart_1997612 baseEnd_1997612 := by
    simpa [prefixWord, tailWord_1997612, baseEnd_1997612] using wordTrace_append hprefix tailTrace_1997612
  have hstable : (prefixWord ++ tailWord_1997612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997612).length < 2 ^ (prefixWord ++ tailWord_1997612).sum := by decide
  have hdescent : baseEnd_1997612 < baseStart_1997612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997689 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 1, 5]
def baseStart_1997689 : Nat := 118140960795 + 1997689 * 2 ^ 59
def prefixEnd_1997689 : Nat := 4983230072969 + 3 ^ 40 * 1997689 * 2
def baseEnd_1997689 : Nat := 683849770133159844200201

theorem tailTrace_1997689 : CollatzResearch.WordTrace tailWord_1997689 prefixEnd_1997689 683849770133159844200201 := by
  unfold tailWord_1997689
  simp only [CollatzResearch.WordTrace]
  refine ⟨72861703659721405963732121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48574469106480937309154747 72861703659721405963732121)
  ·
    refine ⟨54646277744791054472799091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72861703659721405963732121 54646277744791054472799091)
    ·
      refine ⟨81969416617186581709198637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54646277744791054472799091 81969416617186581709198637)
      ·
        refine ⟨30738531231444968140949489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81969416617186581709198637 30738531231444968140949489)
        ·
          refine ⟨23053898423583726105712117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30738531231444968140949489 23053898423583726105712117)
          ·
            refine ⟨2161302977210974322410511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23053898423583726105712117 2161302977210974322410511)
            ·
              refine ⟨3241954465816461483615767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161302977210974322410511 3241954465816461483615767)
              ·
                refine ⟨4862931698724692225423651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241954465816461483615767 4862931698724692225423651)
                ·
                  refine ⟨7294397548087038338135477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862931698724692225423651 7294397548087038338135477)
                  ·
                    refine ⟨683849770133159844200201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7294397548087038338135477 683849770133159844200201)
                    ·
                      rfl

theorem cell22_1997689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_1997689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997689 prefixEnd_1997689 := by exact prefixLift 1997689
  have htrace : WordTrace (prefixWord ++ tailWord_1997689) baseStart_1997689 baseEnd_1997689 := by
    simpa [prefixWord, tailWord_1997689, baseEnd_1997689] using wordTrace_append hprefix tailTrace_1997689
  have hstable : (prefixWord ++ tailWord_1997689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997689).length < 2 ^ (prefixWord ++ tailWord_1997689).sum := by decide
  have hdescent : baseEnd_1997689 < baseStart_1997689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997732 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1997732 : Nat := 118140960795 + 1997732 * 2 ^ 59
def prefixEnd_1997732 : Nat := 4983230072969 + 3 ^ 40 * 1997732 * 2
def baseEnd_1997732 : Nat := 683864489911922065375069

theorem tailTrace_1997732 : CollatzResearch.WordTrace tailWord_1997732 prefixEnd_1997732 683864489911922065375069 := by
  unfold tailWord_1997732
  simp only [CollatzResearch.WordTrace]
  refine ⟨36431635999282812153773725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48575514665710416205031633 36431635999282812153773725)
  ·
    refine ⟨13661863499731054557665147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36431635999282812153773725 13661863499731054557665147)
    ·
      refine ⟨20492795249596581836497721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13661863499731054557665147 20492795249596581836497721)
      ·
        refine ⟨15369596437197436377373291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20492795249596581836497721 15369596437197436377373291)
        ·
          refine ⟨23054394655796154566059937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15369596437197436377373291 23054394655796154566059937)
          ·
            refine ⟨17290795991847115924544953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23054394655796154566059937 17290795991847115924544953)
            ·
              refine ⟨12968096993885336943408715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17290795991847115924544953 12968096993885336943408715)
              ·
                refine ⟨19452145490828005415113073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12968096993885336943408715 19452145490828005415113073)
                ·
                  refine ⟨14589109118121004061334805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19452145490828005415113073 14589109118121004061334805)
                  ·
                    refine ⟨683864489911922065375069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14589109118121004061334805 683864489911922065375069)
                    ·
                      rfl

theorem cell22_1997732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1997732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997732 prefixEnd_1997732 := by exact prefixLift 1997732
  have htrace : WordTrace (prefixWord ++ tailWord_1997732) baseStart_1997732 baseEnd_1997732 := by
    simpa [prefixWord, tailWord_1997732, baseEnd_1997732] using wordTrace_append hprefix tailTrace_1997732
  have hstable : (prefixWord ++ tailWord_1997732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997732).length < 2 ^ (prefixWord ++ tailWord_1997732).sum := by decide
  have hdescent : baseEnd_1997732 < baseStart_1997732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997781 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 5]
def baseStart_1997781 : Nat := 118140960795 + 1997781 * 2 ^ 59
def prefixEnd_1997781 : Nat := 4983230072969 + 3 ^ 40 * 1997781 * 2
def baseEnd_1997781 : Nat := 227960421204434090299973

theorem tailTrace_1997781 : CollatzResearch.WordTrace tailWord_1997781 prefixEnd_1997781 227960421204434090299973 := by
  unfold tailWord_1997781
  simp only [CollatzResearch.WordTrace]
  refine ⟨72865059175388105676081197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48576706116925403784054131 72865059175388105676081197)
  ·
    refine ⟨27324397190770539628530449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72865059175388105676081197 27324397190770539628530449)
    ·
      refine ⟨20493297893077904721397837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27324397190770539628530449 20493297893077904721397837)
      ·
        refine ⟨7684986709904214270524189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20493297893077904721397837 7684986709904214270524189)
        ·
          refine ⟨2881870016214080351446571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7684986709904214270524189 2881870016214080351446571)
          ·
            refine ⟨4322805024321120527169857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881870016214080351446571 4322805024321120527169857)
            ·
              refine ⟨3242103768240840395377393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322805024321120527169857 3242103768240840395377393)
              ·
                refine ⟨2431577826180630296533045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3242103768240840395377393 2431577826180630296533045)
                ·
                  refine ⟨227960421204434090299973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2431577826180630296533045 227960421204434090299973)
                  ·
                    rfl

theorem cell22_1997781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_1997781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997781 prefixEnd_1997781 := by exact prefixLift 1997781
  have htrace : WordTrace (prefixWord ++ tailWord_1997781) baseStart_1997781 baseEnd_1997781 := by
    simpa [prefixWord, tailWord_1997781, baseEnd_1997781] using wordTrace_append hprefix tailTrace_1997781
  have hstable : (prefixWord ++ tailWord_1997781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997781).length < 2 ^ (prefixWord ++ tailWord_1997781).sum := by decide
  have hdescent : baseEnd_1997781 < baseStart_1997781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997785 : List Nat := [1, 2, 1, 2, 5, 3, 2, 2, 1, 3]
def baseStart_1997785 : Nat := 118140960795 + 1997785 * 2 ^ 59
def prefixEnd_1997785 : Nat := 4983230072969 + 3 ^ 40 * 1997785 * 2
def baseEnd_1997785 : Nat := 683882632895047593799907

theorem tailTrace_1997785 : CollatzResearch.WordTrace tailWord_1997785 prefixEnd_1997785 683882632895047593799907 := by
  unfold tailWord_1997785
  simp only [CollatzResearch.WordTrace]
  refine ⟨72865205067373614359226809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48576803378249076239484539 72865205067373614359226809)
  ·
    refine ⟨54648903800530210769420107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72865205067373614359226809 54648903800530210769420107)
    ·
      refine ⟨81973355700795316154130161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54648903800530210769420107 81973355700795316154130161)
      ·
        refine ⟨61480016775596487115597621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81973355700795316154130161 61480016775596487115597621)
        ·
          refine ⟨5763751572712170667087277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61480016775596487115597621 5763751572712170667087277)
          ·
            refine ⟨2161406839767064000157729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5763751572712170667087277 2161406839767064000157729)
            ·
              refine ⟨1621055129825298000118297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161406839767064000157729 1621055129825298000118297)
              ·
                refine ⟨1215791347368973500088723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621055129825298000118297 1215791347368973500088723)
                ·
                  refine ⟨1823687021053460250133085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215791347368973500088723 1823687021053460250133085)
                  ·
                    refine ⟨683882632895047593799907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1823687021053460250133085 683882632895047593799907)
                    ·
                      rfl

theorem cell22_1997785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 3].length) (baseStart_1997785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997785 prefixEnd_1997785 := by exact prefixLift 1997785
  have htrace : WordTrace (prefixWord ++ tailWord_1997785) baseStart_1997785 baseEnd_1997785 := by
    simpa [prefixWord, tailWord_1997785, baseEnd_1997785] using wordTrace_append hprefix tailTrace_1997785
  have hstable : (prefixWord ++ tailWord_1997785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997785).length < 2 ^ (prefixWord ++ tailWord_1997785).sum := by decide
  have hdescent : baseEnd_1997785 < baseStart_1997785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997809 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 6]
def baseStart_1997809 : Nat := 118140960795 + 1997809 * 2 ^ 59
def prefixEnd_1997809 : Nat := 4983230072969 + 3 ^ 40 * 1997809 * 2
def baseEnd_1997809 : Nat := 227963616195173177066611

theorem tailTrace_1997809 : CollatzResearch.WordTrace tailWord_1997809 prefixEnd_1997809 227963616195173177066611 := by
  unfold tailWord_1997809
  simp only [CollatzResearch.WordTrace]
  refine ⟨72866080419286666458100481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48577386946191110972066987 72866080419286666458100481)
  ·
    refine ⟨54649560314464999843575361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72866080419286666458100481 54649560314464999843575361)
    ·
      refine ⟨40987170235848749882681521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54649560314464999843575361 40987170235848749882681521)
      ·
        refine ⟨30740377676886562412011141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40987170235848749882681521 30740377676886562412011141)
        ·
          refine ⟨5763820814416230452252089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30740377676886562412011141 5763820814416230452252089)
          ·
            refine ⟨4322865610812172839189067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5763820814416230452252089 4322865610812172839189067)
            ·
              refine ⟨6484298416218259258783601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322865610812172839189067 6484298416218259258783601)
              ·
                refine ⟨4863223812163694444087701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6484298416218259258783601 4863223812163694444087701)
                ·
                  refine ⟨227963616195173177066611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4863223812163694444087701 227963616195173177066611)
                  ·
                    rfl

theorem cell22_1997809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_1997809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997809 prefixEnd_1997809 := by exact prefixLift 1997809
  have htrace : WordTrace (prefixWord ++ tailWord_1997809) baseStart_1997809 baseEnd_1997809 := by
    simpa [prefixWord, tailWord_1997809, baseEnd_1997809] using wordTrace_append hprefix tailTrace_1997809
  have hstable : (prefixWord ++ tailWord_1997809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997809).length < 2 ^ (prefixWord ++ tailWord_1997809).sum := by decide
  have hdescent : baseEnd_1997809 < baseStart_1997809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997916 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 5]
def baseStart_1997916 : Nat := 118140960795 + 1997916 * 2 ^ 59
def prefixEnd_1997916 : Nat := 4983230072969 + 3 ^ 40 * 1997916 * 2
def baseEnd_1997916 : Nat := 227975825624068972924835

theorem tailTrace_1997916 : CollatzResearch.WordTrace tailWord_1997916 prefixEnd_1997916 227975825624068972924835 := by
  unfold tailWord_1997916
  simp only [CollatzResearch.WordTrace]
  refine ⟨36434991514949511866122801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48579988686599349154830401 36434991514949511866122801)
  ·
    refine ⟨27326243636212133899592101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36434991514949511866122801 27326243636212133899592101)
    ·
      refine ⟨5123670681789775106173519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27326243636212133899592101 5123670681789775106173519)
      ·
        refine ⟨7685506022684662659260279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123670681789775106173519 7685506022684662659260279)
        ·
          refine ⟨11528259034026993988890419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7685506022684662659260279 11528259034026993988890419)
          ·
            refine ⟨17292388551040490983335629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11528259034026993988890419 17292388551040490983335629)
            ·
              refine ⟨6484645706640184118750861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17292388551040490983335629 6484645706640184118750861)
              ·
                refine ⟨2431742139990069044531573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6484645706640184118750861 2431742139990069044531573)
                ·
                  refine ⟨227975825624068972924835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2431742139990069044531573 227975825624068972924835)
                  ·
                    rfl

theorem cell22_1997916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_1997916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997916 prefixEnd_1997916 := by exact prefixLift 1997916
  have htrace : WordTrace (prefixWord ++ tailWord_1997916) baseStart_1997916 baseEnd_1997916 := by
    simpa [prefixWord, tailWord_1997916, baseEnd_1997916] using wordTrace_append hprefix tailTrace_1997916
  have hstable : (prefixWord ++ tailWord_1997916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997916).length < 2 ^ (prefixWord ++ tailWord_1997916).sum := by decide
  have hdescent : baseEnd_1997916 < baseStart_1997916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997959 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1997959 : Nat := 118140960795 + 1997959 * 2 ^ 59
def prefixEnd_1997959 : Nat := 4983230072969 + 3 ^ 40 * 1997959 * 2
def baseEnd_1997959 : Nat := 683942196650969139949373

theorem tailTrace_1997959 : CollatzResearch.WordTrace tailWord_1997959 prefixEnd_1997959 683942196650969139949373 := by
  unfold tailWord_1997959
  simp only [CollatzResearch.WordTrace]
  refine ⟨72871551368743242076060931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48581034245828828050707287 72871551368743242076060931)
  ·
    refine ⟨109307327053114863114091397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72871551368743242076060931 109307327053114863114091397)
    ·
      refine ⟨20495123822459036833892137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109307327053114863114091397 20495123822459036833892137)
      ·
        refine ⟨15371342866844277625419103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20495123822459036833892137 15371342866844277625419103)
        ·
          refine ⟨23057014300266416438128655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15371342866844277625419103 23057014300266416438128655)
          ·
            refine ⟨34585521450399624657192983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23057014300266416438128655 34585521450399624657192983)
            ·
              refine ⟨51878282175599436985789475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34585521450399624657192983 51878282175599436985789475)
              ·
                refine ⟨77817423263399155478684213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51878282175599436985789475 77817423263399155478684213)
                ·
                  refine ⟨7295383430943670826126645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77817423263399155478684213 7295383430943670826126645)
                  ·
                    refine ⟨683942196650969139949373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7295383430943670826126645 683942196650969139949373)
                    ·
                      rfl

theorem cell22_1997959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1997959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997959 prefixEnd_1997959 := by exact prefixLift 1997959
  have htrace : WordTrace (prefixWord ++ tailWord_1997959) baseStart_1997959 baseEnd_1997959 := by
    simpa [prefixWord, tailWord_1997959, baseEnd_1997959] using wordTrace_append hprefix tailTrace_1997959
  have hstable : (prefixWord ++ tailWord_1997959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997959).length < 2 ^ (prefixWord ++ tailWord_1997959).sum := by decide
  have hdescent : baseEnd_1997959 < baseStart_1997959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997976 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_1997976 : Nat := 118140960795 + 1997976 * 2 ^ 59
def prefixEnd_1997976 : Nat := 4983230072969 + 3 ^ 40 * 1997976 * 2
def baseEnd_1997976 : Nat := 683948016098386762274321

theorem tailTrace_1997976 : CollatzResearch.WordTrace tailWord_1997976 prefixEnd_1997976 683948016098386762274321 := by
  unfold tailWord_1997976
  simp only [CollatzResearch.WordTrace]
  refine ⟨36436085704840826989714891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48581447606454435986286521 36436085704840826989714891)
  ·
    refine ⟨54654128557261240484572337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36436085704840826989714891 54654128557261240484572337)
    ·
      refine ⟨40990596417945930363429253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54654128557261240484572337 40990596417945930363429253)
      ·
        refine ⟨7685736828364861943142985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40990596417945930363429253 7685736828364861943142985)
        ·
          refine ⟨5764302621273646457357239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7685736828364861943142985 5764302621273646457357239)
          ·
            refine ⟨8646453931910469686035859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764302621273646457357239 8646453931910469686035859)
            ·
              refine ⟨12969680897865704529053789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8646453931910469686035859 12969680897865704529053789)
              ·
                refine ⟨4863630336699639198395171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12969680897865704529053789 4863630336699639198395171)
                ·
                  refine ⟨7295445505049458797592757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863630336699639198395171 7295445505049458797592757)
                  ·
                    refine ⟨683948016098386762274321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7295445505049458797592757 683948016098386762274321)
                    ·
                      rfl

theorem cell22_1997976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_1997976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997976 prefixEnd_1997976 := by exact prefixLift 1997976
  have htrace : WordTrace (prefixWord ++ tailWord_1997976) baseStart_1997976 baseEnd_1997976 := by
    simpa [prefixWord, tailWord_1997976, baseEnd_1997976] using wordTrace_append hprefix tailTrace_1997976
  have hstable : (prefixWord ++ tailWord_1997976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997976).length < 2 ^ (prefixWord ++ tailWord_1997976).sum := by decide
  have hdescent : baseEnd_1997976 < baseStart_1997976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997997 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1997997 : Nat := 118140960795 + 1997997 * 2 ^ 59
def prefixEnd_1997997 : Nat := 4983230072969 + 3 ^ 40 * 1997997 * 2
def baseEnd_1997997 : Nat := 683955204827549707499257

theorem tailTrace_1997997 : CollatzResearch.WordTrace tailWord_1997997 prefixEnd_1997997 683955204827549707499257 := by
  unfold tailWord_1997997
  simp only [CollatzResearch.WordTrace]
  refine ⟨72872937342605574565944245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48581958228403716377296163 72872937342605574565944245)
  ·
    refine ⟨6831837875869272615557273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72872937342605574565944245 6831837875869272615557273)
    ·
      refine ⟨5123878406901954461667955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6831837875869272615557273 5123878406901954461667955)
      ·
        refine ⟨7685817610352931692501933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123878406901954461667955 7685817610352931692501933)
        ·
          refine ⟨2882181603882349384688225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7685817610352931692501933 2882181603882349384688225)
          ·
            refine ⟨2161636202911762038516169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2882181603882349384688225 2161636202911762038516169)
            ·
              refine ⟨1621227152183821528887127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161636202911762038516169 1621227152183821528887127)
              ·
                refine ⟨2431840728275732293330691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621227152183821528887127 2431840728275732293330691)
                ·
                  refine ⟨3647761092413598439996037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431840728275732293330691 3647761092413598439996037)
                  ·
                    refine ⟨683955204827549707499257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3647761092413598439996037 683955204827549707499257)
                    ·
                      rfl

theorem cell22_1997997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1997997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997997 prefixEnd_1997997 := by exact prefixLift 1997997
  have htrace : WordTrace (prefixWord ++ tailWord_1997997) baseStart_1997997 baseEnd_1997997 := by
    simpa [prefixWord, tailWord_1997997, baseEnd_1997997] using wordTrace_append hprefix tailTrace_1997997
  have hstable : (prefixWord ++ tailWord_1997997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997997).length < 2 ^ (prefixWord ++ tailWord_1997997).sum := by decide
  have hdescent : baseEnd_1997997 < baseStart_1997997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998019 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 2, 6]
def baseStart_1998019 : Nat := 118140960795 + 1998019 * 2 ^ 59
def prefixEnd_1998019 : Nat := 4983230072969 + 3 ^ 40 * 1998019 * 2
def baseEnd_1998019 : Nat := 683962735877148983449189

theorem tailTrace_1998019 : CollatzResearch.WordTrace tailWord_1998019 prefixEnd_1998019 683962735877148983449189 := by
  unfold tailWord_1998019
  simp only [CollatzResearch.WordTrace]
  refine ⟨72873739748525872323245111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48582493165683914882163407 72873739748525872323245111)
  ·
    refine ⟨109310609622788808484867667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72873739748525872323245111 109310609622788808484867667)
    ·
      refine ⟨163965914434183212727301501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109310609622788808484867667 163965914434183212727301501)
      ·
        refine ⟨61487217912818704772738063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163965914434183212727301501 61487217912818704772738063)
        ·
          refine ⟨92230826869228057159107095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61487217912818704772738063 92230826869228057159107095)
          ·
            refine ⟨138346240303842085738660643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92230826869228057159107095 138346240303842085738660643)
            ·
              refine ⟨207519360455763128607990965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138346240303842085738660643 207519360455763128607990965)
              ·
                refine ⟨19454940042727793306999153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207519360455763128607990965 19454940042727793306999153)
                ·
                  refine ⟨14591205032045844980249365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19454940042727793306999153 14591205032045844980249365)
                  ·
                    refine ⟨683962735877148983449189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14591205032045844980249365 683962735877148983449189)
                    ·
                      rfl

theorem cell22_1998019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_1998019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998019 prefixEnd_1998019 := by exact prefixLift 1998019
  have htrace : WordTrace (prefixWord ++ tailWord_1998019) baseStart_1998019 baseEnd_1998019 := by
    simpa [prefixWord, tailWord_1998019, baseEnd_1998019] using wordTrace_append hprefix tailTrace_1998019
  have hstable : (prefixWord ++ tailWord_1998019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998019).length < 2 ^ (prefixWord ++ tailWord_1998019).sum := by decide
  have hdescent : baseEnd_1998019 < baseStart_1998019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998040 : List Nat := [2, 1, 2, 2, 6, 1, 2, 6]
def baseStart_1998040 : Nat := 118140960795 + 1998040 * 2 ^ 59
def prefixEnd_1998040 : Nat := 4983230072969 + 3 ^ 40 * 1998040 * 2
def baseEnd_1998040 : Nat := 75996658289590214297125

theorem tailTrace_1998040 : CollatzResearch.WordTrace tailWord_1998040 prefixEnd_1998040 75996658289590214297125 := by
  unfold tailWord_1998040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36437252840724896454879787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48583003787633195273173049 36437252840724896454879787)
  ·
    refine ⟨54655879261087344682319681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36437252840724896454879787 54655879261087344682319681)
    ·
      refine ⟨40991909445815508511739761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54655879261087344682319681 40991909445815508511739761)
      ·
        refine ⟨30743932084361631383804821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40991909445815508511739761 30743932084361631383804821)
        ·
          refine ⟨1441121816454451471115851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30743932084361631383804821 1441121816454451471115851)
          ·
            refine ⟨2161682724681677206673777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441121816454451471115851 2161682724681677206673777)
            ·
              refine ⟨1621262043511257905005333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161682724681677206673777 1621262043511257905005333)
              ·
                refine ⟨75996658289590214297125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1621262043511257905005333 75996658289590214297125)
                ·
                  rfl

theorem cell22_1998040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 6].length) (baseStart_1998040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998040 prefixEnd_1998040 := by exact prefixLift 1998040
  have htrace : WordTrace (prefixWord ++ tailWord_1998040) baseStart_1998040 baseEnd_1998040 := by
    simpa [prefixWord, tailWord_1998040, baseEnd_1998040] using wordTrace_append hprefix tailTrace_1998040
  have hstable : (prefixWord ++ tailWord_1998040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998040).length < 2 ^ (prefixWord ++ tailWord_1998040).sum := by decide
  have hdescent : baseEnd_1998040 < baseStart_1998040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998113 : List Nat := [1, 2, 3, 2, 1, 1, 1, 7, 4]
def baseStart_1998113 : Nat := 118140960795 + 1998113 * 2 ^ 59
def prefixEnd_1998113 : Nat := 4983230072969 + 3 ^ 40 * 1998113 * 2
def baseEnd_1998113 : Nat := 227998304666054690532967

theorem tailTrace_1998113 : CollatzResearch.WordTrace tailWord_1998113 prefixEnd_1998113 227998304666054690532967 := by
  unfold tailWord_1998113
  simp only [CollatzResearch.WordTrace]
  refine ⟨72877168210185326377166993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48584778806790217584777995 72877168210185326377166993)
  ·
    refine ⟨54657876157638994782875245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72877168210185326377166993 54657876157638994782875245)
    ·
      refine ⟨20496703559114623043578217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54657876157638994782875245 20496703559114623043578217)
      ·
        refine ⟨15372527669335967282683663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20496703559114623043578217 15372527669335967282683663)
        ·
          refine ⟨23058791504003950924025495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15372527669335967282683663 23058791504003950924025495)
          ·
            refine ⟨34588187256005926386038243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23058791504003950924025495 34588187256005926386038243)
            ·
              refine ⟨51882280884008889579057365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34588187256005926386038243 51882280884008889579057365)
              ·
                refine ⟨1215990958218958349509157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51882280884008889579057365 1215990958218958349509157)
                ·
                  refine ⟨227998304666054690532967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215990958218958349509157 227998304666054690532967)
                  ·
                    rfl

theorem cell22_1998113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 4].length) (baseStart_1998113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998113 prefixEnd_1998113 := by exact prefixLift 1998113
  have htrace : WordTrace (prefixWord ++ tailWord_1998113) baseStart_1998113 baseEnd_1998113 := by
    simpa [prefixWord, tailWord_1998113, baseEnd_1998113] using wordTrace_append hprefix tailTrace_1998113
  have hstable : (prefixWord ++ tailWord_1998113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998113).length < 2 ^ (prefixWord ++ tailWord_1998113).sum := by decide
  have hdescent : baseEnd_1998113 < baseStart_1998113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998115 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 1, 4]
def baseStart_1998115 : Nat := 118140960795 + 1998115 * 2 ^ 59
def prefixEnd_1998115 : Nat := 4983230072969 + 3 ^ 40 * 1998115 * 2
def baseEnd_1998115 : Nat := 683995598639036733048895

theorem tailTrace_1998115 : CollatzResearch.WordTrace tailWord_1998115 prefixEnd_1998115 683995598639036733048895 := by
  unfold tailWord_1998115
  simp only [CollatzResearch.WordTrace]
  refine ⟨72877241156178080718739799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48584827437452053812493199 72877241156178080718739799)
  ·
    refine ⟨109315861734267121078109699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72877241156178080718739799 109315861734267121078109699)
    ·
      refine ⟨163973792601400681617164549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109315861734267121078109699 163973792601400681617164549)
      ·
        refine ⟨30745086112762627803218353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163973792601400681617164549 30745086112762627803218353)
        ·
          refine ⟨23058814584571970852413765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30745086112762627803218353 23058814584571970852413765)
          ·
            refine ⟨4323527734607244534827581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23058814584571970852413765 4323527734607244534827581)
            ·
              refine ⟨1621322900477716700560343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4323527734607244534827581 1621322900477716700560343)
              ·
                refine ⟨2431984350716575050840515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621322900477716700560343 2431984350716575050840515)
                ·
                  refine ⟨3647976526074862576260773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431984350716575050840515 3647976526074862576260773)
                  ·
                    refine ⟨683995598639036733048895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3647976526074862576260773 683995598639036733048895)
                    ·
                      rfl

theorem cell22_1998115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 4].length) (baseStart_1998115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998115 prefixEnd_1998115 := by exact prefixLift 1998115
  have htrace : WordTrace (prefixWord ++ tailWord_1998115) baseStart_1998115 baseEnd_1998115 := by
    simpa [prefixWord, tailWord_1998115, baseEnd_1998115] using wordTrace_append hprefix tailTrace_1998115
  have hstable : (prefixWord ++ tailWord_1998115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998115).length < 2 ^ (prefixWord ++ tailWord_1998115).sum := by decide
  have hdescent : baseEnd_1998115 < baseStart_1998115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998130 : List Nat := [3, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1998130 : Nat := 118140960795 + 1998130 * 2 ^ 59
def prefixEnd_1998130 : Nat := 4983230072969 + 3 ^ 40 * 1998130 * 2
def baseEnd_1998130 : Nat := 228000244481860564641283

theorem tailTrace_1998130 : CollatzResearch.WordTrace tailWord_1998130 prefixEnd_1998130 228000244481860564641283 := by
  unfold tailWord_1998130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18219447062780934570133961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48585192167415825520357229 18219447062780934570133961)
  ·
    refine ⟨13664585297085700927600471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18219447062780934570133961 13664585297085700927600471)
    ·
      refine ⟨20496877945628551391400707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13664585297085700927600471 20496877945628551391400707)
      ·
        refine ⟨30745316918442827087101061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20496877945628551391400707 30745316918442827087101061)
        ·
          refine ⟨5764746922208030078831449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30745316918442827087101061 5764746922208030078831449)
          ·
            refine ⟨4323560191656022559123587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5764746922208030078831449 4323560191656022559123587)
            ·
              refine ⟨6485340287484033838685381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323560191656022559123587 6485340287484033838685381)
              ·
                refine ⟨1216001303903256344753509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6485340287484033838685381 1216001303903256344753509)
                ·
                  refine ⟨228000244481860564641283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216001303903256344753509 228000244481860564641283)
                  ·
                    rfl

theorem cell22_1998130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1998130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998130 prefixEnd_1998130 := by exact prefixLift 1998130
  have htrace : WordTrace (prefixWord ++ tailWord_1998130) baseStart_1998130 baseEnd_1998130 := by
    simpa [prefixWord, tailWord_1998130, baseEnd_1998130] using wordTrace_append hprefix tailTrace_1998130
  have hstable : (prefixWord ++ tailWord_1998130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998130).length < 2 ^ (prefixWord ++ tailWord_1998130).sum := by decide
  have hdescent : baseEnd_1998130 < baseStart_1998130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998145 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1998145 : Nat := 118140960795 + 1998145 * 2 ^ 59
def prefixEnd_1998145 : Nat := 4983230072969 + 3 ^ 40 * 1998145 * 2
def baseEnd_1998145 : Nat := 684005868252126654798803

theorem tailTrace_1998145 : CollatzResearch.WordTrace tailWord_1998145 prefixEnd_1998145 684005868252126654798803 := by
  unfold tailWord_1998145
  simp only [CollatzResearch.WordTrace]
  refine ⟨72878335346069395842331889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48585556897379597228221259 72878335346069395842331889)
  ·
    refine ⟨54658751509552046881748917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72878335346069395842331889 54658751509552046881748917)
    ·
      refine ⟨5124257954020504395163961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54658751509552046881748917 5124257954020504395163961)
      ·
        refine ⟨3843193465515378296372971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5124257954020504395163961 3843193465515378296372971)
        ·
          refine ⟨5764790198273067444559457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843193465515378296372971 5764790198273067444559457)
          ·
            refine ⟨4323592648704800583419593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5764790198273067444559457 4323592648704800583419593)
            ·
              refine ⟨3242694486528600437564695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4323592648704800583419593 3242694486528600437564695)
              ·
                refine ⟨4864041729792900656347043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242694486528600437564695 4864041729792900656347043)
                ·
                  refine ⟨7296062594689350984520565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864041729792900656347043 7296062594689350984520565)
                  ·
                    refine ⟨684005868252126654798803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7296062594689350984520565 684005868252126654798803)
                    ·
                      rfl

theorem cell22_1998145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1998145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998145 prefixEnd_1998145 := by exact prefixLift 1998145
  have htrace : WordTrace (prefixWord ++ tailWord_1998145) baseStart_1998145 baseEnd_1998145 := by
    simpa [prefixWord, tailWord_1998145, baseEnd_1998145] using wordTrace_append hprefix tailTrace_1998145
  have hstable : (prefixWord ++ tailWord_1998145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998145).length < 2 ^ (prefixWord ++ tailWord_1998145).sum := by decide
  have hdescent : baseEnd_1998145 < baseStart_1998145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998158 : List Nat := [4, 1, 1, 1, 1, 1, 7, 6]
def baseStart_1998158 : Nat := 118140960795 + 1998158 * 2 ^ 59
def prefixEnd_1998158 : Nat := 4983230072969 + 3 ^ 40 * 1998158 * 2
def baseEnd_1998158 : Nat := 76001146490866550469307

theorem tailTrace_1998158 : CollatzResearch.WordTrace tailWord_1998158 prefixEnd_1998158 76001146490866550469307 := by
  unfold tailWord_1998158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9109851186877787382819391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48585872996681532708370085 9109851186877787382819391)
  ·
    refine ⟨13664776780316681074229087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9109851186877787382819391 13664776780316681074229087)
    ·
      refine ⟨20497165170475021611343631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13664776780316681074229087 20497165170475021611343631)
      ·
        refine ⟨30745747755712532417015447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20497165170475021611343631 30745747755712532417015447)
        ·
          refine ⟨46118621633568798625523171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30745747755712532417015447 46118621633568798625523171)
          ·
            refine ⟨69177932450353197938284757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46118621633568798625523171 69177932450353197938284757)
            ·
              refine ⟨1621357791805153076678549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69177932450353197938284757 1621357791805153076678549)
              ·
                refine ⟨76001146490866550469307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1621357791805153076678549 76001146490866550469307)
                ·
                  rfl

theorem cell22_1998158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_1998158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998158 prefixEnd_1998158 := by exact prefixLift 1998158
  have htrace : WordTrace (prefixWord ++ tailWord_1998158) baseStart_1998158 baseEnd_1998158 := by
    simpa [prefixWord, tailWord_1998158, baseEnd_1998158] using wordTrace_append hprefix tailTrace_1998158
  have hstable : (prefixWord ++ tailWord_1998158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998158).length < 2 ^ (prefixWord ++ tailWord_1998158).sum := by decide
  have hdescent : baseEnd_1998158 < baseStart_1998158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998166 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1998166 : Nat := 118140960795 + 1998166 * 2 ^ 59
def prefixEnd_1998166 : Nat := 4983230072969 + 3 ^ 40 * 1998166 * 2
def baseEnd_1998166 : Nat := 684013056981289600023739

theorem tailTrace_1998166 : CollatzResearch.WordTrace tailWord_1998166 prefixEnd_1998166 684013056981289600023739 := by
  unfold tailWord_1998166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554943829937082276802897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48586067519328877619230901 4554943829937082276802897)
  ·
    refine ⟨3416207872452811707602173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4554943829937082276802897 3416207872452811707602173)
    ·
      refine ⟨1281077952169804390350815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3416207872452811707602173 1281077952169804390350815)
      ·
        refine ⟨1921616928254706585526223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281077952169804390350815 1921616928254706585526223)
        ·
          refine ⟨2882425392382059878289335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921616928254706585526223 2882425392382059878289335)
          ·
            refine ⟨4323638088573089817434003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882425392382059878289335 4323638088573089817434003)
            ·
              refine ⟨6485457132859634726151005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323638088573089817434003 6485457132859634726151005)
              ·
                refine ⟨2432046424822363022306627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6485457132859634726151005 2432046424822363022306627)
                ·
                  refine ⟨3648069637233544533459941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432046424822363022306627 3648069637233544533459941)
                  ·
                    refine ⟨684013056981289600023739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3648069637233544533459941 684013056981289600023739)
                    ·
                      rfl

theorem cell22_1998166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1998166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998166 prefixEnd_1998166 := by exact prefixLift 1998166
  have htrace : WordTrace (prefixWord ++ tailWord_1998166) baseStart_1998166 baseEnd_1998166 := by
    simpa [prefixWord, tailWord_1998166, baseEnd_1998166] using wordTrace_append hprefix tailTrace_1998166
  have hstable : (prefixWord ++ tailWord_1998166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998166).length < 2 ^ (prefixWord ++ tailWord_1998166).sum := by decide
  have hdescent : baseEnd_1998166 < baseStart_1998166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998263 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 1, 5]
def baseStart_1998263 : Nat := 118140960795 + 1998263 * 2 ^ 59
def prefixEnd_1998263 : Nat := 4983230072969 + 3 ^ 40 * 1998263 * 2
def baseEnd_1998263 : Nat := 684046262063613680348441

theorem tailTrace_1998263 : CollatzResearch.WordTrace tailWord_1998263 prefixEnd_1998263 684046262063613680348441 := by
  unfold tailWord_1998263
  simp only [CollatzResearch.WordTrace]
  refine ⟨72882639159641901995127443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48588426106427934663418295 72882639159641901995127443)
  ·
    refine ⟨109323958739462852992691165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72882639159641901995127443 109323958739462852992691165)
    ·
      refine ⟨40996484527298569872259187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109323958739462852992691165 40996484527298569872259187)
      ·
        refine ⟨61494726790947854808388781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40996484527298569872259187 61494726790947854808388781)
        ·
          refine ⟨23060522546605445553145793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61494726790947854808388781 23060522546605445553145793)
          ·
            refine ⟨17295391909954084164859345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23060522546605445553145793 17295391909954084164859345)
            ·
              refine ⟨12971543932465563123644509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17295391909954084164859345 12971543932465563123644509)
              ·
                refine ⟨4864328974674586171366691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12971543932465563123644509 4864328974674586171366691)
                ·
                  refine ⟨7296493462011879257050037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864328974674586171366691 7296493462011879257050037)
                  ·
                    refine ⟨684046262063613680348441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7296493462011879257050037 684046262063613680348441)
                    ·
                      rfl

theorem cell22_1998263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_1998263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998263 prefixEnd_1998263 := by exact prefixLift 1998263
  have htrace : WordTrace (prefixWord ++ tailWord_1998263) baseStart_1998263 baseEnd_1998263 := by
    simpa [prefixWord, tailWord_1998263, baseEnd_1998263] using wordTrace_append hprefix tailTrace_1998263
  have hstable : (prefixWord ++ tailWord_1998263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998263).length < 2 ^ (prefixWord ++ tailWord_1998263).sum := by decide
  have hdescent : baseEnd_1998263 < baseStart_1998263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998297 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 2, 3]
def baseStart_1998297 : Nat := 118140960795 + 1998297 * 2 ^ 59
def prefixEnd_1998297 : Nat := 4983230072969 + 3 ^ 40 * 1998297 * 2
def baseEnd_1998297 : Nat := 684057900958448924998337

theorem tailTrace_1998297 : CollatzResearch.WordTrace tailWord_1998297 prefixEnd_1998297 684057900958448924998337 := by
  unfold tailWord_1998297
  simp only [CollatzResearch.WordTrace]
  refine ⟨72883879241518725801865145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48589252827679150534576763 72883879241518725801865145)
  ·
    refine ⟨54662909431139044351398859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72883879241518725801865145 54662909431139044351398859)
    ·
      refine ⟨81994364146708566527098289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54662909431139044351398859 81994364146708566527098289)
      ·
        refine ⟨61495773110031424895323717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81994364146708566527098289 61495773110031424895323717)
        ·
          refine ⟨11530457458130892167873197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61495773110031424895323717 11530457458130892167873197)
          ·
            refine ⟨4323921546799084562952449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11530457458130892167873197 4323921546799084562952449)
            ·
              refine ⟨3242941160099313422214337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4323921546799084562952449 3242941160099313422214337)
              ·
                refine ⟨2432205870074485066660753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3242941160099313422214337 2432205870074485066660753)
                ·
                  refine ⟨1824154402555863799995565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2432205870074485066660753 1824154402555863799995565)
                  ·
                    refine ⟨684057900958448924998337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1824154402555863799995565 684057900958448924998337)
                    ·
                      rfl

theorem cell22_1998297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_1998297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998297 prefixEnd_1998297 := by exact prefixLift 1998297
  have htrace : WordTrace (prefixWord ++ tailWord_1998297) baseStart_1998297 baseEnd_1998297 := by
    simpa [prefixWord, tailWord_1998297, baseEnd_1998297] using wordTrace_append hprefix tailTrace_1998297
  have hstable : (prefixWord ++ tailWord_1998297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998297).length < 2 ^ (prefixWord ++ tailWord_1998297).sum := by decide
  have hdescent : baseEnd_1998297 < baseStart_1998297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998353 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_1998353 : Nat := 118140960795 + 1998353 * 2 ^ 59
def prefixEnd_1998353 : Nat := 4983230072969 + 3 ^ 40 * 1998353 * 2
def baseEnd_1998353 : Nat := 684077070902883445598165

theorem tailTrace_1998353 : CollatzResearch.WordTrace tailWord_1998353 prefixEnd_1998353 684077070902883445598165 := by
  unfold tailWord_1998353
  simp only [CollatzResearch.WordTrace]
  refine ⟨72885921729315847365903713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48590614486210564910602475 72885921729315847365903713)
  ·
    refine ⟨54664441296986885524427785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72885921729315847365903713 54664441296986885524427785)
    ·
      refine ⟨40998330972740164143320839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54664441296986885524427785 40998330972740164143320839)
      ·
        refine ⟨61497496459110246214981259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40998330972740164143320839 61497496459110246214981259)
        ·
          refine ⟨92246244688665369322471889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61497496459110246214981259 92246244688665369322471889)
          ·
            refine ⟨69184683516499026991853917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92246244688665369322471889 69184683516499026991853917)
            ·
              refine ⟨25944256318687135121945219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69184683516499026991853917 25944256318687135121945219)
              ·
                refine ⟨38916384478030702682917829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25944256318687135121945219 38916384478030702682917829)
                ·
                  refine ⟨7296822089630756753047093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38916384478030702682917829 7296822089630756753047093)
                  ·
                    refine ⟨684077070902883445598165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7296822089630756753047093 684077070902883445598165)
                    ·
                      rfl

theorem cell22_1998353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_1998353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998353 prefixEnd_1998353 := by exact prefixLift 1998353
  have htrace : WordTrace (prefixWord ++ tailWord_1998353) baseStart_1998353 baseEnd_1998353 := by
    simpa [prefixWord, tailWord_1998353, baseEnd_1998353] using wordTrace_append hprefix tailTrace_1998353
  have hstable : (prefixWord ++ tailWord_1998353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998353).length < 2 ^ (prefixWord ++ tailWord_1998353).sum := by decide
  have hdescent : baseEnd_1998353 < baseStart_1998353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998355 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 5]
def baseStart_1998355 : Nat := 118140960795 + 1998355 * 2 ^ 59
def prefixEnd_1998355 : Nat := 4983230072969 + 3 ^ 40 * 1998355 * 2
def baseEnd_1998355 : Nat := 228025918514585369016053

theorem tailTrace_1998355 : CollatzResearch.WordTrace tailWord_1998355 prefixEnd_1998355 228025918514585369016053 := by
  unfold tailWord_1998355
  simp only [CollatzResearch.WordTrace]
  refine ⟨72885994675308601707476519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48590663116872401138317679 72885994675308601707476519)
  ·
    refine ⟨109328992012962902561214779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72885994675308601707476519 109328992012962902561214779)
    ·
      refine ⟨163993488019444353841822169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109328992012962902561214779 163993488019444353841822169)
      ·
        refine ⟨122995116014583265381366627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163993488019444353841822169 122995116014583265381366627)
        ·
          refine ⟨184492674021874898072049941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122995116014583265381366627 184492674021874898072049941)
          ·
            refine ⟨8648094094775385847127341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184492674021874898072049941 8648094094775385847127341)
            ·
              refine ⟨3243035285540769692672753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8648094094775385847127341 3243035285540769692672753)
              ·
                refine ⟨2432276464155577269504565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3243035285540769692672753 2432276464155577269504565)
                ·
                  refine ⟨228025918514585369016053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2432276464155577269504565 228025918514585369016053)
                  ·
                    rfl

theorem cell22_1998355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 5].length) (baseStart_1998355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998355 prefixEnd_1998355 := by exact prefixLift 1998355
  have htrace : WordTrace (prefixWord ++ tailWord_1998355) baseStart_1998355 baseEnd_1998355 := by
    simpa [prefixWord, tailWord_1998355, baseEnd_1998355] using wordTrace_append hprefix tailTrace_1998355
  have hstable : (prefixWord ++ tailWord_1998355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998355).length < 2 ^ (prefixWord ++ tailWord_1998355).sum := by decide
  have hdescent : baseEnd_1998355 < baseStart_1998355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998370 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1998370 : Nat := 118140960795 + 1998370 * 2 ^ 59
def prefixEnd_1998370 : Nat := 4983230072969 + 3 ^ 40 * 1998370 * 2
def baseEnd_1998370 : Nat := 684082890350301067923113

theorem tailTrace_1998370 : CollatzResearch.WordTrace tailWord_1998370 prefixEnd_1998370 684082890350301067923113 := by
  unfold tailWord_1998370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18221635442563564817318141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48591027846836172846181709 18221635442563564817318141)
  ·
    refine ⟨6833113290961336806494303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18221635442563564817318141 6833113290961336806494303)
    ·
      refine ⟨10249669936442005209741455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6833113290961336806494303 10249669936442005209741455)
      ·
        refine ⟨15374504904663007814612183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10249669936442005209741455 15374504904663007814612183)
        ·
          refine ⟨23061757356994511721918275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15374504904663007814612183 23061757356994511721918275)
          ·
            refine ⟨34592636035491767582877413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23061757356994511721918275 34592636035491767582877413)
            ·
              refine ⟨6486119256654706421789515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34592636035491767582877413 6486119256654706421789515)
              ·
                refine ⟨9729178884982059632684273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486119256654706421789515 9729178884982059632684273)
                ·
                  refine ⟨7296884163736544724513205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9729178884982059632684273 7296884163736544724513205)
                  ·
                    refine ⟨684082890350301067923113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7296884163736544724513205 684082890350301067923113)
                    ·
                      rfl

theorem cell22_1998370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1998370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998370 prefixEnd_1998370 := by exact prefixLift 1998370
  have htrace : WordTrace (prefixWord ++ tailWord_1998370) baseStart_1998370 baseEnd_1998370 := by
    simpa [prefixWord, tailWord_1998370, baseEnd_1998370] using wordTrace_append hprefix tailTrace_1998370
  have hstable : (prefixWord ++ tailWord_1998370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998370).length < 2 ^ (prefixWord ++ tailWord_1998370).sum := by decide
  have hdescent : baseEnd_1998370 < baseStart_1998370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998468 : List Nat := [2, 3, 2, 1, 5, 1, 2, 2, 4]
def baseStart_1998468 : Nat := 118140960795 + 1998468 * 2 ^ 59
def prefixEnd_1998468 : Nat := 4983230072969 + 3 ^ 40 * 1998468 * 2
def baseEnd_1998468 : Nat := 228038812584353826324271

theorem tailTrace_1998468 : CollatzResearch.WordTrace tailWord_1998468 prefixEnd_1998468 228038812584353826324271 := by
  unfold tailWord_1998468
  simp only [CollatzResearch.WordTrace]
  refine ⟨36445058061949611003170029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48593410749266148004226705 36445058061949611003170029)
  ·
    refine ⟨13666896773231104126188761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36445058061949611003170029 13666896773231104126188761)
    ·
      refine ⟨10250172579923328094641571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13666896773231104126188761 10250172579923328094641571)
      ·
        refine ⟨15375258869884992141962357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10250172579923328094641571 15375258869884992141962357)
        ·
          refine ⟨1441430519051718013308971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15375258869884992141962357 1441430519051718013308971)
          ·
            refine ⟨2162145778577577019963457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441430519051718013308971 2162145778577577019963457)
            ·
              refine ⟨1621609333933182764972593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162145778577577019963457 1621609333933182764972593)
              ·
                refine ⟨1216207000449887073729445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621609333933182764972593 1216207000449887073729445)
                ·
                  refine ⟨228038812584353826324271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216207000449887073729445 228038812584353826324271)
                  ·
                    rfl

theorem cell22_1998468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_1998468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998468 prefixEnd_1998468 := by exact prefixLift 1998468
  have htrace : WordTrace (prefixWord ++ tailWord_1998468) baseStart_1998468 baseEnd_1998468 := by
    simpa [prefixWord, tailWord_1998468, baseEnd_1998468] using wordTrace_append hprefix tailTrace_1998468
  have hstable : (prefixWord ++ tailWord_1998468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998468).length < 2 ^ (prefixWord ++ tailWord_1998468).sum := by decide
  have hdescent : baseEnd_1998468 < baseStart_1998468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998494 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1998494 : Nat := 118140960795 + 1998494 * 2 ^ 59
def prefixEnd_1998494 : Nat := 4983230072969 + 3 ^ 40 * 1998494 * 2
def baseEnd_1998494 : Nat := 684125338084406077822733

theorem tailTrace_1998494 : CollatzResearch.WordTrace tailWord_1998494 prefixEnd_1998494 684125338084406077822733 := by
  unfold tailWord_1998494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9111383052725628555848317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48594042947870018964524357 9111383052725628555848317)
  ·
    refine ⟨3416768644772110708443119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9111383052725628555848317 3416768644772110708443119)
    ·
      refine ⟨5125152967158166062664679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3416768644772110708443119 5125152967158166062664679)
      ·
        refine ⟨7687729450737249093997019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5125152967158166062664679 7687729450737249093997019)
        ·
          refine ⟨11531594176105873640995529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7687729450737249093997019 11531594176105873640995529)
          ·
            refine ⟨8648695632079405230746647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11531594176105873640995529 8648695632079405230746647)
            ·
              refine ⟨12973043448119107846119971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648695632079405230746647 12973043448119107846119971)
              ·
                refine ⟨19459565172178661769179957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12973043448119107846119971 19459565172178661769179957)
                ·
                  refine ⟨1824334234891749540860621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19459565172178661769179957 1824334234891749540860621)
                  ·
                    refine ⟨684125338084406077822733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1824334234891749540860621 684125338084406077822733)
                    ·
                      rfl

theorem cell22_1998494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1998494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998494 prefixEnd_1998494 := by exact prefixLift 1998494
  have htrace : WordTrace (prefixWord ++ tailWord_1998494) baseStart_1998494 baseEnd_1998494 := by
    simpa [prefixWord, tailWord_1998494, baseEnd_1998494] using wordTrace_append hprefix tailTrace_1998494
  have hstable : (prefixWord ++ tailWord_1998494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998494).length < 2 ^ (prefixWord ++ tailWord_1998494).sum := by decide
  have hdescent : baseEnd_1998494 < baseStart_1998494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998498 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1998498 : Nat := 118140960795 + 1998498 * 2 ^ 59
def prefixEnd_1998498 : Nat := 4983230072969 + 3 ^ 40 * 1998498 * 2
def baseEnd_1998498 : Nat := 684126707366151400722721

theorem tailTrace_1998498 : CollatzResearch.WordTrace tailWord_1998498 prefixEnd_1998498 684126707366151400722721 := by
  unfold tailWord_1998498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18222802578447634282483037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48594140209193691419954765 18222802578447634282483037)
  ·
    refine ⟨6833550966917862855931139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18222802578447634282483037 6833550966917862855931139)
    ·
      refine ⟨10250326450376794283896709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6833550966917862855931139 10250326450376794283896709)
      ·
        refine ⟨1921936209445648928230633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10250326450376794283896709 1921936209445648928230633)
        ·
          refine ⟨1441452157084236696172975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1921936209445648928230633 1441452157084236696172975)
          ·
            refine ⟨2162178235626355044259463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441452157084236696172975 2162178235626355044259463)
            ·
              refine ⟨3243267353439532566389195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162178235626355044259463 3243267353439532566389195)
              ·
                refine ⟨4864901030159298849583793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243267353439532566389195 4864901030159298849583793)
                ·
                  refine ⟨3648675772619474137187845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4864901030159298849583793 3648675772619474137187845)
                  ·
                    refine ⟨684126707366151400722721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3648675772619474137187845 684126707366151400722721)
                    ·
                      rfl

theorem cell22_1998498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1998498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998498 prefixEnd_1998498 := by exact prefixLift 1998498
  have htrace : WordTrace (prefixWord ++ tailWord_1998498) baseStart_1998498 baseEnd_1998498 := by
    simpa [prefixWord, tailWord_1998498, baseEnd_1998498] using wordTrace_append hprefix tailTrace_1998498
  have hstable : (prefixWord ++ tailWord_1998498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998498).length < 2 ^ (prefixWord ++ tailWord_1998498).sum := by decide
  have hdescent : baseEnd_1998498 < baseStart_1998498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998524 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 5]
def baseStart_1998524 : Nat := 118140960795 + 1998524 * 2 ^ 59
def prefixEnd_1998524 : Nat := 4983230072969 + 3 ^ 40 * 1998524 * 2
def baseEnd_1998524 : Nat := 228045202565831999857547

theorem tailTrace_1998524 : CollatzResearch.WordTrace tailWord_1998524 prefixEnd_1998524 228045202565831999857547 := by
  unfold tailWord_1998524
  simp only [CollatzResearch.WordTrace]
  refine ⟨36446079305848171785189313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48594772407797562380252417 36446079305848171785189313)
  ·
    refine ⟨27334559479386128838891985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36446079305848171785189313 27334559479386128838891985)
    ·
      refine ⟨20500919609539596629168989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27334559479386128838891985 20500919609539596629168989)
      ·
        refine ⟨7687844853577348735938371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20500919609539596629168989 7687844853577348735938371)
        ·
          refine ⟨11531767280366023103907557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7687844853577348735938371 11531767280366023103907557)
          ·
            refine ⟨2162206365068629331982667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11531767280366023103907557 2162206365068629331982667)
            ·
              refine ⟨3243309547602943997974001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162206365068629331982667 3243309547602943997974001)
              ·
                refine ⟨2432482160702207998480501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3243309547602943997974001 2432482160702207998480501)
                ·
                  refine ⟨228045202565831999857547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2432482160702207998480501 228045202565831999857547)
                  ·
                    rfl

theorem cell22_1998524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_1998524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998524 prefixEnd_1998524 := by exact prefixLift 1998524
  have htrace : WordTrace (prefixWord ++ tailWord_1998524) baseStart_1998524 baseEnd_1998524 := by
    simpa [prefixWord, tailWord_1998524, baseEnd_1998524] using wordTrace_append hprefix tailTrace_1998524
  have hstable : (prefixWord ++ tailWord_1998524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998524).length < 2 ^ (prefixWord ++ tailWord_1998524).sum := by decide
  have hdescent : baseEnd_1998524 < baseStart_1998524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998554 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_1998554 : Nat := 118140960795 + 1998554 * 2 ^ 59
def prefixEnd_1998554 : Nat := 4983230072969 + 3 ^ 40 * 1998554 * 2
def baseEnd_1998554 : Nat := 684145877310585921322549

theorem tailTrace_1998554 : CollatzResearch.WordTrace tailWord_1998554 prefixEnd_1998554 684145877310585921322549 := by
  unfold tailWord_1998554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18223313200396914673492679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48595501867725105795980477 18223313200396914673492679)
  ·
    refine ⟨27334969800595372010239019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18223313200396914673492679 27334969800595372010239019)
    ·
      refine ⟨41002454700893058015358529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27334969800595372010239019 41002454700893058015358529)
      ·
        refine ⟨30751841025669793511518897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41002454700893058015358529 30751841025669793511518897)
        ·
          refine ⟨23063880769252345133639173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30751841025669793511518897 23063880769252345133639173)
          ·
            refine ⟨4324477644234814712557345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23063880769252345133639173 4324477644234814712557345)
            ·
              refine ⟨3243358233176111034418009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4324477644234814712557345 3243358233176111034418009)
              ·
                refine ⟨2432518674882083275813507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3243358233176111034418009 2432518674882083275813507)
                ·
                  refine ⟨3648778012323124913720261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432518674882083275813507 3648778012323124913720261)
                  ·
                    refine ⟨684145877310585921322549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3648778012323124913720261 684145877310585921322549)
                    ·
                      rfl

theorem cell22_1998554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_1998554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998554 prefixEnd_1998554 := by exact prefixLift 1998554
  have htrace : WordTrace (prefixWord ++ tailWord_1998554) baseStart_1998554 baseEnd_1998554 := by
    simpa [prefixWord, tailWord_1998554, baseEnd_1998554] using wordTrace_append hprefix tailTrace_1998554
  have hstable : (prefixWord ++ tailWord_1998554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998554).length < 2 ^ (prefixWord ++ tailWord_1998554).sum := by decide
  have hdescent : baseEnd_1998554 < baseStart_1998554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998605 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1998605 : Nat := 118140960795 + 1998605 * 2 ^ 59
def prefixEnd_1998605 : Nat := 4983230072969 + 3 ^ 40 * 1998605 * 2
def baseEnd_1998605 : Nat := 684163335652838788297393

theorem tailTrace_1998605 : CollatzResearch.WordTrace tailWord_1998605 prefixEnd_1998605 684163335652838788297393 := by
  unfold tailWord_1998605
  simp only [CollatzResearch.WordTrace]
  refine ⟨72895112924402894404077269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48596741949601929602718179 72895112924402894404077269)
  ·
    refine ⟨1708479209165692837595561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 72895112924402894404077269 1708479209165692837595561)
    ·
      refine ⟨1281359406874269628196671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1708479209165692837595561 1281359406874269628196671)
      ·
        refine ⟨1922039110311404442295007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281359406874269628196671 1922039110311404442295007)
        ·
          refine ⟨2883058665467106663442511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922039110311404442295007 2883058665467106663442511)
          ·
            refine ⟨4324587998200659995163767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883058665467106663442511 4324587998200659995163767)
            ·
              refine ⟨6486881997300989992745651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324587998200659995163767 6486881997300989992745651)
              ·
                refine ⟨9730322995951484989118477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486881997300989992745651 9730322995951484989118477)
                ·
                  refine ⟨3648871123481806870919429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9730322995951484989118477 3648871123481806870919429)
                  ·
                    refine ⟨684163335652838788297393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3648871123481806870919429 684163335652838788297393)
                    ·
                      rfl

theorem cell22_1998605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1998605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998605 prefixEnd_1998605 := by exact prefixLift 1998605
  have htrace : WordTrace (prefixWord ++ tailWord_1998605) baseStart_1998605 baseEnd_1998605 := by
    simpa [prefixWord, tailWord_1998605, baseEnd_1998605] using wordTrace_append hprefix tailTrace_1998605
  have hstable : (prefixWord ++ tailWord_1998605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998605).length < 2 ^ (prefixWord ++ tailWord_1998605).sum := by decide
  have hdescent : baseEnd_1998605 < baseStart_1998605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998644 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1998644 : Nat := 118140960795 + 1998644 * 2 ^ 59
def prefixEnd_1998644 : Nat := 4983230072969 + 3 ^ 40 * 1998644 * 2
def baseEnd_1998644 : Nat := 684176686149855686572273

theorem tailTrace_1998644 : CollatzResearch.WordTrace tailWord_1998644 prefixEnd_1998644 684176686149855686572273 := by
  unfold tailWord_1998644
  simp only [CollatzResearch.WordTrace]
  refine ⟨36448267685630802032373493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48597690247507736043164657 36448267685630802032373493)
  ·
    refine ⟨3417025095527887690535015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36448267685630802032373493 3417025095527887690535015)
    ·
      refine ⟨5125537643291831535802523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3417025095527887690535015 5125537643291831535802523)
      ·
        refine ⟨7688306464937747303703785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5125537643291831535802523 7688306464937747303703785)
        ·
          refine ⟨5766229848703310477777839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7688306464937747303703785 5766229848703310477777839)
          ·
            refine ⟨8649344773054965716666759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766229848703310477777839 8649344773054965716666759)
            ·
              refine ⟨12974017159582448575000139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8649344773054965716666759 12974017159582448575000139)
              ·
                refine ⟨19461025739373672862500209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12974017159582448575000139 19461025739373672862500209)
                ·
                  refine ⟨14595769304530254646875157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19461025739373672862500209 14595769304530254646875157)
                  ·
                    refine ⟨684176686149855686572273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14595769304530254646875157 684176686149855686572273)
                    ·
                      rfl

theorem cell22_1998644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1998644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998644 prefixEnd_1998644 := by exact prefixLift 1998644
  have htrace : WordTrace (prefixWord ++ tailWord_1998644) baseStart_1998644 baseEnd_1998644 := by
    simpa [prefixWord, tailWord_1998644, baseEnd_1998644] using wordTrace_append hprefix tailTrace_1998644
  have hstable : (prefixWord ++ tailWord_1998644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998644).length < 2 ^ (prefixWord ++ tailWord_1998644).sum := by decide
  have hdescent : baseEnd_1998644 < baseStart_1998644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998689 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1998689 : Nat := 118140960795 + 1998689 * 2 ^ 59
def prefixEnd_1998689 : Nat := 4983230072969 + 3 ^ 40 * 1998689 * 2
def baseEnd_1998689 : Nat := 684192090569490569197135

theorem tailTrace_1998689 : CollatzResearch.WordTrace tailWord_1998689 prefixEnd_1998689 684192090569490569197135 := by
  unfold tailWord_1998689
  simp only [CollatzResearch.WordTrace]
  refine ⟨72898176656098576750135121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48598784437399051166756747 72898176656098576750135121)
  ·
    refine ⟨54673632492073932562601341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72898176656098576750135121 54673632492073932562601341)
    ·
      refine ⟨20502612184527724710975503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54673632492073932562601341 20502612184527724710975503)
      ·
        refine ⟨30753918276791587066463255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20502612184527724710975503 30753918276791587066463255)
        ·
          refine ⟨46130877415187380599694883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30753918276791587066463255 46130877415187380599694883)
          ·
            refine ⟨69196316122781070899542325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46130877415187380599694883 69196316122781070899542325)
            ·
              refine ⟨6487154636510725396832093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69196316122781070899542325 6487154636510725396832093)
              ·
                refine ⟨2432682988691522023812035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6487154636510725396832093 2432682988691522023812035)
                ·
                  refine ⟨3649024483037283035718053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432682988691522023812035 3649024483037283035718053)
                  ·
                    refine ⟨684192090569490569197135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3649024483037283035718053 684192090569490569197135)
                    ·
                      rfl

theorem cell22_1998689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1998689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998689 prefixEnd_1998689 := by exact prefixLift 1998689
  have htrace : WordTrace (prefixWord ++ tailWord_1998689) baseStart_1998689 baseEnd_1998689 := by
    simpa [prefixWord, tailWord_1998689, baseEnd_1998689] using wordTrace_append hprefix tailTrace_1998689
  have hstable : (prefixWord ++ tailWord_1998689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998689).length < 2 ^ (prefixWord ++ tailWord_1998689).sum := by decide
  have hdescent : baseEnd_1998689 < baseStart_1998689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998738 : List Nat := [3, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_1998738 : Nat := 118140960795 + 1998738 * 2 ^ 59
def prefixEnd_1998738 : Nat := 4983230072969 + 3 ^ 40 * 1998738 * 2
def baseEnd_1998738 : Nat := 228069621423623591573995

theorem tailTrace_1998738 : CollatzResearch.WordTrace tailWord_1998738 prefixEnd_1998738 228069621423623591573995 := by
  unfold tailWord_1998738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18224990958230264529667217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48599975888614038745779245 18224990958230264529667217)
  ·
    refine ⟨13668743218672698397250413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18224990958230264529667217 13668743218672698397250413)
    ·
      refine ⟨5125778707002261898968905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13668743218672698397250413 5125778707002261898968905)
      ·
        refine ⟨3844334030251696424226679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5125778707002261898968905 3844334030251696424226679)
        ·
          refine ⟨5766501045377544636340019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844334030251696424226679 5766501045377544636340019)
          ·
            refine ⟨8649751568066316954510029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766501045377544636340019 8649751568066316954510029)
            ·
              refine ⟨3243656838024868857941261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8649751568066316954510029 3243656838024868857941261)
              ·
                refine ⟨1216371314259325821727973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3243656838024868857941261 1216371314259325821727973)
                ·
                  refine ⟨228069621423623591573995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216371314259325821727973 228069621423623591573995)
                  ·
                    rfl

theorem cell22_1998738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_1998738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998738 prefixEnd_1998738 := by exact prefixLift 1998738
  have htrace : WordTrace (prefixWord ++ tailWord_1998738) baseStart_1998738 baseEnd_1998738 := by
    simpa [prefixWord, tailWord_1998738, baseEnd_1998738] using wordTrace_append hprefix tailTrace_1998738
  have hstable : (prefixWord ++ tailWord_1998738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998738).length < 2 ^ (prefixWord ++ tailWord_1998738).sum := by decide
  have hdescent : baseEnd_1998738 < baseStart_1998738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998749 : List Nat := [1, 4, 2, 1, 2, 4, 8]
def baseStart_1998749 : Nat := 118140960795 + 1998749 * 2 ^ 59
def prefixEnd_1998749 : Nat := 4983230072969 + 3 ^ 40 * 1998749 * 2
def baseEnd_1998749 : Nat := 25341208510950756025813

theorem tailTrace_1998749 : CollatzResearch.WordTrace tailWord_1998749 prefixEnd_1998749 25341208510950756025813 := by
  unfold tailWord_1998749
  simp only [CollatzResearch.WordTrace]
  refine ⟨72900365035881206997319301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48600243357254137998212867 72900365035881206997319301)
  ·
    refine ⟨13668818444227726311997369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72900365035881206997319301 13668818444227726311997369)
    ·
      refine ⟨10251613833170794733998027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13668818444227726311997369 10251613833170794733998027)
      ·
        refine ⟨15377420749756192100997041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10251613833170794733998027 15377420749756192100997041)
        ·
          refine ⟨11533065562317144075747781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15377420749756192100997041 11533065562317144075747781)
          ·
            refine ⟨2162449792934464514202709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11533065562317144075747781 2162449792934464514202709)
            ·
              refine ⟨25341208510950756025813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2162449792934464514202709 25341208510950756025813)
              ·
                rfl

theorem cell22_1998749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 8].length) (baseStart_1998749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998749 prefixEnd_1998749 := by exact prefixLift 1998749
  have htrace : WordTrace (prefixWord ++ tailWord_1998749) baseStart_1998749 baseEnd_1998749 := by
    simpa [prefixWord, tailWord_1998749, baseEnd_1998749] using wordTrace_append hprefix tailTrace_1998749
  have hstable : (prefixWord ++ tailWord_1998749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998749).length < 2 ^ (prefixWord ++ tailWord_1998749).sum := by decide
  have hdescent : baseEnd_1998749 < baseStart_1998749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998751 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 2, 4]
def baseStart_1998751 : Nat := 118140960795 + 1998751 * 2 ^ 59
def prefixEnd_1998751 : Nat := 4983230072969 + 3 ^ 40 * 1998751 * 2
def baseEnd_1998751 : Nat := 684213314436543074146945

theorem tailTrace_1998751 : CollatzResearch.WordTrace tailWord_1998751 prefixEnd_1998751 684213314436543074146945 := by
  unfold tailWord_1998751
  simp only [CollatzResearch.WordTrace]
  refine ⟨72900437981873961338892107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48600291987915974225928071 72900437981873961338892107)
  ·
    refine ⟨109350656972810942008338161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72900437981873961338892107 109350656972810942008338161)
    ·
      refine ⟨82012992729608206506253621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109350656972810942008338161 82012992729608206506253621)
      ·
        refine ⟨7688718068400769359961277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82012992729608206506253621 7688718068400769359961277)
        ·
          refine ⟨2883269275650288509985479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7688718068400769359961277 2883269275650288509985479)
          ·
            refine ⟨4324903913475432764978219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883269275650288509985479 4324903913475432764978219)
            ·
              refine ⟨6487355870213149147467329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324903913475432764978219 6487355870213149147467329)
              ·
                refine ⟨4865516902659861860600497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6487355870213149147467329 4865516902659861860600497)
                ·
                  refine ⟨3649137676994896395450373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4865516902659861860600497 3649137676994896395450373)
                  ·
                    refine ⟨684213314436543074146945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3649137676994896395450373 684213314436543074146945)
                    ·
                      rfl

theorem cell22_1998751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_1998751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998751 prefixEnd_1998751 := by exact prefixLift 1998751
  have htrace : WordTrace (prefixWord ++ tailWord_1998751) baseStart_1998751 baseEnd_1998751 := by
    simpa [prefixWord, tailWord_1998751, baseEnd_1998751] using wordTrace_append hprefix tailTrace_1998751
  have hstable : (prefixWord ++ tailWord_1998751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998751).length < 2 ^ (prefixWord ++ tailWord_1998751).sum := by decide
  have hdescent : baseEnd_1998751 < baseStart_1998751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998798 : List Nat := [4, 1, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_1998798 : Nat := 118140960795 + 1998798 * 2 ^ 59
def prefixEnd_1998798 : Nat := 4983230072969 + 3 ^ 40 * 1998798 * 2
def baseEnd_1998798 : Nat := 684229403497050618221801

theorem tailTrace_1998798 : CollatzResearch.WordTrace tailWord_1998798 prefixEnd_1998798 684229403497050618221801 := by
  unfold tailWord_1998798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112769026587961045731631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48601434808469125577235365 9112769026587961045731631)
  ·
    refine ⟨13669153539881941568597447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9112769026587961045731631 13669153539881941568597447)
    ·
      refine ⟨20503730309822912352896171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13669153539881941568597447 20503730309822912352896171)
      ·
        refine ⟨30755595464734368529344257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20503730309822912352896171 30755595464734368529344257)
        ·
          refine ⟨23066696598550776397008193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30755595464734368529344257 23066696598550776397008193)
          ·
            refine ⟨17300022448913082297756145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23066696598550776397008193 17300022448913082297756145)
            ·
              refine ⟨12975016836684811723317109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17300022448913082297756145 12975016836684811723317109)
              ·
                refine ⟨1216407828439201099060979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12975016836684811723317109 1216407828439201099060979)
                ·
                  refine ⟨1824611742658801648591469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216407828439201099060979 1824611742658801648591469)
                  ·
                    refine ⟨684229403497050618221801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1824611742658801648591469 684229403497050618221801)
                    ·
                      rfl

theorem cell22_1998798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_1998798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998798 prefixEnd_1998798 := by exact prefixLift 1998798
  have htrace : WordTrace (prefixWord ++ tailWord_1998798) baseStart_1998798 baseEnd_1998798 := by
    simpa [prefixWord, tailWord_1998798, baseEnd_1998798] using wordTrace_append hprefix tailTrace_1998798
  have hstable : (prefixWord ++ tailWord_1998798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998798).length < 2 ^ (prefixWord ++ tailWord_1998798).sum := by decide
  have hdescent : baseEnd_1998798 < baseStart_1998798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998815 : List Nat := [1, 1, 2, 3, 4, 1, 4, 2, 1, 3]
def baseStart_1998815 : Nat := 118140960795 + 1998815 * 2 ^ 59
def prefixEnd_1998815 : Nat := 4983230072969 + 3 ^ 40 * 1998815 * 2
def baseEnd_1998815 : Nat := 684235222944468240546749

theorem tailTrace_1998815 : CollatzResearch.WordTrace tailWord_1998815 prefixEnd_1998815 684235222944468240546749 := by
  unfold tailWord_1998815
  simp only [CollatzResearch.WordTrace]
  refine ⟨72902772253642100269221899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48601848169094733512814599 72902772253642100269221899)
  ·
    refine ⟨109354158380463150403832849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72902772253642100269221899 109354158380463150403832849)
    ·
      refine ⟨82015618785347362802874637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109354158380463150403832849 82015618785347362802874637)
      ·
        refine ⟨30755857044505261051077989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82015618785347362802874637 30755857044505261051077989)
        ·
          refine ⟨5766723195844736447077123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30755857044505261051077989 5766723195844736447077123)
          ·
            refine ⟨8650084793767104670615685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766723195844736447077123 8650084793767104670615685)
            ·
              refine ⟨1621890898831332125740441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8650084793767104670615685 1621890898831332125740441)
              ·
                refine ⟨1216418174123499094305331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621890898831332125740441 1216418174123499094305331)
                ·
                  refine ⟨1824627261185248641457997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216418174123499094305331 1824627261185248641457997)
                  ·
                    refine ⟨684235222944468240546749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1824627261185248641457997 684235222944468240546749)
                    ·
                      rfl

theorem cell22_1998815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 3].length) (baseStart_1998815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998815 prefixEnd_1998815 := by exact prefixLift 1998815
  have htrace : WordTrace (prefixWord ++ tailWord_1998815) baseStart_1998815 baseEnd_1998815 := by
    simpa [prefixWord, tailWord_1998815, baseEnd_1998815] using wordTrace_append hprefix tailTrace_1998815
  have hstable : (prefixWord ++ tailWord_1998815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998815).length < 2 ^ (prefixWord ++ tailWord_1998815).sum := by decide
  have hdescent : baseEnd_1998815 < baseStart_1998815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998858 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1998858 : Nat := 118140960795 + 1998858 * 2 ^ 59
def prefixEnd_1998858 : Nat := 4983230072969 + 3 ^ 40 * 1998858 * 2
def baseEnd_1998858 : Nat := 684249942723230461721617

theorem tailTrace_1998858 : CollatzResearch.WordTrace tailWord_1998858 prefixEnd_1998858 684249942723230461721617 := by
  unfold tailWord_1998858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18226085148121579653259307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48602893728324212408691485 18226085148121579653259307)
  ·
    refine ⟨27339127722182369479888961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18226085148121579653259307 27339127722182369479888961)
    ·
      refine ⟨20504345791636777109916721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27339127722182369479888961 20504345791636777109916721)
      ·
        refine ⟨15378259343727582832437541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20504345791636777109916721 15378259343727582832437541)
        ·
          refine ⟨2883423626948921781082039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15378259343727582832437541 2883423626948921781082039)
          ·
            refine ⟨4325135440423382671623059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883423626948921781082039 4325135440423382671623059)
            ·
              refine ⟨6487703160635074007434589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4325135440423382671623059 6487703160635074007434589)
              ·
                refine ⟨2432888685238152752787971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6487703160635074007434589 2432888685238152752787971)
                ·
                  refine ⟨3649333027857229129181957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432888685238152752787971 3649333027857229129181957)
                  ·
                    refine ⟨684249942723230461721617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3649333027857229129181957 684249942723230461721617)
                    ·
                      rfl

theorem cell22_1998858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1998858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998858 prefixEnd_1998858 := by exact prefixLift 1998858
  have htrace : WordTrace (prefixWord ++ tailWord_1998858) baseStart_1998858 baseEnd_1998858 := by
    simpa [prefixWord, tailWord_1998858, baseEnd_1998858] using wordTrace_append hprefix tailTrace_1998858
  have hstable : (prefixWord ++ tailWord_1998858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998858).length < 2 ^ (prefixWord ++ tailWord_1998858).sum := by decide
  have hdescent : baseEnd_1998858 < baseStart_1998858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998901 : List Nat := [1, 3, 3, 1, 1, 1, 6, 6]
def baseStart_1998901 : Nat := 118140960795 + 1998901 * 2 ^ 59
def prefixEnd_1998901 : Nat := 4983230072969 + 3 ^ 40 * 1998901 * 2
def baseEnd_1998901 : Nat := 76029406944665853655165

theorem tailTrace_1998901 : CollatzResearch.WordTrace tailWord_1998901 prefixEnd_1998901 76029406944665853655165 := by
  unfold tailWord_1998901
  simp only [CollatzResearch.WordTrace]
  refine ⟨72905908931330536956852557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48603939287553691304568371 72905908931330536956852557)
  ·
    refine ⟨27339715849248951358819709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72905908931330536956852557 27339715849248951358819709)
    ·
      refine ⟨10252393443468356759557391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27339715849248951358819709 10252393443468356759557391)
      ·
        refine ⟨15378590165202535139336087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10252393443468356759557391 15378590165202535139336087)
        ·
          refine ⟨23067885247803802709004131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15378590165202535139336087 23067885247803802709004131)
          ·
            refine ⟨34601827871705704063506197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23067885247803802709004131 34601827871705704063506197)
            ·
              refine ⟨1621960681486204877976853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34601827871705704063506197 1621960681486204877976853)
              ·
                refine ⟨76029406944665853655165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1621960681486204877976853 76029406944665853655165)
                ·
                  rfl

theorem cell22_1998901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 6].length) (baseStart_1998901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998901 prefixEnd_1998901 := by exact prefixLift 1998901
  have htrace : WordTrace (prefixWord ++ tailWord_1998901) baseStart_1998901 baseEnd_1998901 := by
    simpa [prefixWord, tailWord_1998901, baseEnd_1998901] using wordTrace_append hprefix tailTrace_1998901
  have hstable : (prefixWord ++ tailWord_1998901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998901).length < 2 ^ (prefixWord ++ tailWord_1998901).sum := by decide
  have hdescent : baseEnd_1998901 < baseStart_1998901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998933 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_1998933 : Nat := 118140960795 + 1998933 * 2 ^ 59
def prefixEnd_1998933 : Nat := 4983230072969 + 3 ^ 40 * 1998933 * 2
def baseEnd_1998933 : Nat := 684275616755955266096387

theorem tailTrace_1998933 : CollatzResearch.WordTrace tailWord_1998933 prefixEnd_1998933 684275616755955266096387 := by
  unfold tailWord_1998933
  simp only [CollatzResearch.WordTrace]
  refine ⟨72907076067214606422017453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48604717378143070948011635 72907076067214606422017453)
  ·
    refine ⟨27340153525205477408256545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72907076067214606422017453 27340153525205477408256545)
    ·
      refine ⟨20505115143904108056192409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27340153525205477408256545 20505115143904108056192409)
      ·
        refine ⟨15378836357928081042144307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20505115143904108056192409 15378836357928081042144307)
        ·
          refine ⟨23068254536892121563216461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15378836357928081042144307 23068254536892121563216461)
          ·
            refine ⟨8650595451334545586206173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23068254536892121563216461 8650595451334545586206173)
            ·
              refine ⟨3243973294250454594827315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8650595451334545586206173 3243973294250454594827315)
              ·
                refine ⟨4865959941375681892240973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243973294250454594827315 4865959941375681892240973)
                ·
                  refine ⟨1824734978015880709590365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4865959941375681892240973 1824734978015880709590365)
                  ·
                    refine ⟨684275616755955266096387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1824734978015880709590365 684275616755955266096387)
                    ·
                      rfl

theorem cell22_1998933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_1998933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998933 prefixEnd_1998933 := by exact prefixLift 1998933
  have htrace : WordTrace (prefixWord ++ tailWord_1998933) baseStart_1998933 baseEnd_1998933 := by
    simpa [prefixWord, tailWord_1998933, baseEnd_1998933] using wordTrace_append hprefix tailTrace_1998933
  have hstable : (prefixWord ++ tailWord_1998933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998933).length < 2 ^ (prefixWord ++ tailWord_1998933).sum := by decide
  have hdescent : baseEnd_1998933 < baseStart_1998933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998984 : List Nat := [2, 1, 3, 4, 1, 3, 2, 2, 1, 3]
def baseStart_1998984 : Nat := 118140960795 + 1998984 * 2 ^ 59
def prefixEnd_1998984 : Nat := 4983230072969 + 3 ^ 40 * 1998984 * 2
def baseEnd_1998984 : Nat := 684293075098208133071231

theorem tailTrace_1998984 : CollatzResearch.WordTrace tailWord_1998984 prefixEnd_1998984 684293075098208133071231 := by
  unfold tailWord_1998984
  simp only [CollatzResearch.WordTrace]
  refine ⟨36454468095014921066062003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48605957460019894754749337 36454468095014921066062003)
  ·
    refine ⟨54681702142522381599093005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36454468095014921066062003 54681702142522381599093005)
    ·
      refine ⟨20505638303445893099659877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54681702142522381599093005 20505638303445893099659877)
      ·
        refine ⟨3844807181896104956186227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20505638303445893099659877 3844807181896104956186227)
        ·
          refine ⟨5767210772844157434279341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844807181896104956186227 5767210772844157434279341)
          ·
            refine ⟨2162704039816559037854753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5767210772844157434279341 2162704039816559037854753)
            ·
              refine ⟨1622028029862419278391065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162704039816559037854753 1622028029862419278391065)
              ·
                refine ⟨1216521022396814458793299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622028029862419278391065 1216521022396814458793299)
                ·
                  refine ⟨1824781533595221688189949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216521022396814458793299 1824781533595221688189949)
                  ·
                    refine ⟨684293075098208133071231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1824781533595221688189949 684293075098208133071231)
                    ·
                      rfl

theorem cell22_1998984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_1998984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1998984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1998984 prefixEnd_1998984 := by exact prefixLift 1998984
  have htrace : WordTrace (prefixWord ++ tailWord_1998984) baseStart_1998984 baseEnd_1998984 := by
    simpa [prefixWord, tailWord_1998984, baseEnd_1998984] using wordTrace_append hprefix tailTrace_1998984
  have hstable : (prefixWord ++ tailWord_1998984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998984).length < 2 ^ (prefixWord ++ tailWord_1998984).sum := by decide
  have hdescent : baseEnd_1998984 < baseStart_1998984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999040 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 2, 3]
def baseStart_1999040 : Nat := 118140960795 + 1999040 * 2 ^ 59
def prefixEnd_1999040 : Nat := 4983230072969 + 3 ^ 40 * 1999040 * 2
def baseEnd_1999040 : Nat := 684312245042642653671059

theorem tailTrace_1999040 : CollatzResearch.WordTrace tailWord_1999040 prefixEnd_1999040 684312245042642653671059 := by
  unfold tailWord_1999040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36455489338913481848081287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48607319118551309130775049 36455489338913481848081287)
  ·
    refine ⟨54683234008370222772121931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36455489338913481848081287 54683234008370222772121931)
    ·
      refine ⟨82024851012555334158182897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54683234008370222772121931 82024851012555334158182897)
      ·
        refine ⟨61518638259416500618637173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82024851012555334158182897 61518638259416500618637173)
        ·
          refine ⟨5767372336820296932997235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61518638259416500618637173 5767372336820296932997235)
          ·
            refine ⟨8651058505230445399495853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767372336820296932997235 8651058505230445399495853)
            ·
              refine ⟨3244146939461417024810945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8651058505230445399495853 3244146939461417024810945)
              ·
                refine ⟨2433110204596062768608209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244146939461417024810945 2433110204596062768608209)
                ·
                  refine ⟨1824832653447047076456157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2433110204596062768608209 1824832653447047076456157)
                  ·
                    refine ⟨684312245042642653671059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1824832653447047076456157 684312245042642653671059)
                    ·
                      rfl

theorem cell22_1999040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_1999040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999040 prefixEnd_1999040 := by exact prefixLift 1999040
  have htrace : WordTrace (prefixWord ++ tailWord_1999040) baseStart_1999040 baseEnd_1999040 := by
    simpa [prefixWord, tailWord_1999040, baseEnd_1999040] using wordTrace_append hprefix tailTrace_1999040
  have hstable : (prefixWord ++ tailWord_1999040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999040).length < 2 ^ (prefixWord ++ tailWord_1999040).sum := by decide
  have hdescent : baseEnd_1999040 < baseStart_1999040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999042 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1999042 : Nat := 118140960795 + 1999042 * 2 ^ 59
def prefixEnd_1999042 : Nat := 4983230072969 + 3 ^ 40 * 1999042 * 2
def baseEnd_1999042 : Nat := 228104309894505105040351

theorem tailTrace_1999042 : CollatzResearch.WordTrace tailWord_1999042 prefixEnd_1999042 228104309894505105040351 := by
  unfold tailWord_1999042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18227762905954929509433845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48607367749213145358490253 18227762905954929509433845)
  ·
    refine ⟨1708852772433274641509423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18227762905954929509433845 1708852772433274641509423)
    ·
      refine ⟨2563279158649911962264135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1708852772433274641509423 2563279158649911962264135)
      ·
        refine ⟨3844918737974867943396203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2563279158649911962264135 3844918737974867943396203)
        ·
          refine ⟨5767378106962301915094305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844918737974867943396203 5767378106962301915094305)
          ·
            refine ⟨4325533580221726436320729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5767378106962301915094305 4325533580221726436320729)
            ·
              refine ⟨3244150185166294827240547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325533580221726436320729 3244150185166294827240547)
              ·
                refine ⟨4866225277749442240860821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244150185166294827240547 4866225277749442240860821)
                ·
                  refine ⟨228104309894505105040351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4866225277749442240860821 228104309894505105040351)
                  ·
                    rfl

theorem cell22_1999042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1999042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999042 prefixEnd_1999042 := by exact prefixLift 1999042
  have htrace : WordTrace (prefixWord ++ tailWord_1999042) baseStart_1999042 baseEnd_1999042 := by
    simpa [prefixWord, tailWord_1999042, baseEnd_1999042] using wordTrace_append hprefix tailTrace_1999042
  have hstable : (prefixWord ++ tailWord_1999042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999042).length < 2 ^ (prefixWord ++ tailWord_1999042).sum := by decide
  have hdescent : baseEnd_1999042 < baseStart_1999042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999066 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_1999066 : Nat := 118140960795 + 1999066 * 2 ^ 59
def prefixEnd_1999066 : Nat := 4983230072969 + 3 ^ 40 * 1999066 * 2
def baseEnd_1999066 : Nat := 684321145373987252520979

theorem tailTrace_1999066 : CollatzResearch.WordTrace tailWord_1999066 prefixEnd_1999066 684321145373987252520979 := by
  unfold tailWord_1999066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18227981743933192534152263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48607951317155180091072701 18227981743933192534152263)
  ·
    refine ⟨27341972615899788801228395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18227981743933192534152263 27341972615899788801228395)
    ·
      refine ⟨41012958923849683201842593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27341972615899788801228395 41012958923849683201842593)
      ·
        refine ⟨30759719192887262401381945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41012958923849683201842593 30759719192887262401381945)
        ·
          refine ⟨23069789394665446801036459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30759719192887262401381945 23069789394665446801036459)
          ·
            refine ⟨34604684091998170201554689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23069789394665446801036459 34604684091998170201554689)
            ·
              refine ⟨25953513068998627651166017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34604684091998170201554689 25953513068998627651166017)
              ·
                refine ⟨19465134801748970738374513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25953513068998627651166017 19465134801748970738374513)
                ·
                  refine ⟨14598851101311728053780885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19465134801748970738374513 14598851101311728053780885)
                  ·
                    refine ⟨684321145373987252520979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14598851101311728053780885 684321145373987252520979)
                    ·
                      rfl

theorem cell22_1999066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_1999066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999066 prefixEnd_1999066 := by exact prefixLift 1999066
  have htrace : WordTrace (prefixWord ++ tailWord_1999066) baseStart_1999066 baseEnd_1999066 := by
    simpa [prefixWord, tailWord_1999066, baseEnd_1999066] using wordTrace_append hprefix tailTrace_1999066
  have hstable : (prefixWord ++ tailWord_1999066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999066).length < 2 ^ (prefixWord ++ tailWord_1999066).sum := by decide
  have hdescent : baseEnd_1999066 < baseStart_1999066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999096 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_1999096 : Nat := 118140960795 + 1999096 * 2 ^ 59
def prefixEnd_1999096 : Nat := 4983230072969 + 3 ^ 40 * 1999096 * 2
def baseEnd_1999096 : Nat := 684331414987077174270887

theorem tailTrace_1999096 : CollatzResearch.WordTrace tailWord_1999096 prefixEnd_1999096 684331414987077174270887 := by
  unfold tailWord_1999096
  simp only [CollatzResearch.WordTrace]
  refine ⟨36456510582812042630100571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48608680777082723506800761 36456510582812042630100571)
  ·
    refine ⟨54684765874218063945150857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36456510582812042630100571 54684765874218063945150857)
    ·
      refine ⟨41013574405663547958863143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54684765874218063945150857 41013574405663547958863143)
      ·
        refine ⟨61520361608495321938294715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41013574405663547958863143 61520361608495321938294715)
        ·
          refine ⟨92280542412742982907442073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61520361608495321938294715 92280542412742982907442073)
          ·
            refine ⟨69210406809557237180581555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92280542412742982907442073 69210406809557237180581555)
            ·
              refine ⟨103815610214335855770872333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69210406809557237180581555 103815610214335855770872333)
              ·
                refine ⟨38930853830375945914077125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103815610214335855770872333 38930853830375945914077125)
                ·
                  refine ⟨7299535093195489858889461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38930853830375945914077125 7299535093195489858889461)
                  ·
                    refine ⟨684331414987077174270887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7299535093195489858889461 684331414987077174270887)
                    ·
                      rfl

theorem cell22_1999096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_1999096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999096 prefixEnd_1999096 := by exact prefixLift 1999096
  have htrace : WordTrace (prefixWord ++ tailWord_1999096) baseStart_1999096 baseEnd_1999096 := by
    simpa [prefixWord, tailWord_1999096, baseEnd_1999096] using wordTrace_append hprefix tailTrace_1999096
  have hstable : (prefixWord ++ tailWord_1999096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999096).length < 2 ^ (prefixWord ++ tailWord_1999096).sum := by decide
  have hdescent : baseEnd_1999096 < baseStart_1999096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999128 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_1999128 : Nat := 118140960795 + 1999128 * 2 ^ 59
def prefixEnd_1999128 : Nat := 4983230072969 + 3 ^ 40 * 1999128 * 2
def baseEnd_1999128 : Nat := 684342369241039757470789

theorem tailTrace_1999128 : CollatzResearch.WordTrace tailWord_1999128 prefixEnd_1999128 684342369241039757470789 := by
  unfold tailWord_1999128
  simp only [CollatzResearch.WordTrace]
  refine ⟨36457094150754077362683019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48609458867672103150244025 36457094150754077362683019)
  ·
    refine ⟨54685641226131116044024529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36457094150754077362683019 54685641226131116044024529)
    ·
      refine ⟨41014230919598337033018397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54685641226131116044024529 41014230919598337033018397)
      ·
        refine ⟨15380336594849376387381899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41014230919598337033018397 15380336594849376387381899)
        ·
          refine ⟨23070504892274064581072849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15380336594849376387381899 23070504892274064581072849)
          ·
            refine ⟨17302878669205548435804637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23070504892274064581072849 17302878669205548435804637)
            ·
              refine ⟨6488579500952080663426739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17302878669205548435804637 6488579500952080663426739)
              ·
                refine ⟨9732869251428120995140109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488579500952080663426739 9732869251428120995140109)
                ·
                  refine ⟨3649825969285545373177541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9732869251428120995140109 3649825969285545373177541)
                  ·
                    refine ⟨684342369241039757470789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3649825969285545373177541 684342369241039757470789)
                    ·
                      rfl

theorem cell22_1999128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_1999128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999128 prefixEnd_1999128 := by exact prefixLift 1999128
  have htrace : WordTrace (prefixWord ++ tailWord_1999128) baseStart_1999128 baseEnd_1999128 := by
    simpa [prefixWord, tailWord_1999128, baseEnd_1999128] using wordTrace_append hprefix tailTrace_1999128
  have hstable : (prefixWord ++ tailWord_1999128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999128).length < 2 ^ (prefixWord ++ tailWord_1999128).sum := by decide
  have hdescent : baseEnd_1999128 < baseStart_1999128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999175 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 2, 3]
def baseStart_1999175 : Nat := 118140960795 + 1999175 * 2 ^ 59
def prefixEnd_1999175 : Nat := 4983230072969 + 3 ^ 40 * 1999175 * 2
def baseEnd_1999175 : Nat := 684358458301547301545645

theorem tailTrace_1999175 : CollatzResearch.WordTrace tailWord_1999175 prefixEnd_1999175 684358458301547301545645 := by
  unfold tailWord_1999175
  simp only [CollatzResearch.WordTrace]
  refine ⟨72915902532337881752326979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48610601688225254501551319 72915902532337881752326979)
  ·
    refine ⟨109373853798506822628490469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72915902532337881752326979 109373853798506822628490469)
    ·
      refine ⟨20507597587220029242841963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109373853798506822628490469 20507597587220029242841963)
      ·
        refine ⟨30761396380830043864262945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20507597587220029242841963 30761396380830043864262945)
        ·
          refine ⟨23071047285622532898197209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30761396380830043864262945 23071047285622532898197209)
          ·
            refine ⟨17303285464216899673647907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23071047285622532898197209 17303285464216899673647907)
            ·
              refine ⟨25954928196325349510471861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17303285464216899673647907 25954928196325349510471861)
              ·
                refine ⟨2433274518405501516606737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25954928196325349510471861 2433274518405501516606737)
                ·
                  refine ⟨1824955888804126137455053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2433274518405501516606737 1824955888804126137455053)
                  ·
                    refine ⟨684358458301547301545645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1824955888804126137455053 684358458301547301545645)
                    ·
                      rfl

theorem cell22_1999175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_1999175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999175 prefixEnd_1999175 := by exact prefixLift 1999175
  have htrace : WordTrace (prefixWord ++ tailWord_1999175) baseStart_1999175 baseEnd_1999175 := by
    simpa [prefixWord, tailWord_1999175, baseEnd_1999175] using wordTrace_append hprefix tailTrace_1999175
  have hstable : (prefixWord ++ tailWord_1999175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999175).length < 2 ^ (prefixWord ++ tailWord_1999175).sum := by decide
  have hdescent : baseEnd_1999175 < baseStart_1999175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999196 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1999196 : Nat := 118140960795 + 1999196 * 2 ^ 59
def prefixEnd_1999196 : Nat := 4983230072969 + 3 ^ 40 * 1999196 * 2
def baseEnd_1999196 : Nat := 684365647030710246770581

theorem tailTrace_1999196 : CollatzResearch.WordTrace tailWord_1999196 prefixEnd_1999196 684365647030710246770581 := by
  unfold tailWord_1999196
  simp only [CollatzResearch.WordTrace]
  refine ⟨36458334232630901169420721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48611112310174534892560961 36458334232630901169420721)
  ·
    refine ⟨27343750674473175877065541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36458334232630901169420721 27343750674473175877065541)
    ·
      refine ⟨5126953251463720476949789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27343750674473175877065541 5126953251463720476949789)
      ·
        refine ⟨1922607469298895178856171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5126953251463720476949789 1922607469298895178856171)
        ·
          refine ⟨2883911203948342768284257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922607469298895178856171 2883911203948342768284257)
          ·
            refine ⟨2162933402961257076213193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2883911203948342768284257 2162933402961257076213193)
            ·
              refine ⟨1622200052220942807159895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162933402961257076213193 1622200052220942807159895)
              ·
                refine ⟨2433300078331414210739843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622200052220942807159895 2433300078331414210739843)
                ·
                  refine ⟨3649950117497121316109765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433300078331414210739843 3649950117497121316109765)
                  ·
                    refine ⟨684365647030710246770581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3649950117497121316109765 684365647030710246770581)
                    ·
                      rfl

theorem cell22_1999196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1999196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999196 prefixEnd_1999196 := by exact prefixLift 1999196
  have htrace : WordTrace (prefixWord ++ tailWord_1999196) baseStart_1999196 baseEnd_1999196 := by
    simpa [prefixWord, tailWord_1999196, baseEnd_1999196] using wordTrace_append hprefix tailTrace_1999196
  have hstable : (prefixWord ++ tailWord_1999196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999196).length < 2 ^ (prefixWord ++ tailWord_1999196).sum := by decide
  have hdescent : baseEnd_1999196 < baseStart_1999196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999271 : List Nat := [1, 1, 6, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1999271 : Nat := 118140960795 + 1999271 * 2 ^ 59
def prefixEnd_1999271 : Nat := 4983230072969 + 3 ^ 40 * 1999271 * 2
def baseEnd_1999271 : Nat := 684391321063435051145351

theorem tailTrace_1999271 : CollatzResearch.WordTrace tailWord_1999271 prefixEnd_1999271 684391321063435051145351 := by
  unfold tailWord_1999271
  simp only [CollatzResearch.WordTrace]
  refine ⟨72919403939990090147821667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48612935959993393431881111 72919403939990090147821667)
  ·
    refine ⟨109379105909985135221732501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72919403939990090147821667 109379105909985135221732501)
    ·
      refine ⟨5127145589530553213518711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109379105909985135221732501 5127145589530553213518711)
      ·
        refine ⟨7690718384295829820278067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5127145589530553213518711 7690718384295829820278067)
        ·
          refine ⟨11536077576443744730417101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690718384295829820278067 11536077576443744730417101)
          ·
            refine ⟨4326029091166404273906413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11536077576443744730417101 4326029091166404273906413)
            ·
              refine ⟨1622260909187401602714905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4326029091166404273906413 1622260909187401602714905)
              ·
                refine ⟨1216695681890551202036179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622260909187401602714905 1216695681890551202036179)
                ·
                  refine ⟨1825043522835826803054269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216695681890551202036179 1825043522835826803054269)
                  ·
                    refine ⟨684391321063435051145351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825043522835826803054269 684391321063435051145351)
                    ·
                      rfl

theorem cell22_1999271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1999271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999271 prefixEnd_1999271 := by exact prefixLift 1999271
  have htrace : WordTrace (prefixWord ++ tailWord_1999271) baseStart_1999271 baseEnd_1999271 := by
    simpa [prefixWord, tailWord_1999271, baseEnd_1999271] using wordTrace_append hprefix tailTrace_1999271
  have hstable : (prefixWord ++ tailWord_1999271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999271).length < 2 ^ (prefixWord ++ tailWord_1999271).sum := by decide
  have hdescent : baseEnd_1999271 < baseStart_1999271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999327 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 2, 3]
def baseStart_1999327 : Nat := 118140960795 + 1999327 * 2 ^ 59
def prefixEnd_1999327 : Nat := 4983230072969 + 3 ^ 40 * 1999327 * 2
def baseEnd_1999327 : Nat := 684410491007869571745179

theorem tailTrace_1999327 : CollatzResearch.WordTrace tailWord_1999327 prefixEnd_1999327 684410491007869571745179 := by
  unfold tailWord_1999327
  simp only [CollatzResearch.WordTrace]
  refine ⟨72921446427787211711860235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48614297618524807807906823 72921446427787211711860235)
  ·
    refine ⟨109382169641680817567790353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72921446427787211711860235 109382169641680817567790353)
    ·
      refine ⟨82036627231260613175842765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109382169641680817567790353 82036627231260613175842765)
      ·
        refine ⟨30763735211722729940941037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82036627231260613175842765 30763735211722729940941037)
        ·
          refine ⟨11536400704396023727852889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30763735211722729940941037 11536400704396023727852889)
          ·
            refine ⟨8652300528297017795889667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11536400704396023727852889 8652300528297017795889667)
            ·
              refine ⟨12978450792445526693834501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652300528297017795889667 12978450792445526693834501)
              ·
                refine ⟨2433459523583536255093969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12978450792445526693834501 2433459523583536255093969)
                ·
                  refine ⟨1825094642687652191320477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2433459523583536255093969 1825094642687652191320477)
                  ·
                    refine ⟨684410491007869571745179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825094642687652191320477 684410491007869571745179)
                    ·
                      rfl

theorem cell22_1999327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_1999327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999327 prefixEnd_1999327 := by exact prefixLift 1999327
  have htrace : WordTrace (prefixWord ++ tailWord_1999327) baseStart_1999327 baseEnd_1999327 := by
    simpa [prefixWord, tailWord_1999327, baseEnd_1999327] using wordTrace_append hprefix tailTrace_1999327
  have hstable : (prefixWord ++ tailWord_1999327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999327).length < 2 ^ (prefixWord ++ tailWord_1999327).sum := by decide
  have hdescent : baseEnd_1999327 < baseStart_1999327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999389 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1999389 : Nat := 118140960795 + 1999389 * 2 ^ 59
def prefixEnd_1999389 : Nat := 4983230072969 + 3 ^ 40 * 1999389 * 2
def baseEnd_1999389 : Nat := 684431714874922076694989

theorem tailTrace_1999389 : CollatzResearch.WordTrace tailWord_1999389 prefixEnd_1999389 684431714874922076694989 := by
  unfold tailWord_1999389
  simp only [CollatzResearch.WordTrace]
  refine ⟨72923707753562596300617221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48615805169041730867078147 72923707753562596300617221)
  ·
    refine ⟨13673195203792986806365729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72923707753562596300617221 13673195203792986806365729)
    ·
      refine ⟨10254896402844740104774297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13673195203792986806365729 10254896402844740104774297)
      ·
        refine ⟨7691172302133555078580723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10254896402844740104774297 7691172302133555078580723)
        ·
          refine ⟨11536758453200332617871085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7691172302133555078580723 11536758453200332617871085)
          ·
            refine ⟨4326284419950124731701657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11536758453200332617871085 4326284419950124731701657)
            ·
              refine ⟨3244713314962593548776243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4326284419950124731701657 3244713314962593548776243)
              ·
                refine ⟨4867069972443890323164365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3244713314962593548776243 4867069972443890323164365)
                ·
                  refine ⟨1825151239666458871186637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4867069972443890323164365 1825151239666458871186637)
                  ·
                    refine ⟨684431714874922076694989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825151239666458871186637 684431714874922076694989)
                    ·
                      rfl

theorem cell22_1999389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1999389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999389 prefixEnd_1999389 := by exact prefixLift 1999389
  have htrace : WordTrace (prefixWord ++ tailWord_1999389) baseStart_1999389 baseEnd_1999389 := by
    simpa [prefixWord, tailWord_1999389, baseEnd_1999389] using wordTrace_append hprefix tailTrace_1999389
  have hstable : (prefixWord ++ tailWord_1999389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999389).length < 2 ^ (prefixWord ++ tailWord_1999389).sum := by decide
  have hdescent : baseEnd_1999389 < baseStart_1999389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999498 : List Nat := [3, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_1999498 : Nat := 118140960795 + 1999498 * 2 ^ 59
def prefixEnd_1999498 : Nat := 4983230072969 + 3 ^ 40 * 1999498 * 2
def baseEnd_1999498 : Nat := 228156342600827375239885

theorem tailTrace_1999498 : CollatzResearch.WordTrace tailWord_1999498 prefixEnd_1999498 228156342600827375239885 := by
  unfold tailWord_1999498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18231920827541926979083787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48618455540111805277556765 18231920827541926979083787)
  ·
    refine ⟨27347881241312890468625681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18231920827541926979083787 27347881241312890468625681)
    ·
      refine ⟨20510910930984667851469261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27347881241312890468625681 20510910930984667851469261)
      ·
        refine ⟨7691591599119250444300973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20510910930984667851469261 7691591599119250444300973)
        ·
          refine ⟨2884346849669718916612865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7691591599119250444300973 2884346849669718916612865)
          ·
            refine ⟨2163260137252289187459649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2884346849669718916612865 2163260137252289187459649)
            ·
              refine ⟨1622445102939216890594737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163260137252289187459649 1622445102939216890594737)
              ·
                refine ⟨1216833827204412667946053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622445102939216890594737 1216833827204412667946053)
                ·
                  refine ⟨228156342600827375239885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216833827204412667946053 228156342600827375239885)
                  ·
                    rfl

theorem cell22_1999498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_1999498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999498 prefixEnd_1999498 := by exact prefixLift 1999498
  have htrace : WordTrace (prefixWord ++ tailWord_1999498) baseStart_1999498 baseEnd_1999498 := by
    simpa [prefixWord, tailWord_1999498, baseEnd_1999498] using wordTrace_append hprefix tailTrace_1999498
  have hstable : (prefixWord ++ tailWord_1999498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999498).length < 2 ^ (prefixWord ++ tailWord_1999498).sum := by decide
  have hdescent : baseEnd_1999498 < baseStart_1999498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999524 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1999524 : Nat := 118140960795 + 1999524 * 2 ^ 59
def prefixEnd_1999524 : Nat := 4983230072969 + 3 ^ 40 * 1999524 * 2
def baseEnd_1999524 : Nat := 684477928133826724569575

theorem tailTrace_1999524 : CollatzResearch.WordTrace tailWord_1999524 prefixEnd_1999524 684477928133826724569575 := by
  unfold tailWord_1999524
  simp only [CollatzResearch.WordTrace]
  refine ⟨36464315804036757178390813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48619087738715676237854417 36464315804036757178390813)
  ·
    refine ⟨13674118426513783941896555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36464315804036757178390813 13674118426513783941896555)
    ·
      refine ⟨20511177639770675912844833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13674118426513783941896555 20511177639770675912844833)
      ·
        refine ⟨15383383229828006934633625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20511177639770675912844833 15383383229828006934633625)
        ·
          refine ⟨11537537422371005200975219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15383383229828006934633625 11537537422371005200975219)
          ·
            refine ⟨17306306133556507801462829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537537422371005200975219 17306306133556507801462829)
            ·
              refine ⟨6489864800083690425548561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17306306133556507801462829 6489864800083690425548561)
              ·
                refine ⟨4867398600062767819161421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6489864800083690425548561 4867398600062767819161421)
                ·
                  refine ⟨1825274475023537932185533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4867398600062767819161421 1825274475023537932185533)
                  ·
                    refine ⟨684477928133826724569575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825274475023537932185533 684477928133826724569575)
                    ·
                      rfl

theorem cell22_1999524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1999524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999524 prefixEnd_1999524 := by exact prefixLift 1999524
  have htrace : WordTrace (prefixWord ++ tailWord_1999524) baseStart_1999524 baseEnd_1999524 := by
    simpa [prefixWord, tailWord_1999524, baseEnd_1999524] using wordTrace_append hprefix tailTrace_1999524
  have hstable : (prefixWord ++ tailWord_1999524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999524).length < 2 ^ (prefixWord ++ tailWord_1999524).sum := by decide
  have hdescent : baseEnd_1999524 < baseStart_1999524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999552 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_1999552 : Nat := 118140960795 + 1999552 * 2 ^ 59
def prefixEnd_1999552 : Nat := 4983230072969 + 3 ^ 40 * 1999552 * 2
def baseEnd_1999552 : Nat := 684487513106043984869489

theorem tailTrace_1999552 : CollatzResearch.WordTrace tailWord_1999552 prefixEnd_1999552 684487513106043984869489 := by
  unfold tailWord_1999552
  simp only [CollatzResearch.WordTrace]
  refine ⟨36464826425986037569400455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48619768567981383425867273 36464826425986037569400455)
  ·
    refine ⟨54697239638979056354100683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36464826425986037569400455 54697239638979056354100683)
    ·
      refine ⟨82045859458468584531151025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54697239638979056354100683 82045859458468584531151025)
      ·
        refine ⟨61534394593851438398363269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82045859458468584531151025 61534394593851438398363269)
        ·
          refine ⟨11537698986347144699693113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61534394593851438398363269 11537698986347144699693113)
          ·
            refine ⟨8653274239760358524769835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11537698986347144699693113 8653274239760358524769835)
            ·
              refine ⟨12979911359640537787154753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8653274239760358524769835 12979911359640537787154753)
              ·
                refine ⟨9734933519730403340366065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12979911359640537787154753 9734933519730403340366065)
                ·
                  refine ⟨7301200139797802505274549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9734933519730403340366065 7301200139797802505274549)
                  ·
                    refine ⟨684487513106043984869489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7301200139797802505274549 684487513106043984869489)
                    ·
                      rfl

theorem cell22_1999552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_1999552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999552 prefixEnd_1999552 := by exact prefixLift 1999552
  have htrace : WordTrace (prefixWord ++ tailWord_1999552) baseStart_1999552 baseEnd_1999552 := by
    simpa [prefixWord, tailWord_1999552, baseEnd_1999552] using wordTrace_append hprefix tailTrace_1999552
  have hstable : (prefixWord ++ tailWord_1999552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999552).length < 2 ^ (prefixWord ++ tailWord_1999552).sum := by decide
  have hdescent : baseEnd_1999552 < baseStart_1999552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999661 : List Nat := [1, 5, 3, 2, 1, 10]
def baseStart_1999661 : Nat := 118140960795 + 1999661 * 2 ^ 59
def prefixEnd_1999661 : Nat := 4983230072969 + 3 ^ 40 * 1999661 * 2
def baseEnd_1999661 : Nat := 8450923778192642393755

theorem tailTrace_1999661 : CollatzResearch.WordTrace tailWord_1999661 prefixEnd_1999661 8450923778192642393755 := by
  unfold tailWord_1999661
  simp only [CollatzResearch.WordTrace]
  refine ⟨72933628408577186754518837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48622418939051457836345891 72933628408577186754518837)
  ·
    refine ⟨6837527663304111258236141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72933628408577186754518837 6837527663304111258236141)
    ·
      refine ⟨2564072873739041721838553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6837527663304111258236141 2564072873739041721838553)
      ·
        refine ⟨1923054655304281291378915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2564072873739041721838553 1923054655304281291378915)
        ·
          refine ⟨2884581982956421937068373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923054655304281291378915 2884581982956421937068373)
          ·
            refine ⟨8450923778192642393755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2884581982956421937068373 8450923778192642393755)
            ·
              rfl

theorem cell22_1999661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 10].length) (baseStart_1999661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999661 prefixEnd_1999661 := by exact prefixLift 1999661
  have htrace : WordTrace (prefixWord ++ tailWord_1999661) baseStart_1999661 baseEnd_1999661 := by
    simpa [prefixWord, tailWord_1999661, baseEnd_1999661] using wordTrace_append hprefix tailTrace_1999661
  have hstable : (prefixWord ++ tailWord_1999661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999661).length < 2 ^ (prefixWord ++ tailWord_1999661).sum := by decide
  have hdescent : baseEnd_1999661 < baseStart_1999661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999678 : List Nat := [4, 2, 1, 2, 4, 1, 1, 7]
def baseStart_1999678 : Nat := 118140960795 + 1999678 * 2 ^ 59
def prefixEnd_1999678 : Nat := 4983230072969 + 3 ^ 40 * 1999678 * 2
def baseEnd_1999678 : Nat := 76058960609002406246567

theorem tailTrace_1999678 : CollatzResearch.WordTrace tailWord_1999678 prefixEnd_1999678 76058960609002406246567 := by
  unfold tailWord_1999678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9116781056189449832235961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48622832299677065771925125 9116781056189449832235961)
  ·
    refine ⟨6837585792142087374176971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9116781056189449832235961 6837585792142087374176971)
    ·
      refine ⟨10256378688213131061265457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6837585792142087374176971 10256378688213131061265457)
      ·
        refine ⟨7692284016159848295949093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10256378688213131061265457 7692284016159848295949093)
        ·
          refine ⟨1442303253029971555490455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7692284016159848295949093 1442303253029971555490455)
          ·
            refine ⟨2163454879544957333235683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442303253029971555490455 2163454879544957333235683)
            ·
              refine ⟨3245182319317435999853525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163454879544957333235683 3245182319317435999853525)
              ·
                refine ⟨76058960609002406246567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3245182319317435999853525 76058960609002406246567)
                ·
                  rfl

theorem cell22_1999678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_1999678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999678 prefixEnd_1999678 := by exact prefixLift 1999678
  have htrace : WordTrace (prefixWord ++ tailWord_1999678) baseStart_1999678 baseEnd_1999678 := by
    simpa [prefixWord, tailWord_1999678, baseEnd_1999678] using wordTrace_append hprefix tailTrace_1999678
  have hstable : (prefixWord ++ tailWord_1999678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999678).length < 2 ^ (prefixWord ++ tailWord_1999678).sum := by decide
  have hdescent : baseEnd_1999678 < baseStart_1999678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999689 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 5]
def baseStart_1999689 : Nat := 118140960795 + 1999689 * 2 ^ 59
def prefixEnd_1999689 : Nat := 4983230072969 + 3 ^ 40 * 1999689 * 2
def baseEnd_1999689 : Nat := 228178137001940431398023

theorem tailTrace_1999689 : CollatzResearch.WordTrace tailWord_1999689 prefixEnd_1999689 228178137001940431398023 := by
  unfold tailWord_1999689
  simp only [CollatzResearch.WordTrace]
  refine ⟨72934649652475747536538121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48623099768317165024358747 72934649652475747536538121)
  ·
    refine ⟨54700987239356810652403591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72934649652475747536538121 54700987239356810652403591)
    ·
      refine ⟨82051480859035215978605387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54700987239356810652403591 82051480859035215978605387)
      ·
        refine ⟨123077221288552823967908081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82051480859035215978605387 123077221288552823967908081)
        ·
          refine ⟨92307915966414617975931061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123077221288552823967908081 92307915966414617975931061)
          ·
            refine ⟨8653867121851370435243537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92307915966414617975931061 8653867121851370435243537)
            ·
              refine ⟨6490400341388527826432653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8653867121851370435243537 6490400341388527826432653)
              ·
                refine ⟨2433900128020697934912245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6490400341388527826432653 2433900128020697934912245)
                ·
                  refine ⟨228178137001940431398023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2433900128020697934912245 228178137001940431398023)
                  ·
                    rfl

theorem cell22_1999689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_1999689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999689 prefixEnd_1999689 := by exact prefixLift 1999689
  have htrace : WordTrace (prefixWord ++ tailWord_1999689) baseStart_1999689 baseEnd_1999689 := by
    simpa [prefixWord, tailWord_1999689, baseEnd_1999689] using wordTrace_append hprefix tailTrace_1999689
  have hstable : (prefixWord ++ tailWord_1999689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999689).length < 2 ^ (prefixWord ++ tailWord_1999689).sum := by decide
  have hdescent : baseEnd_1999689 < baseStart_1999689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999800 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 2, 3]
def baseStart_1999800 : Nat := 118140960795 + 1999800 * 2 ^ 59
def prefixEnd_1999800 : Nat := 4983230072969 + 3 ^ 40 * 1999800 * 2
def baseEnd_1999800 : Nat := 684572408574254004668729

theorem tailTrace_1999800 : CollatzResearch.WordTrace tailWord_1999800 prefixEnd_1999800 684572408574254004668729 := by
  unfold tailWord_1999800
  simp only [CollatzResearch.WordTrace]
  refine ⟨36469349077536806746914427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48625798770049075662552569 36469349077536806746914427)
  ·
    refine ⟨54704023616305210120371641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36469349077536806746914427 54704023616305210120371641)
    ·
      refine ⟨41028017712228907590278731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54704023616305210120371641 41028017712228907590278731)
      ·
        refine ⟨61542026568343361385418097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41028017712228907590278731 61542026568343361385418097)
        ·
          refine ⟨46156519926257521039063573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61542026568343361385418097 46156519926257521039063573)
          ·
            refine ⟨2163586871543321298706105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46156519926257521039063573 2163586871543321298706105)
            ·
              refine ⟨1622690153657490974029579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163586871543321298706105 1622690153657490974029579)
              ·
                refine ⟨2434035230486236461044369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622690153657490974029579 2434035230486236461044369)
                ·
                  refine ⟨1825526422864677345783277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2434035230486236461044369 1825526422864677345783277)
                  ·
                    refine ⟨684572408574254004668729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825526422864677345783277 684572408574254004668729)
                    ·
                      rfl

theorem cell22_1999800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_1999800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999800 prefixEnd_1999800 := by exact prefixLift 1999800
  have htrace : WordTrace (prefixWord ++ tailWord_1999800) baseStart_1999800 baseEnd_1999800 := by
    simpa [prefixWord, tailWord_1999800, baseEnd_1999800] using wordTrace_append hprefix tailTrace_1999800
  have hstable : (prefixWord ++ tailWord_1999800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999800).length < 2 ^ (prefixWord ++ tailWord_1999800).sum := by decide
  have hdescent : baseEnd_1999800 < baseStart_1999800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999903 : List Nat := [1, 1, 2, 4, 1, 3, 2, 4, 4]
def baseStart_1999903 : Nat := 118140960795 + 1999903 * 2 ^ 59
def prefixEnd_1999903 : Nat := 4983230072969 + 3 ^ 40 * 1999903 * 2
def baseEnd_1999903 : Nat := 228202555859732023114471

theorem tailTrace_1999903 : CollatzResearch.WordTrace tailWord_1999903 prefixEnd_1999903 228202555859732023114471 := by
  unfold tailWord_1999903
  simp only [CollatzResearch.WordTrace]
  refine ⟨72942454873700462084828363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48628303249133641389885575 72942454873700462084828363)
  ·
    refine ⟨109413682310550693127242545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72942454873700462084828363 109413682310550693127242545)
    ·
      refine ⟨82060261732913019845431909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109413682310550693127242545 82060261732913019845431909)
      ·
        refine ⟨15386299074921191221018483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82060261732913019845431909 15386299074921191221018483)
        ·
          refine ⟨23079448612381786831527725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15386299074921191221018483 23079448612381786831527725)
          ·
            refine ⟨8654793229643170061822897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23079448612381786831527725 8654793229643170061822897)
            ·
              refine ⟨6491094922232377546367173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8654793229643170061822897 6491094922232377546367173)
              ·
                refine ⟨1217080297918570789943845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6491094922232377546367173 1217080297918570789943845)
                ·
                  refine ⟨228202555859732023114471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217080297918570789943845 228202555859732023114471)
                  ·
                    rfl

theorem cell22_1999903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 4].length) (baseStart_1999903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999903 prefixEnd_1999903 := by exact prefixLift 1999903
  have htrace : WordTrace (prefixWord ++ tailWord_1999903) baseStart_1999903 baseEnd_1999903 := by
    simpa [prefixWord, tailWord_1999903, baseEnd_1999903] using wordTrace_append hprefix tailTrace_1999903
  have hstable : (prefixWord ++ tailWord_1999903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999903).length < 2 ^ (prefixWord ++ tailWord_1999903).sum := by decide
  have hdescent : baseEnd_1999903 < baseStart_1999903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999937 : List Nat := [1, 2, 5, 1, 3, 2, 1, 3, 4]
def baseStart_1999937 : Nat := 118140960795 + 1999937 * 2 ^ 59
def prefixEnd_1999937 : Nat := 4983230072969 + 3 ^ 40 * 1999937 * 2
def baseEnd_1999937 : Nat := 228206435491343771331103

theorem tailTrace_1999937 : CollatzResearch.WordTrace tailWord_1999937 prefixEnd_1999937 228206435491343771331103 := by
  unfold tailWord_1999937
  simp only [CollatzResearch.WordTrace]
  refine ⟨72943694955577285891566065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48629129970384857261044043 72943694955577285891566065)
  ·
    refine ⟨54707771216682964418674549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72943694955577285891566065 54707771216682964418674549)
    ·
      refine ⟨5128853551564027914250739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54707771216682964418674549 5128853551564027914250739)
      ·
        refine ⟨7693280327346041871376109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128853551564027914250739 7693280327346041871376109)
        ·
          refine ⟨2884980122754765701766041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7693280327346041871376109 2884980122754765701766041)
          ·
            refine ⟨2163735092066074276324531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2884980122754765701766041 2163735092066074276324531)
            ·
              refine ⟨3245602638099111414486797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163735092066074276324531 3245602638099111414486797)
              ·
                refine ⟨1217100989287166780432549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3245602638099111414486797 1217100989287166780432549)
                ·
                  refine ⟨228206435491343771331103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217100989287166780432549 228206435491343771331103)
                  ·
                    rfl

theorem cell22_1999937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 4].length) (baseStart_1999937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999937 prefixEnd_1999937 := by exact prefixLift 1999937
  have htrace : WordTrace (prefixWord ++ tailWord_1999937) baseStart_1999937 baseEnd_1999937 := by
    simpa [prefixWord, tailWord_1999937, baseEnd_1999937] using wordTrace_append hprefix tailTrace_1999937
  have hstable : (prefixWord ++ tailWord_1999937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999937).length < 2 ^ (prefixWord ++ tailWord_1999937).sum := by decide
  have hdescent : baseEnd_1999937 < baseStart_1999937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999965 : List Nat := [1, 4, 4, 1, 2, 1, 2, 7]
def baseStart_1999965 : Nat := 118140960795 + 1999965 * 2 ^ 59
def prefixEnd_1999965 : Nat := 4983230072969 + 3 ^ 40 * 1999965 * 2
def baseEnd_1999965 : Nat := 76069876827360952699247

theorem tailTrace_1999965 : CollatzResearch.WordTrace tailWord_1999965 prefixEnd_1999965 76069876827360952699247 := by
  unfold tailWord_1999965
  simp only [CollatzResearch.WordTrace]
  refine ⟨72944716199475846673585349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48629810799650564449056899 72944716199475846673585349)
  ·
    refine ⟨13677134287401721251297253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72944716199475846673585349 13677134287401721251297253)
    ·
      refine ⟨2564462678887822734618235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13677134287401721251297253 2564462678887822734618235)
      ·
        refine ⟨3846694018331734101927353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564462678887822734618235 3846694018331734101927353)
        ·
          refine ⟨2885020513748800576445515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3846694018331734101927353 2885020513748800576445515)
          ·
            refine ⟨4327530770623200864668273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885020513748800576445515 4327530770623200864668273)
            ·
              refine ⟨3245648077967400648501205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4327530770623200864668273 3245648077967400648501205)
              ·
                refine ⟨76069876827360952699247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3245648077967400648501205 76069876827360952699247)
                ·
                  rfl

theorem cell22_1999965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 7].length) (baseStart_1999965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1999965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1999965 prefixEnd_1999965 := by exact prefixLift 1999965
  have htrace : WordTrace (prefixWord ++ tailWord_1999965) baseStart_1999965 baseEnd_1999965 := by
    simpa [prefixWord, tailWord_1999965, baseEnd_1999965] using wordTrace_append hprefix tailTrace_1999965
  have hstable : (prefixWord ++ tailWord_1999965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999965).length < 2 ^ (prefixWord ++ tailWord_1999965).sum := by decide
  have hdescent : baseEnd_1999965 < baseStart_1999965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000014 : List Nat := [4, 1, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2000014 : Nat := 118140960795 + 2000014 * 2 ^ 59
def prefixEnd_2000014 : Nat := 4983230072969 + 3 ^ 40 * 2000014 * 2
def baseEnd_2000014 : Nat := 684645665147628779818073

theorem tailTrace_2000014 : CollatzResearch.WordTrace tailWord_2000014 prefixEnd_2000014 684645665147628779818073 := by
  unfold tailWord_2000014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9118312922037291005264887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48631002250865552028079397 9118312922037291005264887)
  ·
    refine ⟨13677469383055936507897331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9118312922037291005264887 13677469383055936507897331)
    ·
      refine ⟨20516204074583904761845997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13677469383055936507897331 20516204074583904761845997)
      ·
        refine ⟨7693576527968964285692249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20516204074583904761845997 7693576527968964285692249)
        ·
          refine ⟨5770182395976723214269187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7693576527968964285692249 5770182395976723214269187)
          ·
            refine ⟨8655273593965084821403781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5770182395976723214269187 8655273593965084821403781)
            ·
              refine ⟨1622863798868453404013209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8655273593965084821403781 1622863798868453404013209)
              ·
                refine ⟨1217147849151340053009907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622863798868453404013209 1217147849151340053009907)
                ·
                  refine ⟨1825721773727010079514861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217147849151340053009907 1825721773727010079514861)
                  ·
                    refine ⟨684645665147628779818073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825721773727010079514861 684645665147628779818073)
                    ·
                      rfl

theorem cell22_2000014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2000014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000014 prefixEnd_2000014 := by exact prefixLift 2000014
  have htrace : WordTrace (prefixWord ++ tailWord_2000014) baseStart_2000014 baseEnd_2000014 := by
    simpa [prefixWord, tailWord_2000014, baseEnd_2000014] using wordTrace_append hprefix tailTrace_2000014
  have hstable : (prefixWord ++ tailWord_2000014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000014).length < 2 ^ (prefixWord ++ tailWord_2000014).sum := by decide
  have hdescent : baseEnd_2000014 < baseStart_2000014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000023 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2000023 : Nat := 118140960795 + 2000023 * 2 ^ 59
def prefixEnd_2000023 : Nat := 4983230072969 + 3 ^ 40 * 2000023 * 2
def baseEnd_2000023 : Nat := 684648746031555756343045

theorem tailTrace_2000023 : CollatzResearch.WordTrace tailWord_2000023 prefixEnd_2000023 684648746031555756343045 := by
  unfold tailWord_2000023
  simp only [CollatzResearch.WordTrace]
  refine ⟨72946831633265722579196723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48631221088843815052797815 72946831633265722579196723)
  ·
    refine ⟨109420247449898583868795085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72946831633265722579196723 109420247449898583868795085)
    ·
      refine ⟨41032592793711968950798157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109420247449898583868795085 41032592793711968950798157)
      ·
        refine ⟨15387222297641988356549309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41032592793711968950798157 15387222297641988356549309)
        ·
          refine ⟨5770208361615745633705991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15387222297641988356549309 5770208361615745633705991)
          ·
            refine ⟨8655312542423618450558987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5770208361615745633705991 8655312542423618450558987)
            ·
              refine ⟨12982968813635427675838481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8655312542423618450558987 12982968813635427675838481)
              ·
                refine ⟨9737226610226570756878861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12982968813635427675838481 9737226610226570756878861)
                ·
                  refine ⟨3651459978834964033829573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9737226610226570756878861 3651459978834964033829573)
                  ·
                    refine ⟨684648746031555756343045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3651459978834964033829573 684648746031555756343045)
                    ·
                      rfl

theorem cell22_2000023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2000023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000023 prefixEnd_2000023 := by exact prefixLift 2000023
  have htrace : WordTrace (prefixWord ++ tailWord_2000023) baseStart_2000023 baseEnd_2000023 := by
    simpa [prefixWord, tailWord_2000023, baseEnd_2000023] using wordTrace_append hprefix tailTrace_2000023
  have hstable : (prefixWord ++ tailWord_2000023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000023).length < 2 ^ (prefixWord ++ tailWord_2000023).sum := by decide
  have hdescent : baseEnd_2000023 < baseStart_2000023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000055 : List Nat := [1, 1, 3, 1, 4, 1, 4, 3, 4]
def baseStart_2000055 : Nat := 118140960795 + 2000055 * 2 ^ 59
def prefixEnd_2000055 : Nat := 4983230072969 + 3 ^ 40 * 2000055 * 2
def baseEnd_2000055 : Nat := 228219900095172779847649

theorem tailTrace_2000055 : CollatzResearch.WordTrace tailWord_2000055 prefixEnd_2000055 228219900095172779847649 := by
  unfold tailWord_2000055
  simp only [CollatzResearch.WordTrace]
  refine ⟨72947998769149792044361619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48631999179433194696241079 72947998769149792044361619)
  ·
    refine ⟨109421998153724688066542429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72947998769149792044361619 109421998153724688066542429)
    ·
      refine ⟨41033249307646758024953411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109421998153724688066542429 41033249307646758024953411)
      ·
        refine ⟨61549873961470137037430117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41033249307646758024953411 61549873961470137037430117)
        ·
          refine ⟨11540601367775650694518147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61549873961470137037430117 11540601367775650694518147)
          ·
            refine ⟨17310902051663476041777221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11540601367775650694518147 17310902051663476041777221)
            ·
              refine ⟨3245794134686901757833229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17310902051663476041777221 3245794134686901757833229)
              ·
                refine ⟨1217172800507588159187461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3245794134686901757833229 1217172800507588159187461)
                ·
                  refine ⟨228219900095172779847649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217172800507588159187461 228219900095172779847649)
                  ·
                    rfl

theorem cell22_2000055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 4].length) (baseStart_2000055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000055 prefixEnd_2000055 := by exact prefixLift 2000055
  have htrace : WordTrace (prefixWord ++ tailWord_2000055) baseStart_2000055 baseEnd_2000055 := by
    simpa [prefixWord, tailWord_2000055, baseEnd_2000055] using wordTrace_append hprefix tailTrace_2000055
  have hstable : (prefixWord ++ tailWord_2000055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000055).length < 2 ^ (prefixWord ++ tailWord_2000055).sum := by decide
  have hdescent : baseEnd_2000055 < baseStart_2000055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000057 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 1, 4]
def baseStart_2000057 : Nat := 118140960795 + 2000057 * 2 ^ 59
def prefixEnd_2000057 : Nat := 4983230072969 + 3 ^ 40 * 2000057 * 2
def baseEnd_2000057 : Nat := 684660384926391000992941

theorem tailTrace_2000057 : CollatzResearch.WordTrace tailWord_2000057 prefixEnd_2000057 684660384926391000992941 := by
  unfold tailWord_2000057
  simp only [CollatzResearch.WordTrace]
  refine ⟨72948071715142546385934425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48632047810095030923956283 72948071715142546385934425)
  ·
    refine ⟨54711053786356909789450819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72948071715142546385934425 54711053786356909789450819)
    ·
      refine ⟨82066580679535364684176229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54711053786356909789450819 82066580679535364684176229)
      ·
        refine ⟨15387483877412880878283043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82066580679535364684176229 15387483877412880878283043)
        ·
          refine ⟨23081225816119321317424565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15387483877412880878283043 23081225816119321317424565)
          ·
            refine ⟨2163864920261186373508553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23081225816119321317424565 2163864920261186373508553)
            ·
              refine ⟨1622898690195889780131415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163864920261186373508553 1622898690195889780131415)
              ·
                refine ⟨2434348035293834670197123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622898690195889780131415 2434348035293834670197123)
                ·
                  refine ⟨3651522052940752005295685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434348035293834670197123 3651522052940752005295685)
                  ·
                    refine ⟨684660384926391000992941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3651522052940752005295685 684660384926391000992941)
                    ·
                      rfl

theorem cell22_2000057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 4].length) (baseStart_2000057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000057 prefixEnd_2000057 := by exact prefixLift 2000057
  have htrace : WordTrace (prefixWord ++ tailWord_2000057) baseStart_2000057 baseEnd_2000057 := by
    simpa [prefixWord, tailWord_2000057, baseEnd_2000057] using wordTrace_append hprefix tailTrace_2000057
  have hstable : (prefixWord ++ tailWord_2000057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000057).length < 2 ^ (prefixWord ++ tailWord_2000057).sum := by decide
  have hdescent : baseEnd_2000057 < baseStart_2000057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000128 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 5]
def baseStart_2000128 : Nat := 118140960795 + 2000128 * 2 ^ 59
def prefixEnd_2000128 : Nat := 4983230072969 + 3 ^ 40 * 2000128 * 2
def baseEnd_2000128 : Nat := 228228229892456827489241

theorem tailTrace_2000128 : CollatzResearch.WordTrace tailWord_2000128 prefixEnd_2000128 228228229892456827489241 := by
  unfold tailWord_2000128
  simp only [CollatzResearch.WordTrace]
  refine ⟨36475330648942662755884519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48633774198590217007846025 36475330648942662755884519)
  ·
    refine ⟨54712995973413994133826779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36475330648942662755884519 54712995973413994133826779)
    ·
      refine ⟨82069493960120991200740169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54712995973413994133826779 82069493960120991200740169)
      ·
        refine ⟨61552120470090743400555127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82069493960120991200740169 61552120470090743400555127)
        ·
          refine ⟨92328180705136115100832691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61552120470090743400555127 92328180705136115100832691)
          ·
            refine ⟨138492271057704172651249037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92328180705136115100832691 138492271057704172651249037)
            ·
              refine ⟨51934601646639064744218389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138492271057704172651249037 51934601646639064744218389)
              ·
                refine ⟨2434434452186206159885237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51934601646639064744218389 2434434452186206159885237)
                ·
                  refine ⟨228228229892456827489241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2434434452186206159885237 228228229892456827489241)
                  ·
                    rfl

theorem cell22_2000128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_2000128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000128 prefixEnd_2000128 := by exact prefixLift 2000128
  have htrace : WordTrace (prefixWord ++ tailWord_2000128) baseStart_2000128 baseEnd_2000128 := by
    simpa [prefixWord, tailWord_2000128, baseEnd_2000128] using wordTrace_append hprefix tailTrace_2000128
  have hstable : (prefixWord ++ tailWord_2000128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000128).length < 2 ^ (prefixWord ++ tailWord_2000128).sum := by decide
  have hdescent : baseEnd_2000128 < baseStart_2000128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000132 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_2000132 : Nat := 118140960795 + 2000132 * 2 ^ 59
def prefixEnd_2000132 : Nat := 4983230072969 + 3 ^ 40 * 2000132 * 2
def baseEnd_2000132 : Nat := 684686058959115805367711

theorem tailTrace_2000132 : CollatzResearch.WordTrace tailWord_2000132 prefixEnd_2000132 684686058959115805367711 := by
  unfold tailWord_2000132
  simp only [CollatzResearch.WordTrace]
  refine ⟨36475403594935417097457325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48633871459913889463276433 36475403594935417097457325)
  ·
    refine ⟨13678276348100781411546497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36475403594935417097457325 13678276348100781411546497)
    ·
      refine ⟨10258707261075586058659873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13678276348100781411546497 10258707261075586058659873)
      ·
        refine ⟨7694030445806689543994905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10258707261075586058659873 7694030445806689543994905)
        ·
          refine ⟨5770522834355017157996179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7694030445806689543994905 5770522834355017157996179)
          ·
            refine ⟨8655784251532525736994269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5770522834355017157996179 8655784251532525736994269)
            ·
              refine ⟨3245919094324697151372851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8655784251532525736994269 3245919094324697151372851)
              ·
                refine ⟨4868878641487045727059277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245919094324697151372851 4868878641487045727059277)
                ·
                  refine ⟨1825829490557642147647229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4868878641487045727059277 1825829490557642147647229)
                  ·
                    refine ⟨684686058959115805367711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825829490557642147647229 684686058959115805367711)
                    ·
                      rfl

theorem cell22_2000132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_2000132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000132 prefixEnd_2000132 := by exact prefixLift 2000132
  have htrace : WordTrace (prefixWord ++ tailWord_2000132) baseStart_2000132 baseEnd_2000132 := by
    simpa [prefixWord, tailWord_2000132, baseEnd_2000132] using wordTrace_append hprefix tailTrace_2000132
  have hstable : (prefixWord ++ tailWord_2000132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000132).length < 2 ^ (prefixWord ++ tailWord_2000132).sum := by decide
  have hdescent : baseEnd_2000132 < baseStart_2000132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000190 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_2000190 : Nat := 118140960795 + 2000190 * 2 ^ 59
def prefixEnd_2000190 : Nat := 4983230072969 + 3 ^ 40 * 2000190 * 2
def baseEnd_2000190 : Nat := 228235304514807662472511

theorem tailTrace_2000190 : CollatzResearch.WordTrace tailWord_2000190 prefixEnd_2000190 228235304514807662472511 := by
  unfold tailWord_2000190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119115327957588762565753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48635281749107140067017349 9119115327957588762565753)
  ·
    refine ⟨6839336495968191571924315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9119115327957588762565753 6839336495968191571924315)
    ·
      refine ⟨10259004743952287357886473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6839336495968191571924315 10259004743952287357886473)
      ·
        refine ⟨7694253557964215518414855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10259004743952287357886473 7694253557964215518414855)
        ·
          refine ⟨11541380336946323277622283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7694253557964215518414855 11541380336946323277622283)
          ·
            refine ⟨17312070505419484916433425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11541380336946323277622283 17312070505419484916433425)
            ·
              refine ⟨12984052879064613687325069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17312070505419484916433425 12984052879064613687325069)
              ·
                refine ⟨4869019829649230132746901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12984052879064613687325069 4869019829649230132746901)
                ·
                  refine ⟨228235304514807662472511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4869019829649230132746901 228235304514807662472511)
                  ·
                    rfl

theorem cell22_2000190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_2000190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000190 prefixEnd_2000190 := by exact prefixLift 2000190
  have htrace : WordTrace (prefixWord ++ tailWord_2000190) baseStart_2000190 baseEnd_2000190 := by
    simpa [prefixWord, tailWord_2000190, baseEnd_2000190] using wordTrace_append hprefix tailTrace_2000190
  have hstable : (prefixWord ++ tailWord_2000190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000190).length < 2 ^ (prefixWord ++ tailWord_2000190).sum := by decide
  have hdescent : baseEnd_2000190 < baseStart_2000190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000218 : List Nat := [3, 1, 1, 2, 1, 2, 2, 10]
def baseStart_2000218 : Nat := 118140960795 + 2000218 * 2 ^ 59
def prefixEnd_2000218 : Nat := 4983230072969 + 3 ^ 40 * 2000218 * 2
def baseEnd_2000218 : Nat := 76079499835182249746383

theorem tailTrace_2000218 : CollatzResearch.WordTrace tailWord_2000218 prefixEnd_2000218 76079499835182249746383 := by
  unfold tailWord_2000218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18238485966889817720636327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48635962578372847255030205 18238485966889817720636327)
  ·
    refine ⟨27357728950334726580954491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18238485966889817720636327 27357728950334726580954491)
    ·
      refine ⟨41036593425502089871431737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27357728950334726580954491 41036593425502089871431737)
      ·
        refine ⟨30777445069126567403573803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41036593425502089871431737 30777445069126567403573803)
        ·
          refine ⟨46166167603689851105360705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30777445069126567403573803 46166167603689851105360705)
          ·
            refine ⟨34624625702767388329020529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46166167603689851105360705 34624625702767388329020529)
            ·
              refine ⟨25968469277075541246765397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34624625702767388329020529 25968469277075541246765397)
              ·
                refine ⟨76079499835182249746383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25968469277075541246765397 76079499835182249746383)
                ·
                  rfl

theorem cell22_2000218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_2000218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000218 prefixEnd_2000218 := by exact prefixLift 2000218
  have htrace : WordTrace (prefixWord ++ tailWord_2000218) baseStart_2000218 baseEnd_2000218 := by
    simpa [prefixWord, tailWord_2000218, baseEnd_2000218] using wordTrace_append hprefix tailTrace_2000218
  have hstable : (prefixWord ++ tailWord_2000218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000218).length < 2 ^ (prefixWord ++ tailWord_2000218).sum := by decide
  have hdescent : baseEnd_2000218 < baseStart_2000218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000250 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_2000250 : Nat := 118140960795 + 2000250 * 2 ^ 59
def prefixEnd_2000250 : Nat := 4983230072969 + 3 ^ 40 * 2000250 * 2
def baseEnd_2000250 : Nat := 684726452770602830917349

theorem tailTrace_2000250 : CollatzResearch.WordTrace tailWord_2000250 prefixEnd_2000250 684726452770602830917349 := by
  unfold tailWord_2000250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18238777750860835086927551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48636740668962226898473469 18238777750860835086927551)
  ·
    refine ⟨27358166626291252630391327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18238777750860835086927551 27358166626291252630391327)
    ·
      refine ⟨41037249939436878945586991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27358166626291252630391327 41037249939436878945586991)
      ·
        refine ⟨61555874909155318418380487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41037249939436878945586991 61555874909155318418380487)
        ·
          refine ⟨92333812363732977627570731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61555874909155318418380487 92333812363732977627570731)
          ·
            refine ⟨138500718545599466441356097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92333812363732977627570731 138500718545599466441356097)
            ·
              refine ⟨103875538909199599831017073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138500718545599466441356097 103875538909199599831017073)
              ·
                refine ⟨77906654181899699873262805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103875538909199599831017073 77906654181899699873262805)
                ·
                  refine ⟨1825937207388274215779597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 77906654181899699873262805 1825937207388274215779597)
                  ·
                    refine ⟨684726452770602830917349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825937207388274215779597 684726452770602830917349)
                    ·
                      rfl

theorem cell22_2000250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_2000250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000250 prefixEnd_2000250 := by exact prefixLift 2000250
  have htrace : WordTrace (prefixWord ++ tailWord_2000250) baseStart_2000250 baseEnd_2000250 := by
    simpa [prefixWord, tailWord_2000250, baseEnd_2000250] using wordTrace_append hprefix tailTrace_2000250
  have hstable : (prefixWord ++ tailWord_2000250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000250).length < 2 ^ (prefixWord ++ tailWord_2000250).sum := by decide
  have hdescent : baseEnd_2000250 < baseStart_2000250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000301 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2000301 : Nat := 118140960795 + 2000301 * 2 ^ 59
def prefixEnd_2000301 : Nat := 4983230072969 + 3 ^ 40 * 2000301 * 2
def baseEnd_2000301 : Nat := 684743911112855697892193

theorem tailTrace_2000301 : CollatzResearch.WordTrace tailWord_2000301 prefixEnd_2000301 684743911112855697892193 := by
  unfold tailWord_2000301
  simp only [CollatzResearch.WordTrace]
  refine ⟨72956971126258576057816757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48637980750839050705211171 72956971126258576057816757)
  ·
    refine ⟨6839716043086741505420321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72956971126258576057816757 6839716043086741505420321)
    ·
      refine ⟨5129787032315056129065241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6839716043086741505420321 5129787032315056129065241)
      ·
        refine ⟨3847340274236292096798931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5129787032315056129065241 3847340274236292096798931)
        ·
          refine ⟨5771010411354438145198397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847340274236292096798931 5771010411354438145198397)
          ·
            refine ⟨2164128904257914304449399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5771010411354438145198397 2164128904257914304449399)
            ·
              refine ⟨3246193356386871456674099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164128904257914304449399 3246193356386871456674099)
              ·
                refine ⟨4869290034580307185011149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246193356386871456674099 4869290034580307185011149)
                ·
                  refine ⟨1825983762967615194379181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4869290034580307185011149 1825983762967615194379181)
                  ·
                    refine ⟨684743911112855697892193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825983762967615194379181 684743911112855697892193)
                    ·
                      rfl

theorem cell22_2000301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2000301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000301 prefixEnd_2000301 := by exact prefixLift 2000301
  have htrace : WordTrace (prefixWord ++ tailWord_2000301) baseStart_2000301 baseEnd_2000301 := by
    simpa [prefixWord, tailWord_2000301, baseEnd_2000301] using wordTrace_append hprefix tailTrace_2000301
  have hstable : (prefixWord ++ tailWord_2000301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000301).length < 2 ^ (prefixWord ++ tailWord_2000301).sum := by decide
  have hdescent : baseEnd_2000301 < baseStart_2000301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000359 : List Nat := [1, 1, 5, 2, 1, 3, 1, 4, 4]
def baseStart_2000359 : Nat := 118140960795 + 2000359 * 2 ^ 59
def prefixEnd_2000359 : Nat := 4983230072969 + 3 ^ 40 * 2000359 * 2
def baseEnd_2000359 : Nat := 228254588566054293314005

theorem tailTrace_2000359 : CollatzResearch.WordTrace tailWord_2000359 prefixEnd_2000359 228254588566054293314005 := by
  unfold tailWord_2000359
  simp only [CollatzResearch.WordTrace]
  refine ⟨72959086560048451963428131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48639391040032301308952087 72959086560048451963428131)
  ·
    refine ⟨109438629840072677945142197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72959086560048451963428131 109438629840072677945142197)
    ·
      refine ⟨10259871547506813557357081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109438629840072677945142197 10259871547506813557357081)
      ·
        refine ⟨7694903660630110168017811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10259871547506813557357081 7694903660630110168017811)
        ·
          refine ⟨11542355490945165252026717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7694903660630110168017811 11542355490945165252026717)
          ·
            refine ⟨4328383309104436969510019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11542355490945165252026717 4328383309104436969510019)
            ·
              refine ⟨6492574963656655454265029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328383309104436969510019 6492574963656655454265029)
              ·
                refine ⟨1217357805685622897674693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6492574963656655454265029 1217357805685622897674693)
                ·
                  refine ⟨228254588566054293314005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217357805685622897674693 228254588566054293314005)
                  ·
                    rfl

theorem cell22_2000359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 4].length) (baseStart_2000359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000359 prefixEnd_2000359 := by exact prefixLift 2000359
  have htrace : WordTrace (prefixWord ++ tailWord_2000359) baseStart_2000359 baseEnd_2000359 := by
    simpa [prefixWord, tailWord_2000359, baseEnd_2000359] using wordTrace_append hprefix tailTrace_2000359
  have hstable : (prefixWord ++ tailWord_2000359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000359).length < 2 ^ (prefixWord ++ tailWord_2000359).sum := by decide
  have hdescent : baseEnd_2000359 < baseStart_2000359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000374 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2000374 : Nat := 118140960795 + 2000374 * 2 ^ 59
def prefixEnd_2000374 : Nat := 4983230072969 + 3 ^ 40 * 2000374 * 2
def baseEnd_2000374 : Nat := 684768900504707840816969

theorem tailTrace_2000374 : CollatzResearch.WordTrace tailWord_2000374 prefixEnd_2000374 684768900504707840816969 := by
  unfold tailWord_2000374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559977103437131845326511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48639755769996073016816117 4559977103437131845326511)
  ·
    refine ⟨6839965655155697767989767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4559977103437131845326511 6839965655155697767989767)
    ·
      refine ⟨10259948482733546651984651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6839965655155697767989767 10259948482733546651984651)
      ·
        refine ⟨15389922724100319977976977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10259948482733546651984651 15389922724100319977976977)
        ·
          refine ⟨11542442043075239983482733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15389922724100319977976977 11542442043075239983482733)
          ·
            refine ⟨4328415766153214993806025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11542442043075239983482733 4328415766153214993806025)
            ·
              refine ⟨3246311824614911245354519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328415766153214993806025 3246311824614911245354519)
              ·
                refine ⟨4869467736922366868031779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246311824614911245354519 4869467736922366868031779)
                ·
                  refine ⟨7304201605383550302047669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869467736922366868031779 7304201605383550302047669)
                  ·
                    refine ⟨684768900504707840816969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7304201605383550302047669 684768900504707840816969)
                    ·
                      rfl

theorem cell22_2000374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2000374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000374 prefixEnd_2000374 := by exact prefixLift 2000374
  have htrace : WordTrace (prefixWord ++ tailWord_2000374) baseStart_2000374 baseEnd_2000374 := by
    simpa [prefixWord, tailWord_2000374, baseEnd_2000374] using wordTrace_append hprefix tailTrace_2000374
  have hstable : (prefixWord ++ tailWord_2000374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000374).length < 2 ^ (prefixWord ++ tailWord_2000374).sum := by decide
  have hdescent : baseEnd_2000374 < baseStart_2000374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000404 : List Nat := [2, 4, 3, 1, 2, 1, 9]
def baseStart_2000404 : Nat := 118140960795 + 2000404 * 2 ^ 59
def prefixEnd_2000404 : Nat := 4983230072969 + 3 ^ 40 * 2000404 * 2
def baseEnd_2000404 : Nat := 25362191485844361576551

theorem tailTrace_2000404 : CollatzResearch.WordTrace tailWord_2000404 prefixEnd_2000404 25362191485844361576551 := by
  unfold tailWord_2000404
  simp only [CollatzResearch.WordTrace]
  refine ⟨36480363922442712324408133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48640485229923616432544177 36480363922442712324408133)
  ·
    refine ⟨6840068235458008560826525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36480363922442712324408133 6840068235458008560826525)
    ·
      refine ⟨2565025588296753210309947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6840068235458008560826525 2565025588296753210309947)
      ·
        refine ⟨3847538382445129815464921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565025588296753210309947 3847538382445129815464921)
        ·
          refine ⟨2885653786833847361598691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3847538382445129815464921 2885653786833847361598691)
          ·
            refine ⟨4328480680250771042398037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885653786833847361598691 4328480680250771042398037)
            ·
              refine ⟨25362191485844361576551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4328480680250771042398037 25362191485844361576551)
              ·
                rfl

theorem cell22_2000404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 9].length) (baseStart_2000404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000404 prefixEnd_2000404 := by exact prefixLift 2000404
  have htrace : WordTrace (prefixWord ++ tailWord_2000404) baseStart_2000404 baseEnd_2000404 := by
    simpa [prefixWord, tailWord_2000404, baseEnd_2000404] using wordTrace_append hprefix tailTrace_2000404
  have hstable : (prefixWord ++ tailWord_2000404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000404).length < 2 ^ (prefixWord ++ tailWord_2000404).sum := by decide
  have hdescent : baseEnd_2000404 < baseStart_2000404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000408 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 2, 3]
def baseStart_2000408 : Nat := 118140960795 + 2000408 * 2 ^ 59
def prefixEnd_2000408 : Nat := 4983230072969 + 3 ^ 40 * 2000408 * 2
def baseEnd_2000408 : Nat := 684780539399543085466865

theorem tailTrace_2000408 : CollatzResearch.WordTrace tailWord_2000408 prefixEnd_2000408 684780539399543085466865 := by
  unfold tailWord_2000408
  simp only [CollatzResearch.WordTrace]
  refine ⟨36480436868435466665980939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48640582491247288887974585 36480436868435466665980939)
  ·
    refine ⟨54720655302653199998971409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36480436868435466665980939 54720655302653199998971409)
    ·
      refine ⟨41040491476989899999228557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54720655302653199998971409 41040491476989899999228557)
      ·
        refine ⟨15390184303871212499710709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41040491476989899999228557 15390184303871212499710709)
        ·
          refine ⟨1442829778487926171847879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15390184303871212499710709 1442829778487926171847879)
          ·
            refine ⟨2164244667731889257771819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442829778487926171847879 2164244667731889257771819)
            ·
              refine ⟨3246367001597833886657729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164244667731889257771819 3246367001597833886657729)
              ·
                refine ⟨2434775251198375414993297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246367001597833886657729 2434775251198375414993297)
                ·
                  refine ⟨1826081438398781561244973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2434775251198375414993297 1826081438398781561244973)
                  ·
                    refine ⟨684780539399543085466865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1826081438398781561244973 684780539399543085466865)
                    ·
                      rfl

theorem cell22_2000408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_2000408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000408 prefixEnd_2000408 := by exact prefixLift 2000408
  have htrace : WordTrace (prefixWord ++ tailWord_2000408) baseStart_2000408 baseEnd_2000408 := by
    simpa [prefixWord, tailWord_2000408, baseEnd_2000408] using wordTrace_append hprefix tailTrace_2000408
  have hstable : (prefixWord ++ tailWord_2000408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000408).length < 2 ^ (prefixWord ++ tailWord_2000408).sum := by decide
  have hdescent : baseEnd_2000408 < baseStart_2000408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000438 : List Nat := [5, 1, 2, 1, 4, 1, 2, 6]
def baseStart_2000438 : Nat := 118140960795 + 2000438 * 2 ^ 59
def prefixEnd_2000438 : Nat := 4983230072969 + 3 ^ 40 * 2000438 * 2
def baseEnd_2000438 : Nat := 76087867668070334135197

theorem tailTrace_2000438 : CollatzResearch.WordTrace tailWord_2000438 prefixEnd_2000438 76087867668070334135197 := by
  unfold tailWord_2000438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560122995422640528472123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48641311951174832303702645 4560122995422640528472123)
  ·
    refine ⟨6840184493133960792708185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4560122995422640528472123 6840184493133960792708185)
    ·
      refine ⟨5130138369850470594531139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6840184493133960792708185 5130138369850470594531139)
      ·
        refine ⟨7695207554775705891796709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130138369850470594531139 7695207554775705891796709)
        ·
          refine ⟨1442851416520444854711883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7695207554775705891796709 1442851416520444854711883)
          ·
            refine ⟨2164277124780667282067825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442851416520444854711883 2164277124780667282067825)
            ·
              refine ⟨1623207843585500461550869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164277124780667282067825 1623207843585500461550869)
              ·
                refine ⟨76087867668070334135197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1623207843585500461550869 76087867668070334135197)
                ·
                  rfl

theorem cell22_2000438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_2000438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000438 prefixEnd_2000438 := by exact prefixLift 2000438
  have htrace : WordTrace (prefixWord ++ tailWord_2000438) baseStart_2000438 baseEnd_2000438 := by
    simpa [prefixWord, tailWord_2000438, baseEnd_2000438] using wordTrace_append hprefix tailTrace_2000438
  have hstable : (prefixWord ++ tailWord_2000438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000438).length < 2 ^ (prefixWord ++ tailWord_2000438).sum := by decide
  have hdescent : baseEnd_2000438 < baseStart_2000438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000462 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2000462 : Nat := 118140960795 + 2000462 * 2 ^ 59
def prefixEnd_2000462 : Nat := 4983230072969 + 3 ^ 40 * 2000462 * 2
def baseEnd_2000462 : Nat := 684799024703104944616699

theorem tailTrace_2000462 : CollatzResearch.WordTrace tailWord_2000462 prefixEnd_2000462 684799024703104944616699 := by
  unfold tailWord_2000462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120355409834412569303455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48641895519116867036285093 9120355409834412569303455)
  ·
    refine ⟨13680533114751618853955183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9120355409834412569303455 13680533114751618853955183)
    ·
      refine ⟨20520799672127428280932775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13680533114751618853955183 20520799672127428280932775)
      ·
        refine ⟨30781199508191142421399163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20520799672127428280932775 30781199508191142421399163)
        ·
          refine ⟨46171799262286713632098745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30781199508191142421399163 46171799262286713632098745)
          ·
            refine ⟨34628849446715035224074059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46171799262286713632098745 34628849446715035224074059)
            ·
              refine ⟨51943274170072552836111089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34628849446715035224074059 51943274170072552836111089)
              ·
                refine ⟨38957455627554414627083317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51943274170072552836111089 38957455627554414627083317)
                ·
                  refine ⟨3652261465083226371289061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38957455627554414627083317 3652261465083226371289061)
                  ·
                    refine ⟨684799024703104944616699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3652261465083226371289061 684799024703104944616699)
                    ·
                      rfl

theorem cell22_2000462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2000462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000462 prefixEnd_2000462 := by exact prefixLift 2000462
  have htrace : WordTrace (prefixWord ++ tailWord_2000462) baseStart_2000462 baseEnd_2000462 := by
    simpa [prefixWord, tailWord_2000462, baseEnd_2000462] using wordTrace_append hprefix tailTrace_2000462
  have hstable : (prefixWord ++ tailWord_2000462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000462).length < 2 ^ (prefixWord ++ tailWord_2000462).sum := by decide
  have hdescent : baseEnd_2000462 < baseStart_2000462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000492 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_2000492 : Nat := 118140960795 + 2000492 * 2 ^ 59
def prefixEnd_2000492 : Nat := 4983230072969 + 3 ^ 40 * 2000492 * 2
def baseEnd_2000492 : Nat := 684809294316194866366607

theorem tailTrace_2000492 : CollatzResearch.WordTrace tailWord_2000492 prefixEnd_2000492 684809294316194866366607 := by
  unfold tailWord_2000492
  simp only [CollatzResearch.WordTrace]
  refine ⟨36481968734283307839009865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48642624979044410452013153 36481968734283307839009865)
  ·
    refine ⟨27361476550712480879257399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36481968734283307839009865 27361476550712480879257399)
    ·
      refine ⟨41042214826068721318886099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27361476550712480879257399 41042214826068721318886099)
      ·
        refine ⟨61563322239103081978329149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41042214826068721318886099 61563322239103081978329149)
        ·
          refine ⟨23086245839663655741873431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61563322239103081978329149 23086245839663655741873431)
          ·
            refine ⟨34629368759495483612810147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23086245839663655741873431 34629368759495483612810147)
            ·
              refine ⟨51944053139243225419215221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34629368759495483612810147 51944053139243225419215221)
              ·
                refine ⟨4869754981804052383051427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51944053139243225419215221 4869754981804052383051427)
                ·
                  refine ⟨7304632472706078574577141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869754981804052383051427 7304632472706078574577141)
                  ·
                    refine ⟨684809294316194866366607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7304632472706078574577141 684809294316194866366607)
                    ·
                      rfl

theorem cell22_2000492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_2000492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000492 prefixEnd_2000492 := by exact prefixLift 2000492
  have htrace : WordTrace (prefixWord ++ tailWord_2000492) baseStart_2000492 baseEnd_2000492 := by
    simpa [prefixWord, tailWord_2000492, baseEnd_2000492] using wordTrace_append hprefix tailTrace_2000492
  have hstable : (prefixWord ++ tailWord_2000492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000492).length < 2 ^ (prefixWord ++ tailWord_2000492).sum := by decide
  have hdescent : baseEnd_2000492 < baseStart_2000492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000496 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 1, 4]
def baseStart_2000496 : Nat := 118140960795 + 2000496 * 2 ^ 59
def prefixEnd_2000496 : Nat := 4983230072969 + 3 ^ 40 * 2000496 * 2
def baseEnd_2000496 : Nat := 684810663597940189266595

theorem tailTrace_2000496 : CollatzResearch.WordTrace tailWord_2000496 prefixEnd_2000496 684810663597940189266595 := by
  unfold tailWord_2000496
  simp only [CollatzResearch.WordTrace]
  refine ⟨36482041680276062180582671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48642722240368082907443561 36482041680276062180582671)
  ·
    refine ⟨54723062520414093270874007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36482041680276062180582671 54723062520414093270874007)
    ·
      refine ⟨82084593780621139906311011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54723062520414093270874007 82084593780621139906311011)
      ·
        refine ⟨123126890670931709859466517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82084593780621139906311011 123126890670931709859466517)
        ·
          refine ⟨5771573000199923899662493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123126890670931709859466517 5771573000199923899662493)
          ·
            refine ⟨2164339875074971462373435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5771573000199923899662493 2164339875074971462373435)
            ·
              refine ⟨3246509812612457193560153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164339875074971462373435 3246509812612457193560153)
              ·
                refine ⟨2434882359459342895170115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246509812612457193560153 2434882359459342895170115)
                ·
                  refine ⟨3652323539189014342755173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434882359459342895170115 3652323539189014342755173)
                  ·
                    refine ⟨684810663597940189266595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3652323539189014342755173 684810663597940189266595)
                    ·
                      rfl

theorem cell22_2000496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_2000496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000496 prefixEnd_2000496 := by exact prefixLift 2000496
  have htrace : WordTrace (prefixWord ++ tailWord_2000496) baseStart_2000496 baseEnd_2000496 := by
    simpa [prefixWord, tailWord_2000496, baseEnd_2000496] using wordTrace_append hprefix tailTrace_2000496
  have hstable : (prefixWord ++ tailWord_2000496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000496).length < 2 ^ (prefixWord ++ tailWord_2000496).sum := by decide
  have hdescent : baseEnd_2000496 < baseStart_2000496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000509 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_2000509 : Nat := 118140960795 + 2000509 * 2 ^ 59
def prefixEnd_2000509 : Nat := 4983230072969 + 3 ^ 40 * 2000509 * 2
def baseEnd_2000509 : Nat := 684815113763612488691555

theorem tailTrace_2000509 : CollatzResearch.WordTrace tailWord_2000509 prefixEnd_2000509 684815113763612488691555 := by
  unfold tailWord_2000509
  simp only [CollatzResearch.WordTrace]
  refine ⟨72964557509505027581388581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48643038339670018387592387 72964557509505027581388581)
  ·
    refine ⟨13680854533032192671510359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72964557509505027581388581 13680854533032192671510359)
    ·
      refine ⟨20521281799548289007265539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13680854533032192671510359 20521281799548289007265539)
      ·
        refine ⟨30781922699322433510898309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20521281799548289007265539 30781922699322433510898309)
        ·
          refine ⟨5771610506122956283293433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30781922699322433510898309 5771610506122956283293433)
          ·
            refine ⟨4328707879592217212470075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5771610506122956283293433 4328707879592217212470075)
            ·
              refine ⟨6493061819388325818705113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328707879592217212470075 6493061819388325818705113)
              ·
                refine ⟨4869796364541244364028835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6493061819388325818705113 4869796364541244364028835)
                ·
                  refine ⟨7304694546811866546043253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869796364541244364028835 7304694546811866546043253)
                  ·
                    refine ⟨684815113763612488691555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7304694546811866546043253 684815113763612488691555)
                    ·
                      rfl

theorem cell22_2000509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_2000509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000509 prefixEnd_2000509 := by exact prefixLift 2000509
  have htrace : WordTrace (prefixWord ++ tailWord_2000509) baseStart_2000509 baseEnd_2000509 := by
    simpa [prefixWord, tailWord_2000509, baseEnd_2000509] using wordTrace_append hprefix tailTrace_2000509
  have hstable : (prefixWord ++ tailWord_2000509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000509).length < 2 ^ (prefixWord ++ tailWord_2000509).sum := by decide
  have hdescent : baseEnd_2000509 < baseStart_2000509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000522 : List Nat := [3, 1, 2, 3, 2, 11]
def baseStart_2000522 : Nat := 118140960795 + 2000522 * 2 ^ 59
def prefixEnd_2000522 : Nat := 4983230072969 + 3 ^ 40 * 2000522 * 2
def baseEnd_2000522 : Nat := 8454562517645491211315

theorem tailTrace_2000522 : CollatzResearch.WordTrace tailWord_2000522 prefixEnd_2000522 8454562517645491211315 := by
  unfold tailWord_2000522
  simp only [CollatzResearch.WordTrace]
  refine ⟨18241257914614482700402955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48643354438971953867741213 18241257914614482700402955)
  ·
    refine ⟨27361886871921724050604433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18241257914614482700402955 27361886871921724050604433)
    ·
      refine ⟨20521415153941293037953325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27361886871921724050604433 20521415153941293037953325)
      ·
        refine ⟨7695530682727984889232497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20521415153941293037953325 7695530682727984889232497)
        ·
          refine ⟨5771648012045988666924373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7695530682727984889232497 5771648012045988666924373)
          ·
            refine ⟨8454562517645491211315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5771648012045988666924373 8454562517645491211315)
            ·
              rfl

theorem cell22_2000522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 11].length) (baseStart_2000522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000522 prefixEnd_2000522 := by exact prefixLift 2000522
  have htrace : WordTrace (prefixWord ++ tailWord_2000522) baseStart_2000522 baseEnd_2000522 := by
    simpa [prefixWord, tailWord_2000522, baseEnd_2000522] using wordTrace_append hprefix tailTrace_2000522
  have hstable : (prefixWord ++ tailWord_2000522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000522).length < 2 ^ (prefixWord ++ tailWord_2000522).sum := by decide
  have hdescent : baseEnd_2000522 < baseStart_2000522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000526 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_2000526 : Nat := 118140960795 + 2000526 * 2 ^ 59
def prefixEnd_2000526 : Nat := 4983230072969 + 3 ^ 40 * 2000526 * 2
def baseEnd_2000526 : Nat := 684820933211030111016503

theorem tailTrace_2000526 : CollatzResearch.WordTrace tailWord_2000526 prefixEnd_2000526 684820933211030111016503 := by
  unfold tailWord_2000526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120647193805429935594679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48643451700295626323171621 9120647193805429935594679)
  ·
    refine ⟨13680970790708144903392019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9120647193805429935594679 13680970790708144903392019)
    ·
      refine ⟨20521456186062217355088029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13680970790708144903392019 20521456186062217355088029)
      ·
        refine ⟨7695546069773331508158011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20521456186062217355088029 7695546069773331508158011)
        ·
          refine ⟨11543319104659997262237017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695546069773331508158011 11543319104659997262237017)
          ·
            refine ⟨8657489328494997946677763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11543319104659997262237017 8657489328494997946677763)
            ·
              refine ⟨12986233992742496920016645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657489328494997946677763 12986233992742496920016645)
              ·
                refine ⟨2434918873639218172503121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12986233992742496920016645 2434918873639218172503121)
                ·
                  refine ⟨1826189155229413629377341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2434918873639218172503121 1826189155229413629377341)
                  ·
                    refine ⟨684820933211030111016503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1826189155229413629377341 684820933211030111016503)
                    ·
                      rfl

theorem cell22_2000526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_2000526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000526 prefixEnd_2000526 := by exact prefixLift 2000526
  have htrace : WordTrace (prefixWord ++ tailWord_2000526) baseStart_2000526 baseEnd_2000526 := by
    simpa [prefixWord, tailWord_2000526, baseEnd_2000526] using wordTrace_append hprefix tailTrace_2000526
  have hstable : (prefixWord ++ tailWord_2000526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000526).length < 2 ^ (prefixWord ++ tailWord_2000526).sum := by decide
  have hdescent : baseEnd_2000526 < baseStart_2000526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000588 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_2000588 : Nat := 118140960795 + 2000588 * 2 ^ 59
def prefixEnd_2000588 : Nat := 4983230072969 + 3 ^ 40 * 2000588 * 2
def baseEnd_2000588 : Nat := 684842157078082615966313

theorem tailTrace_2000588 : CollatzResearch.WordTrace tailWord_2000588 prefixEnd_2000588 684842157078082615966313 := by
  unfold tailWord_2000588
  simp only [CollatzResearch.WordTrace]
  refine ⟨36483719438109412036757209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48644959250812549382342945 36483719438109412036757209)
  ·
    refine ⟨27362789578582059027567907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36483719438109412036757209 27362789578582059027567907)
    ·
      refine ⟨41044184367873088541351861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27362789578582059027567907 41044184367873088541351861)
      ·
        refine ⟨3847892284488102050751737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41044184367873088541351861 3847892284488102050751737)
        ·
          refine ⟨2885919213366076538063803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3847892284488102050751737 2885919213366076538063803)
          ·
            refine ⟨4328878820049114807095705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885919213366076538063803 4328878820049114807095705)
            ·
              refine ⟨3246659115036836105321779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328878820049114807095705 3246659115036836105321779)
              ·
                refine ⟨4869988672555254157982669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246659115036836105321779 4869988672555254157982669)
                ·
                  refine ⟨1826245752208220309243501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4869988672555254157982669 1826245752208220309243501)
                  ·
                    refine ⟨684842157078082615966313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1826245752208220309243501 684842157078082615966313)
                    ·
                      rfl

theorem cell22_2000588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_2000588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000588 prefixEnd_2000588 := by exact prefixLift 2000588
  have htrace : WordTrace (prefixWord ++ tailWord_2000588) baseStart_2000588 baseEnd_2000588 := by
    simpa [prefixWord, tailWord_2000588, baseEnd_2000588] using wordTrace_append hprefix tailTrace_2000588
  have hstable : (prefixWord ++ tailWord_2000588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000588).length < 2 ^ (prefixWord ++ tailWord_2000588).sum := by decide
  have hdescent : baseEnd_2000588 < baseStart_2000588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000601 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 5]
def baseStart_2000601 : Nat := 118140960795 + 2000601 * 2 ^ 59
def prefixEnd_2000601 : Nat := 4983230072969 + 3 ^ 40 * 2000601 * 2
def baseEnd_2000601 : Nat := 228282202414584971797091

theorem tailTrace_2000601 : CollatzResearch.WordTrace tailWord_2000601 prefixEnd_2000601 228282202414584971797091 := by
  unfold tailWord_2000601
  simp only [CollatzResearch.WordTrace]
  refine ⟨72967913025171727293737657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48645275350114484862491771 72967913025171727293737657)
  ·
    refine ⟨54725934768878795470303243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72967913025171727293737657 54725934768878795470303243)
    ·
      refine ⟨82088902153318193205454865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54725934768878795470303243 82088902153318193205454865)
      ·
        refine ⟨61566676614988644904091149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82088902153318193205454865 61566676614988644904091149)
        ·
          refine ⟨23087503730620741839034181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61566676614988644904091149 23087503730620741839034181)
          ·
            refine ⟨4328906949491389094818909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23087503730620741839034181 4328906949491389094818909)
            ·
              refine ⟨1623340106059270910557091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4328906949491389094818909 1623340106059270910557091)
              ·
                refine ⟨2435010159088906365835637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623340106059270910557091 2435010159088906365835637)
                ·
                  refine ⟨228282202414584971797091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2435010159088906365835637 228282202414584971797091)
                  ·
                    rfl

theorem cell22_2000601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_2000601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000601 prefixEnd_2000601 := by exact prefixLift 2000601
  have htrace : WordTrace (prefixWord ++ tailWord_2000601) baseStart_2000601 baseEnd_2000601 := by
    simpa [prefixWord, tailWord_2000601, baseEnd_2000601] using wordTrace_append hprefix tailTrace_2000601
  have hstable : (prefixWord ++ tailWord_2000601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000601).length < 2 ^ (prefixWord ++ tailWord_2000601).sum := by decide
  have hdescent : baseEnd_2000601 < baseStart_2000601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000674 : List Nat := [3, 3, 1, 1, 2, 1, 1, 10]
def baseStart_2000674 : Nat := 118140960795 + 2000674 * 2 ^ 59
def prefixEnd_2000674 : Nat := 4983230072969 + 3 ^ 40 * 2000674 * 2
def baseEnd_2000674 : Nat := 76096844070623006479561

theorem tailTrace_2000674 : CollatzResearch.WordTrace tailWord_2000674 prefixEnd_2000674 76096844070623006479561 := by
  unfold tailWord_2000674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18242643888476815190286269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48647050369271507174096717 18242643888476815190286269)
  ·
    refine ⟨6840991458178805696357351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18242643888476815190286269 6840991458178805696357351)
    ·
      refine ⟨10261487187268208544536027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840991458178805696357351 10261487187268208544536027)
      ·
        refine ⟨15392230780902312816804041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10261487187268208544536027 15392230780902312816804041)
        ·
          refine ⟨11544173085676734612603031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15392230780902312816804041 11544173085676734612603031)
          ·
            refine ⟨17316259628515101918904547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11544173085676734612603031 17316259628515101918904547)
            ·
              refine ⟨25974389442772652878356821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17316259628515101918904547 25974389442772652878356821)
              ·
                refine ⟨76096844070623006479561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25974389442772652878356821 76096844070623006479561)
                ·
                  rfl

theorem cell22_2000674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_2000674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000674 prefixEnd_2000674 := by exact prefixLift 2000674
  have htrace : WordTrace (prefixWord ++ tailWord_2000674) baseStart_2000674 baseEnd_2000674 := by
    simpa [prefixWord, tailWord_2000674, baseEnd_2000674] using wordTrace_append hprefix tailTrace_2000674
  have hstable : (prefixWord ++ tailWord_2000674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000674).length < 2 ^ (prefixWord ++ tailWord_2000674).sum := by decide
  have hdescent : baseEnd_2000674 < baseStart_2000674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000676 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_2000676 : Nat := 118140960795 + 2000676 * 2 ^ 59
def prefixEnd_2000676 : Nat := 4983230072969 + 3 ^ 40 * 2000676 * 2
def baseEnd_2000676 : Nat := 684872281276479719766043

theorem tailTrace_2000676 : CollatzResearch.WordTrace tailWord_2000676 prefixEnd_2000676 684872281276479719766043 := by
  unfold tailWord_2000676
  simp only [CollatzResearch.WordTrace]
  refine ⟨36485324249950007551358941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48647098999933343401811921 36485324249950007551358941)
  ·
    refine ⟨13681996593731252831759603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36485324249950007551358941 13681996593731252831759603)
    ·
      refine ⟨20522994890596879247639405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13681996593731252831759603 20522994890596879247639405)
      ·
        refine ⟨7696123083973829717864777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20522994890596879247639405 7696123083973829717864777)
        ·
          refine ⟨5772092312980372288398583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7696123083973829717864777 5772092312980372288398583)
          ·
            refine ⟨8658138469470558432597875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772092312980372288398583 8658138469470558432597875)
            ·
              refine ⟨12987207704205837648896813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658138469470558432597875 12987207704205837648896813)
              ·
                refine ⟨4870202889077189118336305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12987207704205837648896813 4870202889077189118336305)
                ·
                  refine ⟨3652652166807891838752229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4870202889077189118336305 3652652166807891838752229)
                  ·
                    refine ⟨684872281276479719766043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3652652166807891838752229 684872281276479719766043)
                    ·
                      rfl

theorem cell22_2000676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_2000676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000676 prefixEnd_2000676 := by exact prefixLift 2000676
  have htrace : WordTrace (prefixWord ++ tailWord_2000676) baseStart_2000676 baseEnd_2000676 := by
    simpa [prefixWord, tailWord_2000676, baseEnd_2000676] using wordTrace_append hprefix tailTrace_2000676
  have hstable : (prefixWord ++ tailWord_2000676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000676).length < 2 ^ (prefixWord ++ tailWord_2000676).sum := by decide
  have hdescent : baseEnd_2000676 < baseStart_2000676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000697 : List Nat := [1, 2, 1, 7, 1, 2, 2, 2, 4]
def baseStart_2000697 : Nat := 118140960795 + 2000697 * 2 ^ 59
def prefixEnd_2000697 : Nat := 4983230072969 + 3 ^ 40 * 2000697 * 2
def baseEnd_2000697 : Nat := 228293156668547554996993

theorem tailTrace_2000697 : CollatzResearch.WordTrace tailWord_2000697 prefixEnd_2000697 228293156668547554996993 := by
  unfold tailWord_2000697
  simp only [CollatzResearch.WordTrace]
  refine ⟨72971414432823935689232345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48647609621882623792821563 72971414432823935689232345)
  ·
    refine ⟨54728560824617951766924259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72971414432823935689232345 54728560824617951766924259)
    ·
      refine ⟨82092841236926927650386389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54728560824617951766924259 82092841236926927650386389)
      ·
        refine ⟨1924050966490474866805931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 82092841236926927650386389 1924050966490474866805931)
        ·
          refine ⟨2886076449735712300208897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924050966490474866805931 2886076449735712300208897)
          ·
            refine ⟨2164557337301784225156673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886076449735712300208897 2164557337301784225156673)
            ·
              refine ⟨1623418002976338168867505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164557337301784225156673 1623418002976338168867505)
              ·
                refine ⟨1217563502232253626650629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623418002976338168867505 1217563502232253626650629)
                ·
                  refine ⟨228293156668547554996993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217563502232253626650629 228293156668547554996993)
                  ·
                    rfl

theorem cell22_2000697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 4].length) (baseStart_2000697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000697 prefixEnd_2000697 := by exact prefixLift 2000697
  have htrace : WordTrace (prefixWord ++ tailWord_2000697) baseStart_2000697 baseEnd_2000697 := by
    simpa [prefixWord, tailWord_2000697, baseEnd_2000697] using wordTrace_append hprefix tailTrace_2000697
  have hstable : (prefixWord ++ tailWord_2000697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000697).length < 2 ^ (prefixWord ++ tailWord_2000697).sum := by decide
  have hdescent : baseEnd_2000697 < baseStart_2000697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000830 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_2000830 : Nat := 118140960795 + 2000830 * 2 ^ 59
def prefixEnd_2000830 : Nat := 4983230072969 + 3 ^ 40 * 2000830 * 2
def baseEnd_2000830 : Nat := 684924998623674651415571

theorem tailTrace_2000830 : CollatzResearch.WordTrace tailWord_2000830 prefixEnd_2000830 684924998623674651415571 := by
  unfold tailWord_2000830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9122033167667762425477993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48650843560894732935882629 9122033167667762425477993)
  ·
    refine ⟨6841524875750821819108495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9122033167667762425477993 6841524875750821819108495)
    ·
      refine ⟨10262287313626232728662743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6841524875750821819108495 10262287313626232728662743)
      ·
        refine ⟨15393430970439349092994115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10262287313626232728662743 15393430970439349092994115)
        ·
          refine ⟨23090146455659023639491173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15393430970439349092994115 23090146455659023639491173)
          ·
            refine ⟨4329402460436066932404595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23090146455659023639491173 4329402460436066932404595)
            ·
              refine ⟨6494103690654100398606893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329402460436066932404595 6494103690654100398606893)
              ·
                refine ⟨2435288883995287649477585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6494103690654100398606893 2435288883995287649477585)
                ·
                  refine ⟨1826466662996465737108189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2435288883995287649477585 1826466662996465737108189)
                  ·
                    refine ⟨684924998623674651415571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1826466662996465737108189 684924998623674651415571)
                    ·
                      rfl

theorem cell22_2000830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_2000830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000830 prefixEnd_2000830 := by exact prefixLift 2000830
  have htrace : WordTrace (prefixWord ++ tailWord_2000830) baseStart_2000830 baseEnd_2000830 := by
    simpa [prefixWord, tailWord_2000830, baseEnd_2000830] using wordTrace_append hprefix tailTrace_2000830
  have hstable : (prefixWord ++ tailWord_2000830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000830).length < 2 ^ (prefixWord ++ tailWord_2000830).sum := by decide
  have hdescent : baseEnd_2000830 < baseStart_2000830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000860 : List Nat := [2, 2, 6, 1, 1, 10]
def baseStart_2000860 : Nat := 118140960795 + 2000860 * 2 ^ 59
def prefixEnd_2000860 : Nat := 4983230072969 + 3 ^ 40 * 2000860 * 2
def baseEnd_2000860 : Nat := 8455990965885982384759

theorem tailTrace_2000860 : CollatzResearch.WordTrace tailWord_2000860 prefixEnd_2000860 8455990965885982384759 := by
  unfold tailWord_2000860
  simp only [CollatzResearch.WordTrace]
  refine ⟨36488679765616707263708017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48651573020822276351610689 36488679765616707263708017)
  ·
    refine ⟨27366509824212530447781013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36488679765616707263708017 27366509824212530447781013)
    ·
      refine ⟨1282805148009962364739735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27366509824212530447781013 1282805148009962364739735)
      ·
        refine ⟨1924207722014943547109603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282805148009962364739735 1924207722014943547109603)
        ·
          refine ⟨2886311583022415320664405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924207722014943547109603 2886311583022415320664405)
          ·
            refine ⟨8455990965885982384759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2886311583022415320664405 8455990965885982384759)
            ·
              rfl

theorem cell22_2000860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 10].length) (baseStart_2000860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000860 prefixEnd_2000860 := by exact prefixLift 2000860
  have htrace : WordTrace (prefixWord ++ tailWord_2000860) baseStart_2000860 baseEnd_2000860 := by
    simpa [prefixWord, tailWord_2000860, baseEnd_2000860] using wordTrace_append hprefix tailTrace_2000860
  have hstable : (prefixWord ++ tailWord_2000860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000860).length < 2 ^ (prefixWord ++ tailWord_2000860).sum := by decide
  have hdescent : baseEnd_2000860 < baseStart_2000860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000866 : List Nat := [3, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_2000866 : Nat := 118140960795 + 2000866 * 2 ^ 59
def prefixEnd_2000866 : Nat := 4983230072969 + 3 ^ 40 * 2000866 * 2
def baseEnd_2000866 : Nat := 228312440719794185838487

theorem tailTrace_2000866 : CollatzResearch.WordTrace tailWord_2000866 prefixEnd_2000866 228312440719794185838487 := by
  unfold tailWord_2000866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18244394592302919388033613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48651718912807785034756301 18244394592302919388033613)
  ·
    refine ⟨6841647972113594770512605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18244394592302919388033613 6841647972113594770512605)
    ·
      refine ⟨2565617989542598038942227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6841647972113594770512605 2565617989542598038942227)
      ·
        refine ⟨3848426984313897058413341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565617989542598038942227 3848426984313897058413341)
        ·
          refine ⟨1443160119117711396905003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3848426984313897058413341 1443160119117711396905003)
          ·
            refine ⟨2164740178676567095357505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443160119117711396905003 2164740178676567095357505)
            ·
              refine ⟨1623555134007425321518129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164740178676567095357505 1623555134007425321518129)
              ·
                refine ⟨1217666350505568991138597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623555134007425321518129 1217666350505568991138597)
                ·
                  refine ⟨228312440719794185838487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217666350505568991138597 228312440719794185838487)
                  ·
                    rfl

theorem cell22_2000866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_2000866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000866 prefixEnd_2000866 := by exact prefixLift 2000866
  have htrace : WordTrace (prefixWord ++ tailWord_2000866) baseStart_2000866 baseEnd_2000866 := by
    simpa [prefixWord, tailWord_2000866, baseEnd_2000866] using wordTrace_append hprefix tailTrace_2000866
  have hstable : (prefixWord ++ tailWord_2000866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000866).length < 2 ^ (prefixWord ++ tailWord_2000866).sum := by decide
  have hdescent : baseEnd_2000866 < baseStart_2000866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000877 : List Nat := [1, 5, 1, 4, 2, 1, 1, 7]
def baseStart_2000877 : Nat := 118140960795 + 2000877 * 2 ^ 59
def prefixEnd_2000877 : Nat := 4983230072969 + 3 ^ 40 * 2000877 * 2
def baseEnd_2000877 : Nat := 76104565298242466165603

theorem tailTrace_2000877 : CollatzResearch.WordTrace tailWord_2000877 prefixEnd_2000877 76104565298242466165603 := by
  unfold tailWord_2000877
  simp only [CollatzResearch.WordTrace]
  refine ⟨72977979572171826430784885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48651986381447884287189923 72977979572171826430784885)
  ·
    refine ⟨6841685584891108727886083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72977979572171826430784885 6841685584891108727886083)
    ·
      refine ⟨10262528377336663091829125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6841685584891108727886083 10262528377336663091829125)
      ·
        refine ⟨1924224070750624329717961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10262528377336663091829125 1924224070750624329717961)
        ·
          refine ⟨1443168053062968247288471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1924224070750624329717961 1443168053062968247288471)
          ·
            refine ⟨2164752079594452370932707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443168053062968247288471 2164752079594452370932707)
            ·
              refine ⟨3247128119391678556399061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164752079594452370932707 3247128119391678556399061)
              ·
                refine ⟨76104565298242466165603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3247128119391678556399061 76104565298242466165603)
                ·
                  rfl

theorem cell22_2000877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 7].length) (baseStart_2000877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000877 prefixEnd_2000877 := by exact prefixLift 2000877
  have htrace : WordTrace (prefixWord ++ tailWord_2000877) baseStart_2000877 baseEnd_2000877 := by
    simpa [prefixWord, tailWord_2000877, baseEnd_2000877] using wordTrace_append hprefix tailTrace_2000877
  have hstable : (prefixWord ++ tailWord_2000877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000877).length < 2 ^ (prefixWord ++ tailWord_2000877).sum := by decide
  have hdescent : baseEnd_2000877 < baseStart_2000877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000933 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 6]
def baseStart_2000933 : Nat := 118140960795 + 2000933 * 2 ^ 59
def prefixEnd_2000933 : Nat := 4983230072969 + 3 ^ 40 * 2000933 * 2
def baseEnd_2000933 : Nat := 228320085876205572030085

theorem tailTrace_2000933 : CollatzResearch.WordTrace tailWord_2000933 prefixEnd_2000933 228320085876205572030085 := by
  unfold tailWord_2000933
  simp only [CollatzResearch.WordTrace]
  refine ⟨72980022059968947994823453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48653348039979298663215635 72980022059968947994823453)
  ·
    refine ⟨27367508272488355498058795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72980022059968947994823453 27367508272488355498058795)
    ·
      refine ⟨41051262408732533247088193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27367508272488355498058795 41051262408732533247088193)
      ·
        refine ⟨30788446806549399935316145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41051262408732533247088193 30788446806549399935316145)
        ·
          refine ⟨23091335104912049951487109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30788446806549399935316145 23091335104912049951487109)
          ·
            refine ⟨4329625332171009365903833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23091335104912049951487109 4329625332171009365903833)
            ·
              refine ⟨3247218999128257024427875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4329625332171009365903833 3247218999128257024427875)
              ·
                refine ⟨4870828498692385536641813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247218999128257024427875 4870828498692385536641813)
                ·
                  refine ⟨228320085876205572030085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4870828498692385536641813 228320085876205572030085)
                  ·
                    rfl

theorem cell22_2000933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_2000933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2000933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2000933 prefixEnd_2000933 := by exact prefixLift 2000933
  have htrace : WordTrace (prefixWord ++ tailWord_2000933) baseStart_2000933 baseEnd_2000933 := by
    simpa [prefixWord, tailWord_2000933, baseEnd_2000933] using wordTrace_append hprefix tailTrace_2000933
  have hstable : (prefixWord ++ tailWord_2000933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000933).length < 2 ^ (prefixWord ++ tailWord_2000933).sum := by decide
  have hdescent : baseEnd_2000933 < baseStart_2000933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001055 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 2, 5]
def baseStart_2001055 : Nat := 118140960795 + 2001055 * 2 ^ 59
def prefixEnd_2001055 : Nat := 4983230072969 + 3 ^ 40 * 2001055 * 2
def baseEnd_2001055 : Nat := 685002020721849064539881

theorem tailTrace_2001055 : CollatzResearch.WordTrace tailWord_2001055 prefixEnd_2001055 685002020721849064539881 := by
  unfold tailWord_2001055
  simp only [CollatzResearch.WordTrace]
  refine ⟨72984471765526962830764619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48656314510351308553843079 72984471765526962830764619)
  ·
    refine ⟨109476707648290444246146929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72984471765526962830764619 109476707648290444246146929)
    ·
      refine ⟨82107530736217833184610197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109476707648290444246146929 82107530736217833184610197)
      ·
        refine ⟨3848790503260210930528603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82107530736217833184610197 3848790503260210930528603)
        ·
          refine ⟨5773185754890316395792905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848790503260210930528603 5773185754890316395792905)
          ·
            refine ⟨4329889316167737296844679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773185754890316395792905 4329889316167737296844679)
            ·
              refine ⟨6494833974251605945267019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329889316167737296844679 6494833974251605945267019)
              ·
                refine ⟨9742250961377408917900529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494833974251605945267019 9742250961377408917900529)
                ·
                  refine ⟨7306688221033056688425397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9742250961377408917900529 7306688221033056688425397)
                  ·
                    refine ⟨685002020721849064539881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7306688221033056688425397 685002020721849064539881)
                    ·
                      rfl

theorem cell22_2001055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_2001055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001055 prefixEnd_2001055 := by exact prefixLift 2001055
  have htrace : WordTrace (prefixWord ++ tailWord_2001055) baseStart_2001055 baseEnd_2001055 := by
    simpa [prefixWord, tailWord_2001055, baseEnd_2001055] using wordTrace_append hprefix tailTrace_2001055
  have hstable : (prefixWord ++ tailWord_2001055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001055).length < 2 ^ (prefixWord ++ tailWord_2001055).sum := by decide
  have hdescent : baseEnd_2001055 < baseStart_2001055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001083 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 1, 5]
def baseStart_2001083 : Nat := 118140960795 + 2001083 * 2 ^ 59
def prefixEnd_2001083 : Nat := 4983230072969 + 3 ^ 40 * 2001083 * 2
def baseEnd_2001083 : Nat := 685011605694066324839795

theorem tailTrace_2001083 : CollatzResearch.WordTrace tailWord_2001083 prefixEnd_2001083 685011605694066324839795 := by
  unfold tailWord_2001083
  simp only [CollatzResearch.WordTrace]
  refine ⟨72985493009425523612783903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48656995339617015741855935 72985493009425523612783903)
  ·
    refine ⟨109478239514138285419175855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72985493009425523612783903 109478239514138285419175855)
    ·
      refine ⟨164217359271207428128763783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109478239514138285419175855 164217359271207428128763783)
      ·
        refine ⟨246326038906811142193145675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164217359271207428128763783 246326038906811142193145675)
        ·
          refine ⟨369489058360216713289718513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246326038906811142193145675 369489058360216713289718513)
          ·
            refine ⟨277116793770162534967288885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369489058360216713289718513 277116793770162534967288885)
            ·
              refine ⟨25979699415952737653183333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277116793770162534967288885 25979699415952737653183333)
              ·
                refine ⟨4871193640491138309971875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25979699415952737653183333 4871193640491138309971875)
                ·
                  refine ⟨7306790460736707464957813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871193640491138309971875 7306790460736707464957813)
                  ·
                    refine ⟨685011605694066324839795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7306790460736707464957813 685011605694066324839795)
                    ·
                      rfl

theorem cell22_2001083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_2001083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001083 prefixEnd_2001083 := by exact prefixLift 2001083
  have htrace : WordTrace (prefixWord ++ tailWord_2001083) baseStart_2001083 baseEnd_2001083 := by
    simpa [prefixWord, tailWord_2001083, baseEnd_2001083] using wordTrace_append hprefix tailTrace_2001083
  have hstable : (prefixWord ++ tailWord_2001083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001083).length < 2 ^ (prefixWord ++ tailWord_2001083).sum := by decide
  have hdescent : baseEnd_2001083 < baseStart_2001083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001102 : List Nat := [4, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_2001102 : Nat := 118140960795 + 2001102 * 2 ^ 59
def prefixEnd_2001102 : Nat := 4983230072969 + 3 ^ 40 * 2001102 * 2
def baseEnd_2001102 : Nat := 228339369927452202871579

theorem tailTrace_2001102 : CollatzResearch.WordTrace tailWord_2001102 prefixEnd_2001102 228339369927452202871579 := by
  unfold tailWord_2001102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9123273249544586232215695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48657457330904459905150373 9123273249544586232215695)
  ·
    refine ⟨13684909874316879348323543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9123273249544586232215695 13684909874316879348323543)
    ·
      refine ⟨20527364811475319022485315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13684909874316879348323543 20527364811475319022485315)
      ·
        refine ⟨30791047217212978533727973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20527364811475319022485315 30791047217212978533727973)
        ·
          refine ⟨5773321353227433475073995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30791047217212978533727973 5773321353227433475073995)
          ·
            refine ⟨8659982029841150212610993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773321353227433475073995 8659982029841150212610993)
            ·
              refine ⟨6494986522380862659458245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8659982029841150212610993 6494986522380862659458245)
              ·
                refine ⟨1217809972946411748648421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6494986522380862659458245 1217809972946411748648421)
                ·
                  refine ⟨228339369927452202871579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217809972946411748648421 228339369927452202871579)
                  ·
                    rfl

theorem cell22_2001102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_2001102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001102 prefixEnd_2001102 := by exact prefixLift 2001102
  have htrace : WordTrace (prefixWord ++ tailWord_2001102) baseStart_2001102 baseEnd_2001102 := by
    simpa [prefixWord, tailWord_2001102, baseEnd_2001102] using wordTrace_append hprefix tailTrace_2001102
  have hstable : (prefixWord ++ tailWord_2001102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001102).length < 2 ^ (prefixWord ++ tailWord_2001102).sum := by decide
  have hdescent : baseEnd_2001102 < baseStart_2001102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001117 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2001117 : Nat := 118140960795 + 2001117 * 2 ^ 59
def prefixEnd_2001117 : Nat := 4983230072969 + 3 ^ 40 * 2001117 * 2
def baseEnd_2001117 : Nat := 685023244588901569489691

theorem tailTrace_2001117 : CollatzResearch.WordTrace tailWord_2001117 prefixEnd_2001117 685023244588901569489691 := by
  unfold tailWord_2001117
  simp only [CollatzResearch.WordTrace]
  refine ⟨72986733091302347419521605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48657822060868231613014403 72986733091302347419521605)
  ·
    refine ⟨13685012454619190141160301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72986733091302347419521605 13685012454619190141160301)
    ·
      refine ⟨5131879670482196302935113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13685012454619190141160301 5131879670482196302935113)
      ·
        refine ⟨3848909752861647227201335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5131879670482196302935113 3848909752861647227201335)
        ·
          refine ⟨5773364629292470840802003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848909752861647227201335 5773364629292470840802003)
          ·
            refine ⟨8660046943938706261203005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773364629292470840802003 8660046943938706261203005)
            ·
              refine ⟨3247517603977014847951127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8660046943938706261203005 3247517603977014847951127)
              ·
                refine ⟨4871276405965522271926691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247517603977014847951127 4871276405965522271926691)
                ·
                  refine ⟨7306914608948283407890037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871276405965522271926691 7306914608948283407890037)
                  ·
                    refine ⟨685023244588901569489691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7306914608948283407890037 685023244588901569489691)
                    ·
                      rfl

theorem cell22_2001117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2001117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001117 prefixEnd_2001117 := by exact prefixLift 2001117
  have htrace : WordTrace (prefixWord ++ tailWord_2001117) baseStart_2001117 baseEnd_2001117 := by
    simpa [prefixWord, tailWord_2001117, baseEnd_2001117] using wordTrace_append hprefix tailTrace_2001117
  have hstable : (prefixWord ++ tailWord_2001117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001117).length < 2 ^ (prefixWord ++ tailWord_2001117).sum := by decide
  have hdescent : baseEnd_2001117 < baseStart_2001117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001162 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_2001162 : Nat := 118140960795 + 2001162 * 2 ^ 59
def prefixEnd_2001162 : Nat := 4983230072969 + 3 ^ 40 * 2001162 * 2
def baseEnd_2001162 : Nat := 685038649008536452114553

theorem tailTrace_2001162 : CollatzResearch.WordTrace tailWord_2001162 prefixEnd_2001162 685038649008536452114553 := by
  unfold tailWord_2001162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18247093594034830026227435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48658916250759546736606493 18247093594034830026227435)
  ·
    refine ⟨27370640391052245039341153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18247093594034830026227435 27370640391052245039341153)
    ·
      refine ⟨20527980293289183779505865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27370640391052245039341153 20527980293289183779505865)
      ·
        refine ⟨15395985219966887834629399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20527980293289183779505865 15395985219966887834629399)
        ·
          refine ⟨23093977829950331751944099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15395985219966887834629399 23093977829950331751944099)
          ·
            refine ⟨34640966744925497627916149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23093977829950331751944099 34640966744925497627916149)
            ·
              refine ⟨3247590632336765402617139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34640966744925497627916149 3247590632336765402617139)
              ·
                refine ⟨4871385948505148103925709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247590632336765402617139 4871385948505148103925709)
                ·
                  refine ⟨1826769730689430538972141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4871385948505148103925709 1826769730689430538972141)
                  ·
                    refine ⟨685038649008536452114553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1826769730689430538972141 685038649008536452114553)
                    ·
                      rfl

theorem cell22_2001162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_2001162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001162 prefixEnd_2001162 := by exact prefixLift 2001162
  have htrace : WordTrace (prefixWord ++ tailWord_2001162) baseStart_2001162 baseEnd_2001162 := by
    simpa [prefixWord, tailWord_2001162, baseEnd_2001162] using wordTrace_append hprefix tailTrace_2001162
  have hstable : (prefixWord ++ tailWord_2001162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001162).length < 2 ^ (prefixWord ++ tailWord_2001162).sum := by decide
  have hdescent : baseEnd_2001162 < baseStart_2001162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001237 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 6]
def baseStart_2001237 : Nat := 118140960795 + 2001237 * 2 ^ 59
def prefixEnd_2001237 : Nat := 4983230072969 + 3 ^ 40 * 2001237 * 2
def baseEnd_2001237 : Nat := 228354774347087085496441

theorem tailTrace_2001237 : CollatzResearch.WordTrace tailWord_2001237 prefixEnd_2001237 228354774347087085496441 := by
  unfold tailWord_2001237
  simp only [CollatzResearch.WordTrace]
  refine ⟨72991109850867607913889965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48660739900578405275926643 72991109850867607913889965)
  ·
    refine ⟨27371666194075352967708737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72991109850867607913889965 27371666194075352967708737)
    ·
      refine ⟨20528749645556514725781553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27371666194075352967708737 20528749645556514725781553)
      ·
        refine ⟨15396562234167386044336165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20528749645556514725781553 15396562234167386044336165)
        ·
          refine ⟨2886855418906384883313031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15396562234167386044336165 2886855418906384883313031)
          ·
            refine ⟨4330283128359577324969547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886855418906384883313031 4330283128359577324969547)
            ·
              refine ⟨6495424692539365987454321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330283128359577324969547 6495424692539365987454321)
              ·
                refine ⟨4871568519404524490590741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6495424692539365987454321 4871568519404524490590741)
                ·
                  refine ⟨228354774347087085496441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4871568519404524490590741 228354774347087085496441)
                  ·
                    rfl

theorem cell22_2001237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_2001237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001237 prefixEnd_2001237 := by exact prefixLift 2001237
  have htrace : WordTrace (prefixWord ++ tailWord_2001237) baseStart_2001237 baseEnd_2001237 := by
    simpa [prefixWord, tailWord_2001237, baseEnd_2001237] using wordTrace_append hprefix tailTrace_2001237
  have hstable : (prefixWord ++ tailWord_2001237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001237).length < 2 ^ (prefixWord ++ tailWord_2001237).sum := by decide
  have hdescent : baseEnd_2001237 < baseStart_2001237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001252 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_2001252 : Nat := 118140960795 + 2001252 * 2 ^ 59
def prefixEnd_2001252 : Nat := 4983230072969 + 3 ^ 40 * 2001252 * 2
def baseEnd_2001252 : Nat := 685069457847806217364277

theorem tailTrace_2001252 : CollatzResearch.WordTrace tailWord_2001252 prefixEnd_2001252 685069457847806217364277 := by
  unfold tailWord_2001252
  simp only [CollatzResearch.WordTrace]
  refine ⟨36495828472906632737843005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48661104630542176983790673 36495828472906632737843005)
  ·
    refine ⟨13685935677339987276691127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36495828472906632737843005 13685935677339987276691127)
    ·
      refine ⟨20528903516009980915036691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13685935677339987276691127 20528903516009980915036691)
      ·
        refine ⟨30793355274014971372555037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20528903516009980915036691 30793355274014971372555037)
        ·
          refine ⟨11547508227755614264708139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30793355274014971372555037 11547508227755614264708139)
          ·
            refine ⟨17321262341633421397062209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547508227755614264708139 17321262341633421397062209)
            ·
              refine ⟨12990946756225066047796657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17321262341633421397062209 12990946756225066047796657)
              ·
                refine ⟨9743210067168799535847493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12990946756225066047796657 9743210067168799535847493)
                ·
                  refine ⟨1826851887594149912971405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9743210067168799535847493 1826851887594149912971405)
                  ·
                    refine ⟨685069457847806217364277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1826851887594149912971405 685069457847806217364277)
                    ·
                      rfl

theorem cell22_2001252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_2001252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001252 prefixEnd_2001252 := by exact prefixLift 2001252
  have htrace : WordTrace (prefixWord ++ tailWord_2001252) baseStart_2001252 baseEnd_2001252 := by
    simpa [prefixWord, tailWord_2001252, baseEnd_2001252] using wordTrace_append hprefix tailTrace_2001252
  have hstable : (prefixWord ++ tailWord_2001252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001252).length < 2 ^ (prefixWord ++ tailWord_2001252).sum := by decide
  have hdescent : baseEnd_2001252 < baseStart_2001252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001256 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 1, 4]
def baseStart_2001256 : Nat := 118140960795 + 2001256 * 2 ^ 59
def prefixEnd_2001256 : Nat := 4983230072969 + 3 ^ 40 * 2001256 * 2
def baseEnd_2001256 : Nat := 685070827129551540264265

theorem tailTrace_2001256 : CollatzResearch.WordTrace tailWord_2001256 prefixEnd_2001256 685070827129551540264265 := by
  unfold tailWord_2001256
  simp only [CollatzResearch.WordTrace]
  refine ⟨36495901418899387079415811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48661201891865849439221081 36495901418899387079415811)
  ·
    refine ⟨54743852128349080619123717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36495901418899387079415811 54743852128349080619123717)
    ·
      refine ⟨10264472274065452616085697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54743852128349080619123717 10264472274065452616085697)
      ·
        refine ⟨7698354205549089462064273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10264472274065452616085697 7698354205549089462064273)
        ·
          refine ⟨5773765654161817096548205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7698354205549089462064273 5773765654161817096548205)
          ·
            refine ⟨2165162120310681411205577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5773765654161817096548205 2165162120310681411205577)
            ·
              refine ⟨1623871590233011058404183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165162120310681411205577 1623871590233011058404183)
              ·
                refine ⟨2435807385349516587606275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623871590233011058404183 2435807385349516587606275)
                ·
                  refine ⟨3653711078024274881409413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435807385349516587606275 3653711078024274881409413)
                  ·
                    refine ⟨685070827129551540264265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3653711078024274881409413 685070827129551540264265)
                    ·
                      rfl

theorem cell22_2001256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_2001256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001256 prefixEnd_2001256 := by exact prefixLift 2001256
  have htrace : WordTrace (prefixWord ++ tailWord_2001256) baseStart_2001256 baseEnd_2001256 := by
    simpa [prefixWord, tailWord_2001256, baseEnd_2001256] using wordTrace_append hprefix tailTrace_2001256
  have hstable : (prefixWord ++ tailWord_2001256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001256).length < 2 ^ (prefixWord ++ tailWord_2001256).sum := by decide
  have hdescent : baseEnd_2001256 < baseStart_2001256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001269 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_2001269 : Nat := 118140960795 + 2001269 * 2 ^ 59
def prefixEnd_2001269 : Nat := 4983230072969 + 3 ^ 40 * 2001269 * 2
def baseEnd_2001269 : Nat := 685075277295223839689225

theorem tailTrace_2001269 : CollatzResearch.WordTrace tailWord_2001269 prefixEnd_2001269 685075277295223839689225 := by
  unfold tailWord_2001269
  simp only [CollatzResearch.WordTrace]
  refine ⟨72992276986751677379054861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48661517991167784919369907 72992276986751677379054861)
  ·
    refine ⟨27372103870031879017145573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72992276986751677379054861 27372103870031879017145573)
    ·
      refine ⟨5132269475630977315714795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27372103870031879017145573 5132269475630977315714795)
      ·
        refine ⟨7698404213446465973572193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132269475630977315714795 7698404213446465973572193)
        ·
          refine ⟨5773803160084849480179145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7698404213446465973572193 5773803160084849480179145)
          ·
            refine ⟨4330352370063637110134359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773803160084849480179145 4330352370063637110134359)
            ·
              refine ⟨6495528555095455665201539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330352370063637110134359 6495528555095455665201539)
              ·
                refine ⟨9743292832643183497802309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495528555095455665201539 9743292832643183497802309)
                ·
                  refine ⟨1826867406120596905837933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9743292832643183497802309 1826867406120596905837933)
                  ·
                    refine ⟨685075277295223839689225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1826867406120596905837933 685075277295223839689225)
                    ·
                      rfl

theorem cell22_2001269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_2001269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001269 prefixEnd_2001269 := by exact prefixLift 2001269
  have htrace : WordTrace (prefixWord ++ tailWord_2001269) baseStart_2001269 baseEnd_2001269 := by
    simpa [prefixWord, tailWord_2001269, baseEnd_2001269] using wordTrace_append hprefix tailTrace_2001269
  have hstable : (prefixWord ++ tailWord_2001269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001269).length < 2 ^ (prefixWord ++ tailWord_2001269).sum := by decide
  have hdescent : baseEnd_2001269 < baseStart_2001269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001342 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2001342 : Nat := 118140960795 + 2001342 * 2 ^ 59
def prefixEnd_2001342 : Nat := 4983230072969 + 3 ^ 40 * 2001342 * 2
def baseEnd_2001342 : Nat := 685100266687075982614001

theorem tailTrace_2001342 : CollatzResearch.WordTrace tailWord_2001342 prefixEnd_2001342 685100266687075982614001 := by
  unfold tailWord_2001342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124367439435901355807785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48663293010324807230974853 9124367439435901355807785)
  ·
    refine ⟨6843275579576926016855839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9124367439435901355807785 6843275579576926016855839)
    ·
      refine ⟨10264913369365389025283759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6843275579576926016855839 10264913369365389025283759)
      ·
        refine ⟨15397370054048083537925639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264913369365389025283759 15397370054048083537925639)
        ·
          refine ⟨23096055081072125306888459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15397370054048083537925639 23096055081072125306888459)
          ·
            refine ⟨34644082621608187960332689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23096055081072125306888459 34644082621608187960332689)
            ·
              refine ⟨25983061966206140970249517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34644082621608187960332689 25983061966206140970249517)
              ·
                refine ⟨9743648237327302863843569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25983061966206140970249517 9743648237327302863843569)
                ·
                  refine ⟨7307736177995477147882677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9743648237327302863843569 7307736177995477147882677)
                  ·
                    refine ⟨685100266687075982614001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7307736177995477147882677 685100266687075982614001)
                    ·
                      rfl

theorem cell22_2001342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2001342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001342 prefixEnd_2001342 := by exact prefixLift 2001342
  have htrace : WordTrace (prefixWord ++ tailWord_2001342) baseStart_2001342 baseEnd_2001342 := by
    simpa [prefixWord, tailWord_2001342, baseEnd_2001342] using wordTrace_append hprefix tailTrace_2001342
  have hstable : (prefixWord ++ tailWord_2001342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001342).length < 2 ^ (prefixWord ++ tailWord_2001342).sum := by decide
  have hdescent : baseEnd_2001342 < baseStart_2001342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001355 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 8]
def baseStart_2001355 : Nat := 118140960795 + 2001355 * 2 ^ 59
def prefixEnd_2001355 : Nat := 4983230072969 + 3 ^ 40 * 2001355 * 2
def baseEnd_2001355 : Nat := 228368238950916094012987

theorem tailTrace_2001355 : CollatzResearch.WordTrace tailWord_2001355 prefixEnd_2001355 228368238950916094012987 := by
  unfold tailWord_2001355
  simp only [CollatzResearch.WordTrace]
  refine ⟨72995413664440114066685519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48663609109626742711123679 72995413664440114066685519)
  ·
    refine ⟨109493120496660171100028279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72995413664440114066685519 109493120496660171100028279)
    ·
      refine ⟨164239680744990256650042419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109493120496660171100028279 164239680744990256650042419)
      ·
        refine ⟨246359521117485384975063629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164239680744990256650042419 246359521117485384975063629)
        ·
          refine ⟨92384820419057019365648861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246359521117485384975063629 92384820419057019365648861)
          ·
            refine ⟨34644307657146382262118323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92384820419057019365648861 34644307657146382262118323)
            ·
              refine ⟨51966461485719573393177485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34644307657146382262118323 51966461485719573393177485)
              ·
                refine ⟨19487423057144840022441557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51966461485719573393177485 19487423057144840022441557)
                ·
                  refine ⟨228368238950916094012987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19487423057144840022441557 228368238950916094012987)
                  ·
                    rfl

theorem cell22_2001355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 8].length) (baseStart_2001355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001355 prefixEnd_2001355 := by exact prefixLift 2001355
  have htrace : WordTrace (prefixWord ++ tailWord_2001355) baseStart_2001355 baseEnd_2001355 := by
    simpa [prefixWord, tailWord_2001355, baseEnd_2001355] using wordTrace_append hprefix tailTrace_2001355
  have hstable : (prefixWord ++ tailWord_2001355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001355).length < 2 ^ (prefixWord ++ tailWord_2001355).sum := by decide
  have hdescent : baseEnd_2001355 < baseStart_2001355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001378 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_2001378 : Nat := 118140960795 + 2001378 * 2 ^ 59
def prefixEnd_2001378 : Nat := 4983230072969 + 3 ^ 40 * 2001378 * 2
def baseEnd_2001378 : Nat := 228370863407594629571297

theorem tailTrace_2001378 : CollatzResearch.WordTrace tailWord_2001378 prefixEnd_2001378 228370863407594629571297 := by
  unfold tailWord_2001378
  simp only [CollatzResearch.WordTrace]
  refine ⟨18249063135839197248693197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48664168362237859329848525 18249063135839197248693197)
  ·
    refine ⟨6843398675939698968259949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18249063135839197248693197 6843398675939698968259949)
    ·
      refine ⟨2566274503477387113097481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6843398675939698968259949 2566274503477387113097481)
      ·
        refine ⟨1924705877608040334823111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2566274503477387113097481 1924705877608040334823111)
        ·
          refine ⟨2887058816412060502234667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924705877608040334823111 2887058816412060502234667)
          ·
            refine ⟨4330588224618090753352001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887058816412060502234667 4330588224618090753352001)
            ·
              refine ⟨3247941168463568065014001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330588224618090753352001 3247941168463568065014001)
              ·
                refine ⟨2435955876347676048760501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3247941168463568065014001 2435955876347676048760501)
                ·
                  refine ⟨228370863407594629571297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2435955876347676048760501 228370863407594629571297)
                  ·
                    rfl

theorem cell22_2001378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_2001378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001378 prefixEnd_2001378 := by exact prefixLift 2001378
  have htrace : WordTrace (prefixWord ++ tailWord_2001378) baseStart_2001378 baseEnd_2001378 := by
    simpa [prefixWord, tailWord_2001378, baseEnd_2001378] using wordTrace_append hprefix tailTrace_2001378
  have hstable : (prefixWord ++ tailWord_2001378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001378).length < 2 ^ (prefixWord ++ tailWord_2001378).sum := by decide
  have hdescent : baseEnd_2001378 < baseStart_2001378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001419 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 2, 4]
def baseStart_2001419 : Nat := 118140960795 + 2001419 * 2 ^ 59
def prefixEnd_2001419 : Nat := 4983230072969 + 3 ^ 40 * 2001419 * 2
def baseEnd_2001419 : Nat := 685126625360673448438765

theorem tailTrace_2001419 : CollatzResearch.WordTrace tailWord_2001419 prefixEnd_2001419 685126625360673448438765 := by
  unfold tailWord_2001419
  simp only [CollatzResearch.WordTrace]
  refine ⟨72997747936208252997015311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48665165290805501998010207 72997747936208252997015311)
  ·
    refine ⟨109496621904312379495522967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72997747936208252997015311 109496621904312379495522967)
    ·
      refine ⟨164244932856468569243284451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109496621904312379495522967 164244932856468569243284451)
      ·
        refine ⟨246367399284702853864926677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164244932856468569243284451 246367399284702853864926677)
        ·
          refine ⟨5774235920735223137459219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 246367399284702853864926677 5774235920735223137459219)
          ·
            refine ⟨8661353881102834706188829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5774235920735223137459219 8661353881102834706188829)
            ·
              refine ⟨3248007705413563014820811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8661353881102834706188829 3248007705413563014820811)
              ·
                refine ⟨4872011558120344522231217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248007705413563014820811 4872011558120344522231217)
                ·
                  refine ⟨3654008668590258391673413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872011558120344522231217 3654008668590258391673413)
                  ·
                    refine ⟨685126625360673448438765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3654008668590258391673413 685126625360673448438765)
                    ·
                      rfl

theorem cell22_2001419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 4].length) (baseStart_2001419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001419 prefixEnd_2001419 := by exact prefixLift 2001419
  have htrace : WordTrace (prefixWord ++ tailWord_2001419) baseStart_2001419 baseEnd_2001419 := by
    simpa [prefixWord, tailWord_2001419, baseEnd_2001419] using wordTrace_append hprefix tailTrace_2001419
  have hstable : (prefixWord ++ tailWord_2001419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001419).length < 2 ^ (prefixWord ++ tailWord_2001419).sum := by decide
  have hdescent : baseEnd_2001419 < baseStart_2001419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001500 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2001500 : Nat := 118140960795 + 2001500 * 2 ^ 59
def prefixEnd_2001500 : Nat := 4983230072969 + 3 ^ 40 * 2001500 * 2
def baseEnd_2001500 : Nat := 685154353316016237163517

theorem tailTrace_2001500 : CollatzResearch.WordTrace tailWord_2001500 prefixEnd_2001500 685154353316016237163517 := by
  unfold tailWord_2001500
  simp only [CollatzResearch.WordTrace]
  refine ⟨36500351124457401915356977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48667134832609869220475969 36500351124457401915356977)
  ·
    refine ⟨27375263343343051436517733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36500351124457401915356977 27375263343343051436517733)
    ·
      refine ⟨5132861876876822144347075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27375263343343051436517733 5132861876876822144347075)
      ·
        refine ⟨7699292815315233216520613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132861876876822144347075 7699292815315233216520613)
        ·
          refine ⟨1443617402871606228097615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7699292815315233216520613 1443617402871606228097615)
          ·
            refine ⟨2165426104307409342146423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443617402871606228097615 2165426104307409342146423)
            ·
              refine ⟨3248139156461114013219635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165426104307409342146423 3248139156461114013219635)
              ·
                refine ⟨4872208734691671019829453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248139156461114013219635 4872208734691671019829453)
                ·
                  refine ⟨1827078275509376632436045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4872208734691671019829453 1827078275509376632436045)
                  ·
                    refine ⟨685154353316016237163517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1827078275509376632436045 685154353316016237163517)
                    ·
                      rfl

theorem cell22_2001500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2001500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001500 prefixEnd_2001500 := by exact prefixLift 2001500
  have htrace : WordTrace (prefixWord ++ tailWord_2001500) baseStart_2001500 baseEnd_2001500 := by
    simpa [prefixWord, tailWord_2001500, baseEnd_2001500] using wordTrace_append hprefix tailTrace_2001500
  have hstable : (prefixWord ++ tailWord_2001500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001500).length < 2 ^ (prefixWord ++ tailWord_2001500).sum := by decide
  have hdescent : baseEnd_2001500 < baseStart_2001500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001539 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 6, 3]
def baseStart_2001539 : Nat := 118140960795 + 2001539 * 2 ^ 59
def prefixEnd_2001539 : Nat := 4983230072969 + 3 ^ 40 * 2001539 * 2
def baseEnd_2001539 : Nat := 685167703813033135438397

theorem tailTrace_2001539 : CollatzResearch.WordTrace tailWord_2001539 prefixEnd_2001539 685167703813033135438397 := by
  unfold tailWord_2001539
  simp only [CollatzResearch.WordTrace]
  refine ⟨73002124695773513491383671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48668083130515675660922447 73002124695773513491383671)
  ·
    refine ⟨109503187043660270237075507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73002124695773513491383671 109503187043660270237075507)
    ·
      refine ⟨164254780565490405355613261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109503187043660270237075507 164254780565490405355613261)
      ·
        refine ⟨61595542712058902008354973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164254780565490405355613261 61595542712058902008354973)
        ·
          refine ⟨23098328517022088253133115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61595542712058902008354973 23098328517022088253133115)
          ·
            refine ⟨34647492775533132379699673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23098328517022088253133115 34647492775533132379699673)
            ·
              refine ⟨25985619581649849284774755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34647492775533132379699673 25985619581649849284774755)
              ·
                refine ⟨38978429372474773927162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25985619581649849284774755 38978429372474773927162133)
                ·
                  refine ⟨1827113876834755027835725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38978429372474773927162133 1827113876834755027835725)
                  ·
                    refine ⟨685167703813033135438397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1827113876834755027835725 685167703813033135438397)
                    ·
                      rfl

theorem cell22_2001539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 3].length) (baseStart_2001539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001539 prefixEnd_2001539 := by exact prefixLift 2001539
  have htrace : WordTrace (prefixWord ++ tailWord_2001539) baseStart_2001539 baseEnd_2001539 := by
    simpa [prefixWord, tailWord_2001539, baseEnd_2001539] using wordTrace_append hprefix tailTrace_2001539
  have hstable : (prefixWord ++ tailWord_2001539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001539).length < 2 ^ (prefixWord ++ tailWord_2001539).sum := by decide
  have hdescent : baseEnd_2001539 < baseStart_2001539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001661 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_2001661 : Nat := 118140960795 + 2001661 * 2 ^ 59
def prefixEnd_2001661 : Nat := 4983230072969 + 3 ^ 40 * 2001661 * 2
def baseEnd_2001661 : Nat := 685209466906265483888023

theorem tailTrace_2001661 : CollatzResearch.WordTrace tailWord_2001661 prefixEnd_2001661 685209466906265483888023 := by
  unfold tailWord_2001661
  simp only [CollatzResearch.WordTrace]
  refine ⟨73006574401331528327324837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48671049600887685551549891 73006574401331528327324837)
  ·
    refine ⟨13688732700249661561373407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73006574401331528327324837 13688732700249661561373407)
    ·
      refine ⟨20533099050374492342060111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13688732700249661561373407 20533099050374492342060111)
      ·
        refine ⟨30799648575561738513090167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20533099050374492342060111 30799648575561738513090167)
        ·
          refine ⟨46199472863342607769635251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30799648575561738513090167 46199472863342607769635251)
          ·
            refine ⟨69299209295013911654452877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46199472863342607769635251 69299209295013911654452877)
            ·
              refine ⟨25987203485630216870419829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69299209295013911654452877 25987203485630216870419829)
              ·
                refine ⟨2436300326777832831601859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25987203485630216870419829 2436300326777832831601859)
                ·
                  refine ⟨3654450490166749247402789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436300326777832831601859 3654450490166749247402789)
                  ·
                    refine ⟨685209466906265483888023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3654450490166749247402789 685209466906265483888023)
                    ·
                      rfl

theorem cell22_2001661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_2001661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001661 prefixEnd_2001661 := by exact prefixLift 2001661
  have htrace : WordTrace (prefixWord ++ tailWord_2001661) baseStart_2001661 baseEnd_2001661 := by
    simpa [prefixWord, tailWord_2001661, baseEnd_2001661] using wordTrace_append hprefix tailTrace_2001661
  have hstable : (prefixWord ++ tailWord_2001661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001661).length < 2 ^ (prefixWord ++ tailWord_2001661).sum := by decide
  have hdescent : baseEnd_2001661 < baseStart_2001661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001682 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_2001682 : Nat := 118140960795 + 2001682 * 2 ^ 59
def prefixEnd_2001682 : Nat := 4983230072969 + 3 ^ 40 * 2001682 * 2
def baseEnd_2001682 : Nat := 228405551878476143037653

theorem tailTrace_2001682 : CollatzResearch.WordTrace tailWord_2001682 prefixEnd_2001682 228405551878476143037653 := by
  unfold tailWord_2001682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18251835083563862228459825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48671560222836965942559533 18251835083563862228459825)
  ·
    refine ⟨13688876312672896671344869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18251835083563862228459825 13688876312672896671344869)
    ·
      refine ⟨2566664308626168125877163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13688876312672896671344869 2566664308626168125877163)
      ·
        refine ⟨3849996462939252188815745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566664308626168125877163 3849996462939252188815745)
        ·
          refine ⟨2887497347204439141611809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3849996462939252188815745 2887497347204439141611809)
          ·
            refine ⟨2165623010403329356208857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887497347204439141611809 2165623010403329356208857)
            ·
              refine ⟨1624217257802497017156643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165623010403329356208857 1624217257802497017156643)
              ·
                refine ⟨2436325886703745525734965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624217257802497017156643 2436325886703745525734965)
                ·
                  refine ⟨228405551878476143037653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2436325886703745525734965 228405551878476143037653)
                  ·
                    rfl

theorem cell22_2001682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_2001682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001682 prefixEnd_2001682 := by exact prefixLift 2001682
  have htrace : WordTrace (prefixWord ++ tailWord_2001682) baseStart_2001682 baseEnd_2001682 := by
    simpa [prefixWord, tailWord_2001682, baseEnd_2001682] using wordTrace_append hprefix tailTrace_2001682
  have hstable : (prefixWord ++ tailWord_2001682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001682).length < 2 ^ (prefixWord ++ tailWord_2001682).sum := by decide
  have hdescent : baseEnd_2001682 < baseStart_2001682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001689 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_2001689 : Nat := 118140960795 + 2001689 * 2 ^ 59
def prefixEnd_2001689 : Nat := 4983230072969 + 3 ^ 40 * 2001689 * 2
def baseEnd_2001689 : Nat := 685219051878482744187937

theorem tailTrace_2001689 : CollatzResearch.WordTrace tailWord_2001689 prefixEnd_2001689 685219051878482744187937 := by
  unfold tailWord_2001689
  simp only [CollatzResearch.WordTrace]
  refine ⟨73007595645230089109344121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48671730430153392739562747 73007595645230089109344121)
  ·
    refine ⟨54755696733922566832008091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73007595645230089109344121 54755696733922566832008091)
    ·
      refine ⟨82133545100883850248012137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54755696733922566832008091 82133545100883850248012137)
      ·
        refine ⟨61600158825662887686009103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82133545100883850248012137 61600158825662887686009103)
        ·
          refine ⟨92400238238494331529013655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61600158825662887686009103 92400238238494331529013655)
          ·
            refine ⟨138600357357741497293520483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92400238238494331529013655 138600357357741497293520483)
            ·
              refine ⟨207900536036612245940280725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138600357357741497293520483 207900536036612245940280725)
              ·
                refine ⟨9745337626716199028450659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207900536036612245940280725 9745337626716199028450659)
                ·
                  refine ⟨14618006440074298542675989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9745337626716199028450659 14618006440074298542675989)
                  ·
                    refine ⟨685219051878482744187937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14618006440074298542675989 685219051878482744187937)
                    ·
                      rfl

theorem cell22_2001689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_2001689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001689 prefixEnd_2001689 := by exact prefixLift 2001689
  have htrace : WordTrace (prefixWord ++ tailWord_2001689) baseStart_2001689 baseEnd_2001689 := by
    simpa [prefixWord, tailWord_2001689, baseEnd_2001689] using wordTrace_append hprefix tailTrace_2001689
  have hstable : (prefixWord ++ tailWord_2001689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001689).length < 2 ^ (prefixWord ++ tailWord_2001689).sum := by decide
  have hdescent : baseEnd_2001689 < baseStart_2001689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001753 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 3, 3]
def baseStart_2001753 : Nat := 118140960795 + 2001753 * 2 ^ 59
def prefixEnd_2001753 : Nat := 4983230072969 + 3 ^ 40 * 2001753 * 2
def baseEnd_2001753 : Nat := 685240960386407910587741

theorem tailTrace_2001753 : CollatzResearch.WordTrace tailWord_2001753 prefixEnd_2001753 685240960386407910587741 := by
  unfold tailWord_2001753
  simp only [CollatzResearch.WordTrace]
  refine ⟨73009929916998228039673913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48673286611332152026449275 73009929916998228039673913)
  ·
    refine ⟨54757447437748671029755435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73009929916998228039673913 54757447437748671029755435)
    ·
      refine ⟨82136171156623006544633153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54757447437748671029755435 82136171156623006544633153)
      ·
        refine ⟨61602128367467254908474865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82136171156623006544633153 61602128367467254908474865)
        ·
          refine ⟨46201596275600441181356149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61602128367467254908474865 46201596275600441181356149)
          ·
            refine ⟨4331399650837541360752139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46201596275600441181356149 4331399650837541360752139)
            ·
              refine ⟨6497099476256312041128209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331399650837541360752139 6497099476256312041128209)
              ·
                refine ⟨4872824607192234030846157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497099476256312041128209 4872824607192234030846157)
                ·
                  refine ⟨1827309227697087761567309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4872824607192234030846157 1827309227697087761567309)
                  ·
                    refine ⟨685240960386407910587741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1827309227697087761567309 685240960386407910587741)
                    ·
                      rfl

theorem cell22_2001753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_2001753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001753 prefixEnd_2001753 := by exact prefixLift 2001753
  have htrace : WordTrace (prefixWord ++ tailWord_2001753) baseStart_2001753 baseEnd_2001753 := by
    simpa [prefixWord, tailWord_2001753, baseEnd_2001753] using wordTrace_append hprefix tailTrace_2001753
  have hstable : (prefixWord ++ tailWord_2001753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001753).length < 2 ^ (prefixWord ++ tailWord_2001753).sum := by decide
  have hdescent : baseEnd_2001753 < baseStart_2001753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001800 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 5]
def baseStart_2001800 : Nat := 118140960795 + 2001800 * 2 ^ 59
def prefixEnd_2001800 : Nat := 4983230072969 + 3 ^ 40 * 2001800 * 2
def baseEnd_2001800 : Nat := 228419016482305151554199

theorem tailTrace_2001800 : CollatzResearch.WordTrace tailWord_2001800 prefixEnd_2001800 228419016482305151554199 := by
  unfold tailWord_2001800
  simp only [CollatzResearch.WordTrace]
  refine ⟨36505822073913977533317427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48674429431885303377756569 36505822073913977533317427)
  ·
    refine ⟨54758733110870966299976141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36505822073913977533317427 54758733110870966299976141)
    ·
      refine ⟨20534524916576612362491053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54758733110870966299976141 20534524916576612362491053)
      ·
        refine ⟨7700446843716229635934145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20534524916576612362491053 7700446843716229635934145)
        ·
          refine ⟨5775335132787172226950609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7700446843716229635934145 5775335132787172226950609)
          ·
            refine ⟨4331501349590379170212957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775335132787172226950609 4331501349590379170212957)
            ·
              refine ⟨1624313006096392188829859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4331501349590379170212957 1624313006096392188829859)
              ·
                refine ⟨2436469509144588283244789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624313006096392188829859 2436469509144588283244789)
                ·
                  refine ⟨228419016482305151554199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2436469509144588283244789 228419016482305151554199)
                  ·
                    rfl

theorem cell22_2001800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_2001800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001800 prefixEnd_2001800 := by exact prefixLift 2001800
  have htrace : WordTrace (prefixWord ++ tailWord_2001800) baseStart_2001800 baseEnd_2001800 := by
    simpa [prefixWord, tailWord_2001800, baseEnd_2001800] using wordTrace_append hprefix tailTrace_2001800
  have hstable : (prefixWord ++ tailWord_2001800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001800).length < 2 ^ (prefixWord ++ tailWord_2001800).sum := by decide
  have hdescent : baseEnd_2001800 < baseStart_2001800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001813 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_2001813 : Nat := 118140960795 + 2001813 * 2 ^ 59
def prefixEnd_2001813 : Nat := 4983230072969 + 3 ^ 40 * 2001813 * 2
def baseEnd_2001813 : Nat := 685261499612587754087557

theorem tailTrace_2001813 : CollatzResearch.WordTrace tailWord_2001813 prefixEnd_2001813 685261499612587754087557 := by
  unfold tailWord_2001813
  simp only [CollatzResearch.WordTrace]
  refine ⟨73012118296780858286858093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48674745531187238857905395 73012118296780858286858093)
  ·
    refine ⟨27379544361292821857571785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73012118296780858286858093 27379544361292821857571785)
    ·
      refine ⟨20534658270969616393178839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27379544361292821857571785 20534658270969616393178839)
      ·
        refine ⟨30801987406454424589768259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20534658270969616393178839 30801987406454424589768259)
        ·
          refine ⟨46202981109681636884652389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30801987406454424589768259 46202981109681636884652389)
          ·
            refine ⟨8663058958065306915872323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46202981109681636884652389 8663058958065306915872323)
            ·
              refine ⟨12994588437097960373808485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663058958065306915872323 12994588437097960373808485)
              ·
                refine ⟨2436485331955867570089091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12994588437097960373808485 2436485331955867570089091)
                ·
                  refine ⟨3654727997933801355133637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436485331955867570089091 3654727997933801355133637)
                  ·
                    refine ⟨685261499612587754087557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3654727997933801355133637 685261499612587754087557)
                    ·
                      rfl

theorem cell22_2001813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_2001813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001813 prefixEnd_2001813 := by exact prefixLift 2001813
  have htrace : WordTrace (prefixWord ++ tailWord_2001813) baseStart_2001813 baseEnd_2001813 := by
    simpa [prefixWord, tailWord_2001813, baseEnd_2001813] using wordTrace_append hprefix tailTrace_2001813
  have hstable : (prefixWord ++ tailWord_2001813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001813).length < 2 ^ (prefixWord ++ tailWord_2001813).sum := by decide
  have hdescent : baseEnd_2001813 < baseStart_2001813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001856 : List Nat := [2, 1, 1, 2, 3, 3, 1, 9]
def baseStart_2001856 : Nat := 118140960795 + 2001856 * 2 ^ 59
def prefixEnd_2001856 : Nat := 4983230072969 + 3 ^ 40 * 2001856 * 2
def baseEnd_2001856 : Nat := 76141802154594441695825

theorem tailTrace_2001856 : CollatzResearch.WordTrace tailWord_2001856 prefixEnd_2001856 76141802154594441695825 := by
  unfold tailWord_2001856
  simp only [CollatzResearch.WordTrace]
  refine ⟨36506843317812538315336711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48675791090416717753782281 36506843317812538315336711)
  ·
    refine ⟨54760264976718807473005067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36506843317812538315336711 54760264976718807473005067)
    ·
      refine ⟨82140397465078211209507601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54760264976718807473005067 82140397465078211209507601)
      ·
        refine ⟨61605298098808658407130701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82140397465078211209507601 61605298098808658407130701)
        ·
          refine ⟨23101986787053246902674013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61605298098808658407130701 23101986787053246902674013)
          ·
            refine ⟨8663245045144967588502755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23101986787053246902674013 8663245045144967588502755)
            ·
              refine ⟨12994867567717451382754133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663245045144967588502755 12994867567717451382754133)
              ·
                refine ⟨76141802154594441695825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12994867567717451382754133 76141802154594441695825)
                ·
                  rfl

theorem cell22_2001856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 9].length) (baseStart_2001856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001856 prefixEnd_2001856 := by exact prefixLift 2001856
  have htrace : WordTrace (prefixWord ++ tailWord_2001856) baseStart_2001856 baseEnd_2001856 := by
    simpa [prefixWord, tailWord_2001856, baseEnd_2001856] using wordTrace_append hprefix tailTrace_2001856
  have hstable : (prefixWord ++ tailWord_2001856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001856).length < 2 ^ (prefixWord ++ tailWord_2001856).sum := by decide
  have hdescent : baseEnd_2001856 < baseStart_2001856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001963 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 6]
def baseStart_2001963 : Nat := 118140960795 + 2001963 * 2 ^ 59
def prefixEnd_2001963 : Nat := 4983230072969 + 3 ^ 40 * 2001963 * 2
def baseEnd_2001963 : Nat := 228437615892679120945699

theorem tailTrace_2001963 : CollatzResearch.WordTrace tailWord_2001963 prefixEnd_2001963 228437615892679120945699 := by
  unfold tailWord_2001963
  simp only [CollatzResearch.WordTrace]
  refine ⟨73017589246237433904818543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48678392830824955936545695 73017589246237433904818543)
  ·
    refine ⟨109526383869356150857227815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73017589246237433904818543 109526383869356150857227815)
    ·
      refine ⟨164289575804034226285841723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109526383869356150857227815 164289575804034226285841723)
      ·
        refine ⟨246434363706051339428762585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164289575804034226285841723 246434363706051339428762585)
        ·
          refine ⟨184825772779538504571571939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246434363706051339428762585 184825772779538504571571939)
          ·
            refine ⟨277238659169307756857357909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184825772779538504571571939 277238659169307756857357909)
            ·
              refine ⟨3248890537140325275672163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 277238659169307756857357909 3248890537140325275672163)
              ·
                refine ⟨4873335805710487913508245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248890537140325275672163 4873335805710487913508245)
                ·
                  refine ⟨228437615892679120945699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4873335805710487913508245 228437615892679120945699)
                  ·
                    rfl

theorem cell22_2001963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 6].length) (baseStart_2001963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001963 prefixEnd_2001963 := by exact prefixLift 2001963
  have htrace : WordTrace (prefixWord ++ tailWord_2001963) baseStart_2001963 baseEnd_2001963 := by
    simpa [prefixWord, tailWord_2001963, baseEnd_2001963] using wordTrace_append hprefix tailTrace_2001963
  have hstable : (prefixWord ++ tailWord_2001963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001963).length < 2 ^ (prefixWord ++ tailWord_2001963).sum := by decide
  have hdescent : baseEnd_2001963 < baseStart_2001963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001982 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2001982 : Nat := 118140960795 + 2001982 * 2 ^ 59
def prefixEnd_2001982 : Nat := 4983230072969 + 3 ^ 40 * 2001982 * 2
def baseEnd_2001982 : Nat := 685319351766327646612039

theorem tailTrace_2001982 : CollatzResearch.WordTrace tailWord_2001982 prefixEnd_2001982 685319351766327646612039 := by
  unfold tailWord_2001982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127285279146075018720025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48678854822112400099840133 9127285279146075018720025)
  ·
    refine ⟨6845463959359556264040019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9127285279146075018720025 6845463959359556264040019)
    ·
      refine ⟨10268195939039334396060029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6845463959359556264040019 10268195939039334396060029)
      ·
        refine ⟨3850573477139750398522511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10268195939039334396060029 3850573477139750398522511)
        ·
          refine ⟨5775860215709625597783767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850573477139750398522511 5775860215709625597783767)
          ·
            refine ⟨8663790323564438396675651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775860215709625597783767 8663790323564438396675651)
            ·
              refine ⟨12995685485346657595013477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663790323564438396675651 12995685485346657595013477)
              ·
                refine ⟨2436691028502498299065027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12995685485346657595013477 2436691028502498299065027)
                ·
                  refine ⟨3655036542753747448597541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436691028502498299065027 3655036542753747448597541)
                  ·
                    refine ⟨685319351766327646612039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3655036542753747448597541 685319351766327646612039)
                    ·
                      rfl

theorem cell22_2001982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2001982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2001982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2001982 prefixEnd_2001982 := by exact prefixLift 2001982
  have htrace : WordTrace (prefixWord ++ tailWord_2001982) baseStart_2001982 baseEnd_2001982 := by
    simpa [prefixWord, tailWord_2001982, baseEnd_2001982] using wordTrace_append hprefix tailTrace_2001982
  have hstable : (prefixWord ++ tailWord_2001982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001982).length < 2 ^ (prefixWord ++ tailWord_2001982).sum := by decide
  have hdescent : baseEnd_2001982 < baseStart_2001982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002012 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2002012 : Nat := 118140960795 + 2002012 * 2 ^ 59
def prefixEnd_2002012 : Nat := 4983230072969 + 3 ^ 40 * 2002012 * 2
def baseEnd_2002012 : Nat := 685329621379417568361947

theorem tailTrace_2002012 : CollatzResearch.WordTrace tailWord_2002012 prefixEnd_2002012 685329621379417568361947 := by
  unfold tailWord_2002012
  simp only [CollatzResearch.WordTrace]
  refine ⟨36509688211529957636676145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48679584282039943515568193 36509688211529957636676145)
  ·
    refine ⟨27382266158647468227507109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36509688211529957636676145 27382266158647468227507109)
    ·
      refine ⟨5134174904746400292657583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27382266158647468227507109 5134174904746400292657583)
      ·
        refine ⟨7701262357119600438986375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134174904746400292657583 7701262357119600438986375)
        ·
          refine ⟨11551893535679400658479563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701262357119600438986375 11551893535679400658479563)
          ·
            refine ⟨17327840303519100987719345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551893535679400658479563 17327840303519100987719345)
            ·
              refine ⟨12995880227639325740789509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17327840303519100987719345 12995880227639325740789509)
              ·
                refine ⟨2436727542682373576398033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12995880227639325740789509 2436727542682373576398033)
                ·
                  refine ⟨1827545657011780182298525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2436727542682373576398033 1827545657011780182298525)
                  ·
                    refine ⟨685329621379417568361947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1827545657011780182298525 685329621379417568361947)
                    ·
                      rfl

theorem cell22_2002012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2002012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002012 prefixEnd_2002012 := by exact prefixLift 2002012
  have htrace : WordTrace (prefixWord ++ tailWord_2002012) baseStart_2002012 baseEnd_2002012 := by
    simpa [prefixWord, tailWord_2002012, baseEnd_2002012] using wordTrace_append hprefix tailTrace_2002012
  have hstable : (prefixWord ++ tailWord_2002012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002012).length < 2 ^ (prefixWord ++ tailWord_2002012).sum := by decide
  have hdescent : baseEnd_2002012 < baseStart_2002012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002014 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2002014 : Nat := 118140960795 + 2002014 * 2 ^ 59
def prefixEnd_2002014 : Nat := 4983230072969 + 3 ^ 40 * 2002014 * 2
def baseEnd_2002014 : Nat := 228443435340096743270647

theorem tailTrace_2002014 : CollatzResearch.WordTrace tailWord_2002014 prefixEnd_2002014 228443435340096743270647 := by
  unfold tailWord_2002014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127431171131583701865637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48679632912701779743283397 9127431171131583701865637)
  ·
    refine ⟨1711393344587171944099807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9127431171131583701865637 1711393344587171944099807)
    ·
      refine ⟨2567090016880757916149711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711393344587171944099807 2567090016880757916149711)
      ·
        refine ⟨3850635025321136874224567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567090016880757916149711 3850635025321136874224567)
        ·
          refine ⟨5775952537981705311336851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850635025321136874224567 5775952537981705311336851)
          ·
            refine ⟨8663928806972557967005277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775952537981705311336851 8663928806972557967005277)
            ·
              refine ⟨3248973302614709237626979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8663928806972557967005277 3248973302614709237626979)
              ·
                refine ⟨4873459953922063856440469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248973302614709237626979 4873459953922063856440469)
                ·
                  refine ⟨228443435340096743270647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4873459953922063856440469 228443435340096743270647)
                  ·
                    rfl

theorem cell22_2002014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2002014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002014 prefixEnd_2002014 := by exact prefixLift 2002014
  have htrace : WordTrace (prefixWord ++ tailWord_2002014) baseStart_2002014 baseEnd_2002014 := by
    simpa [prefixWord, tailWord_2002014, baseEnd_2002014] using wordTrace_append hprefix tailTrace_2002014
  have hstable : (prefixWord ++ tailWord_2002014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002014).length < 2 ^ (prefixWord ++ tailWord_2002014).sum := by decide
  have hdescent : baseEnd_2002014 < baseStart_2002014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002029 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_2002029 : Nat := 118140960795 + 2002029 * 2 ^ 59
def prefixEnd_2002029 : Nat := 4983230072969 + 3 ^ 40 * 2002029 * 2
def baseEnd_2002029 : Nat := 685335440826835190686895

theorem tailTrace_2002029 : CollatzResearch.WordTrace tailWord_2002029 prefixEnd_2002029 685335440826835190686895 := by
  unfold tailWord_2002029
  simp only [CollatzResearch.WordTrace]
  refine ⟨73019996463998327176721141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48679997642665551451147427 73019996463998327176721141)
  ·
    refine ⟨6845624668499843172817607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73019996463998327176721141 6845624668499843172817607)
    ·
      refine ⟨10268437002749764759226411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6845624668499843172817607 10268437002749764759226411)
      ·
        refine ⟨15402655504124647138839617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10268437002749764759226411 15402655504124647138839617)
        ·
          refine ⟨11551991628093485354129713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15402655504124647138839617 11551991628093485354129713)
          ·
            refine ⟨8663993721070114015597285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11551991628093485354129713 8663993721070114015597285)
            ·
              refine ⟨1624498822700646377924491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8663993721070114015597285 1624498822700646377924491)
              ·
                refine ⟨2436748234050969566886737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624498822700646377924491 2436748234050969566886737)
                ·
                  refine ⟨1827561175538227175165053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2436748234050969566886737 1827561175538227175165053)
                  ·
                    refine ⟨685335440826835190686895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1827561175538227175165053 685335440826835190686895)
                    ·
                      rfl

theorem cell22_2002029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_2002029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002029 prefixEnd_2002029 := by exact prefixLift 2002029
  have htrace : WordTrace (prefixWord ++ tailWord_2002029) baseStart_2002029 baseEnd_2002029 := by
    simpa [prefixWord, tailWord_2002029, baseEnd_2002029] using wordTrace_append hprefix tailTrace_2002029
  have hstable : (prefixWord ++ tailWord_2002029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002029).length < 2 ^ (prefixWord ++ tailWord_2002029).sum := by decide
  have hdescent : baseEnd_2002029 < baseStart_2002029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002040 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 3, 3]
def baseStart_2002040 : Nat := 118140960795 + 2002040 * 2 ^ 59
def prefixEnd_2002040 : Nat := 4983230072969 + 3 ^ 40 * 2002040 * 2
def baseEnd_2002040 : Nat := 685339206351634828661861

theorem tailTrace_2002040 : CollatzResearch.WordTrace tailWord_2002040 prefixEnd_2002040 685339206351634828661861 := by
  unfold tailWord_2002040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36510198833479238027685787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48680265111305650703581049 36510198833479238027685787)
  ·
    refine ⟨54765298250218857041528681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36510198833479238027685787 54765298250218857041528681)
    ·
      refine ⟨41073973687664142781146511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54765298250218857041528681 41073973687664142781146511)
      ·
        refine ⟨61610960531496214171719767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41073973687664142781146511 61610960531496214171719767)
        ·
          refine ⟨92416440797244321257579651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61610960531496214171719767 92416440797244321257579651)
          ·
            refine ⟨138624661195866481886369477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92416440797244321257579651 138624661195866481886369477)
            ·
              refine ⟨25992123974224965353694277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138624661195866481886369477 25992123974224965353694277)
              ·
                refine ⟨4873523245167181003817677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25992123974224965353694277 4873523245167181003817677)
                ·
                  refine ⟨1827571216937692876431629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4873523245167181003817677 1827571216937692876431629)
                  ·
                    refine ⟨685339206351634828661861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1827571216937692876431629 685339206351634828661861)
                    ·
                      rfl

theorem cell22_2002040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_2002040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002040 prefixEnd_2002040 := by exact prefixLift 2002040
  have htrace : WordTrace (prefixWord ++ tailWord_2002040) baseStart_2002040 baseEnd_2002040 := by
    simpa [prefixWord, tailWord_2002040, baseEnd_2002040] using wordTrace_append hprefix tailTrace_2002040
  have hstable : (prefixWord ++ tailWord_2002040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002040).length < 2 ^ (prefixWord ++ tailWord_2002040).sum := by decide
  have hdescent : baseEnd_2002040 < baseStart_2002040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002046 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2002046 : Nat := 118140960795 + 2002046 * 2 ^ 59
def prefixEnd_2002046 : Nat := 4983230072969 + 3 ^ 40 * 2002046 * 2
def baseEnd_2002046 : Nat := 685341260274252813011843

theorem tailTrace_2002046 : CollatzResearch.WordTrace tailWord_2002046 prefixEnd_2002046 685341260274252813011843 := by
  unfold tailWord_2002046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127577063117092385011249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48680411003291159386726661 9127577063117092385011249)
  ·
    refine ⟨6845682797337819288758437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9127577063117092385011249 6845682797337819288758437)
    ·
      refine ⟨1283565524500841116642207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6845682797337819288758437 1283565524500841116642207)
      ·
        refine ⟨1925348286751261674963311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283565524500841116642207 1925348286751261674963311)
        ·
          refine ⟨2888022430126892512444967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925348286751261674963311 2888022430126892512444967)
          ·
            refine ⟨4332033645190338768667451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888022430126892512444967 4332033645190338768667451)
            ·
              refine ⟨6498050467785508153001177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332033645190338768667451 6498050467785508153001177)
              ·
                refine ⟨4873537850839131114750883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498050467785508153001177 4873537850839131114750883)
                ·
                  refine ⟨7310306776258696672126325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873537850839131114750883 7310306776258696672126325)
                  ·
                    refine ⟨685341260274252813011843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7310306776258696672126325 685341260274252813011843)
                    ·
                      rfl

theorem cell22_2002046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2002046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002046 prefixEnd_2002046 := by exact prefixLift 2002046
  have htrace : WordTrace (prefixWord ++ tailWord_2002046) baseStart_2002046 baseEnd_2002046 := by
    simpa [prefixWord, tailWord_2002046, baseEnd_2002046] using wordTrace_append hprefix tailTrace_2002046
  have hstable : (prefixWord ++ tailWord_2002046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002046).length < 2 ^ (prefixWord ++ tailWord_2002046).sum := by decide
  have hdescent : baseEnd_2002046 < baseStart_2002046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002085 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_2002085 : Nat := 118140960795 + 2002085 * 2 ^ 59
def prefixEnd_2002085 : Nat := 4983230072969 + 3 ^ 40 * 2002085 * 2
def baseEnd_2002085 : Nat := 685354610771269711286723

theorem tailTrace_2002085 : CollatzResearch.WordTrace tailWord_2002085 prefixEnd_2002085 685354610771269711286723 := by
  unfold tailWord_2002085
  simp only [CollatzResearch.WordTrace]
  refine ⟨73022038951795448740759709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48681359301196965827173139 73022038951795448740759709)
  ·
    refine ⟨27383264606923293277784891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73022038951795448740759709 27383264606923293277784891)
    ·
      refine ⟨41074896910384939916677337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27383264606923293277784891 41074896910384939916677337)
      ·
        refine ⟨30806172682788704937508003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41074896910384939916677337 30806172682788704937508003)
        ·
          refine ⟨46209259024183057406262005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30806172682788704937508003 46209259024183057406262005)
          ·
            refine ⟨4332118033517161631837063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46209259024183057406262005 4332118033517161631837063)
            ·
              refine ⟨6498177050275742447755595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332118033517161631837063 6498177050275742447755595)
              ·
                refine ⟨9747265575413613671633393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498177050275742447755595 9747265575413613671633393)
                ·
                  refine ⟨7310449181560210253725045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9747265575413613671633393 7310449181560210253725045)
                  ·
                    refine ⟨685354610771269711286723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7310449181560210253725045 685354610771269711286723)
                    ·
                      rfl

theorem cell22_2002085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_2002085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002085 prefixEnd_2002085 := by exact prefixLift 2002085
  have htrace : WordTrace (prefixWord ++ tailWord_2002085) baseStart_2002085 baseEnd_2002085 := by
    simpa [prefixWord, tailWord_2002085, baseEnd_2002085] using wordTrace_append hprefix tailTrace_2002085
  have hstable : (prefixWord ++ tailWord_2002085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002085).length < 2 ^ (prefixWord ++ tailWord_2002085).sum := by decide
  have hdescent : baseEnd_2002085 < baseStart_2002085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002087 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 5]
def baseStart_2002087 : Nat := 118140960795 + 2002087 * 2 ^ 59
def prefixEnd_2002087 : Nat := 4983230072969 + 3 ^ 40 * 2002087 * 2
def baseEnd_2002087 : Nat := 228451765137380790912239

theorem tailTrace_2002087 : CollatzResearch.WordTrace tailWord_2002087 prefixEnd_2002087 228451765137380790912239 := by
  unfold tailWord_2002087
  simp only [CollatzResearch.WordTrace]
  refine ⟨73022111897788203082332515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48681407931858802054888343 73022111897788203082332515)
  ·
    refine ⟨109533167846682304623498773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73022111897788203082332515 109533167846682304623498773)
    ·
      refine ⟨5134367242813233029226505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109533167846682304623498773 5134367242813233029226505)
      ·
        refine ⟨3850775432109924771919879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5134367242813233029226505 3850775432109924771919879)
        ·
          refine ⟨5776163148164887157879819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850775432109924771919879 5776163148164887157879819)
          ·
            refine ⟨8664244722247330736819729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5776163148164887157879819 8664244722247330736819729)
            ·
              refine ⟨6498183541685498052614797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8664244722247330736819729 6498183541685498052614797)
              ·
                refine ⟨2436818828132061769730549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6498183541685498052614797 2436818828132061769730549)
                ·
                  refine ⟨228451765137380790912239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2436818828132061769730549 228451765137380790912239)
                  ·
                    rfl

theorem cell22_2002087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 5].length) (baseStart_2002087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002087 prefixEnd_2002087 := by exact prefixLift 2002087
  have htrace : WordTrace (prefixWord ++ tailWord_2002087) baseStart_2002087 baseEnd_2002087 := by
    simpa [prefixWord, tailWord_2002087, baseEnd_2002087] using wordTrace_append hprefix tailTrace_2002087
  have hstable : (prefixWord ++ tailWord_2002087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002087).length < 2 ^ (prefixWord ++ tailWord_2002087).sum := by decide
  have hdescent : baseEnd_2002087 < baseStart_2002087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002145 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_2002145 : Nat := 118140960795 + 2002145 * 2 ^ 59
def prefixEnd_2002145 : Nat := 4983230072969 + 3 ^ 40 * 2002145 * 2
def baseEnd_2002145 : Nat := 685375149997449554786539

theorem tailTrace_2002145 : CollatzResearch.WordTrace tailWord_2002145 prefixEnd_2002145 685375149997449554786539 := by
  unfold tailWord_2002145
  simp only [CollatzResearch.WordTrace]
  refine ⟨73024227331578078987943889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48682818221052052658629259 73024227331578078987943889)
  ·
    refine ⟨54768170498683559240957917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73024227331578078987943889 54768170498683559240957917)
    ·
      refine ⟨20538063937006334715359219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54768170498683559240957917 20538063937006334715359219)
      ·
        refine ⟨30807095905509502073038829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20538063937006334715359219 30807095905509502073038829)
        ·
          refine ⟨11552660964566063277389561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30807095905509502073038829 11552660964566063277389561)
          ·
            refine ⟨8664495723424547458042171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11552660964566063277389561 8664495723424547458042171)
            ·
              refine ⟨12996743585136821187063257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8664495723424547458042171 12996743585136821187063257)
              ·
                refine ⟨9747557688852615890297443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12996743585136821187063257 9747557688852615890297443)
                ·
                  refine ⟨14621336533278923835446165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9747557688852615890297443 14621336533278923835446165)
                  ·
                    refine ⟨685375149997449554786539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14621336533278923835446165 685375149997449554786539)
                    ·
                      rfl

theorem cell22_2002145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_2002145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002145 prefixEnd_2002145 := by exact prefixLift 2002145
  have htrace : WordTrace (prefixWord ++ tailWord_2002145) baseStart_2002145 baseEnd_2002145 := by
    simpa [prefixWord, tailWord_2002145, baseEnd_2002145] using wordTrace_append hprefix tailTrace_2002145
  have hstable : (prefixWord ++ tailWord_2002145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002145).length < 2 ^ (prefixWord ++ tailWord_2002145).sum := by decide
  have hdescent : baseEnd_2002145 < baseStart_2002145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002220 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_2002220 : Nat := 118140960795 + 2002220 * 2 ^ 59
def prefixEnd_2002220 : Nat := 4983230072969 + 3 ^ 40 * 2002220 * 2
def baseEnd_2002220 : Nat := 685400824030174359161309

theorem tailTrace_2002220 : CollatzResearch.WordTrace tailWord_2002220 prefixEnd_2002220 685400824030174359161309 := by
  unfold tailWord_2002220
  simp only [CollatzResearch.WordTrace]
  refine ⟨36513481403153183398462057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48684641870870911197949409 36513481403153183398462057)
  ·
    refine ⟨27385111052364887548846543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36513481403153183398462057 27385111052364887548846543)
    ·
      refine ⟨41077666578547331323269815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27385111052364887548846543 41077666578547331323269815)
      ·
        refine ⟨61616499867820996984904723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41077666578547331323269815 61616499867820996984904723)
        ·
          refine ⟨92424749801731495477357085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61616499867820996984904723 92424749801731495477357085)
          ·
            refine ⟨34659281175649310804008907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92424749801731495477357085 34659281175649310804008907)
            ·
              refine ⟨51988921763473966206013361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34659281175649310804008907 51988921763473966206013361)
              ·
                refine ⟨38991691322605474654510021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51988921763473966206013361 38991691322605474654510021)
                ·
                  refine ⟨7310942122988526497720629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38991691322605474654510021 7310942122988526497720629)
                  ·
                    refine ⟨685400824030174359161309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7310942122988526497720629 685400824030174359161309)
                    ·
                      rfl

theorem cell22_2002220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_2002220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002220 prefixEnd_2002220 := by exact prefixLift 2002220
  have htrace : WordTrace (prefixWord ++ tailWord_2002220) baseStart_2002220 baseEnd_2002220 := by
    simpa [prefixWord, tailWord_2002220, baseEnd_2002220] using wordTrace_append hprefix tailTrace_2002220
  have hstable : (prefixWord ++ tailWord_2002220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002220).length < 2 ^ (prefixWord ++ tailWord_2002220).sum := by decide
  have hdescent : baseEnd_2002220 < baseStart_2002220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002250 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_2002250 : Nat := 118140960795 + 2002250 * 2 ^ 59
def prefixEnd_2002250 : Nat := 4983230072969 + 3 ^ 40 * 2002250 * 2
def baseEnd_2002250 : Nat := 228470364547754760303739

theorem tailTrace_2002250 : CollatzResearch.WordTrace tailWord_2002250 prefixEnd_2002250 228470364547754760303739 := by
  unfold tailWord_2002250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18257014249049420480129051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48685371330798454613677469 18257014249049420480129051)
  ·
    refine ⟨27385521373574130720193577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18257014249049420480129051 27385521373574130720193577)
    ·
      refine ⟨20539141030180598040145183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27385521373574130720193577 20539141030180598040145183)
      ·
        refine ⟨30808711545270897060217775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20539141030180598040145183 30808711545270897060217775)
        ·
          refine ⟨46213067317906345590326663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30808711545270897060217775 46213067317906345590326663)
          ·
            refine ⟨69319600976859518385489995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46213067317906345590326663 69319600976859518385489995)
            ·
              refine ⟨103979401465289277578234993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69319600976859518385489995 103979401465289277578234993)
              ·
                refine ⟨77984551098966958183676245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103979401465289277578234993 77984551098966958183676245)
                ·
                  refine ⟨228470364547754760303739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 77984551098966958183676245 228470364547754760303739)
                  ·
                    rfl

theorem cell22_2002250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_2002250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002250 prefixEnd_2002250 := by exact prefixLift 2002250
  have htrace : WordTrace (prefixWord ++ tailWord_2002250) baseStart_2002250 baseEnd_2002250 := by
    simpa [prefixWord, tailWord_2002250, baseEnd_2002250] using wordTrace_append hprefix tailTrace_2002250
  have hstable : (prefixWord ++ tailWord_2002250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002250).length < 2 ^ (prefixWord ++ tailWord_2002250).sum := by decide
  have hdescent : baseEnd_2002250 < baseStart_2002250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002252 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_2002252 : Nat := 118140960795 + 2002252 * 2 ^ 59
def prefixEnd_2002252 : Nat := 4983230072969 + 3 ^ 40 * 2002252 * 2
def baseEnd_2002252 : Nat := 685411778284136942361211

theorem tailTrace_2002252 : CollatzResearch.WordTrace tailWord_2002252 prefixEnd_2002252 685411778284136942361211 := by
  unfold tailWord_2002252
  simp only [CollatzResearch.WordTrace]
  refine ⟨36514064971095218131044505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48685419961460290841392673 36514064971095218131044505)
  ·
    refine ⟨27385548728321413598283379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36514064971095218131044505 27385548728321413598283379)
    ·
      refine ⟨41078323092482120397425069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27385548728321413598283379 41078323092482120397425069)
      ·
        refine ⟨15404371159680795149034401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41078323092482120397425069 15404371159680795149034401)
        ·
          refine ⟨11553278369760596361775801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15404371159680795149034401 11553278369760596361775801)
          ·
            refine ⟨8664958777320447271331851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11553278369760596361775801 8664958777320447271331851)
            ·
              refine ⟨12997438165980670906997777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8664958777320447271331851 12997438165980670906997777)
              ·
                refine ⟨9748078624485503180248333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12997438165980670906997777 9748078624485503180248333)
                ·
                  refine ⟨3655529484182063692593125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9748078624485503180248333 3655529484182063692593125)
                  ·
                    refine ⟨685411778284136942361211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3655529484182063692593125 685411778284136942361211)
                    ·
                      rfl

theorem cell22_2002252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_2002252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002252 prefixEnd_2002252 := by exact prefixLift 2002252
  have htrace : WordTrace (prefixWord ++ tailWord_2002252) baseStart_2002252 baseEnd_2002252 := by
    simpa [prefixWord, tailWord_2002252, baseEnd_2002252] using wordTrace_append hprefix tailTrace_2002252
  have hstable : (prefixWord ++ tailWord_2002252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002252).length < 2 ^ (prefixWord ++ tailWord_2002252).sum := by decide
  have hdescent : baseEnd_2002252 < baseStart_2002252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002284 : List Nat := [2, 2, 1, 1, 5, 1, 1, 5, 4]
def baseStart_2002284 : Nat := 118140960795 + 2002284 * 2 ^ 59
def prefixEnd_2002284 : Nat := 4983230072969 + 3 ^ 40 * 2002284 * 2
def baseEnd_2002284 : Nat := 228474244179366508520371

theorem tailTrace_2002284 : CollatzResearch.WordTrace tailWord_2002284 prefixEnd_2002284 228474244179366508520371 := by
  unfold tailWord_2002284
  simp only [CollatzResearch.WordTrace]
  refine ⟨36514648539037252863626953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48686198052049670484835937 36514648539037252863626953)
  ·
    refine ⟨27385986404277939647720215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36514648539037252863626953 27385986404277939647720215)
    ·
      refine ⟨41078979606416909471580323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27385986404277939647720215 41078979606416909471580323)
      ·
        refine ⟨61618469409625364207370485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41078979606416909471580323 61618469409625364207370485)
        ·
          refine ⟨5776731507152377894440983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61618469409625364207370485 5776731507152377894440983)
          ·
            refine ⟨8665097260728566841661475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5776731507152377894440983 8665097260728566841661475)
            ·
              refine ⟨12997645891092850262492213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8665097260728566841661475 12997645891092850262492213)
              ·
                refine ⟨1218529302289954712108645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12997645891092850262492213 1218529302289954712108645)
                ·
                  refine ⟨228474244179366508520371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1218529302289954712108645 228474244179366508520371)
                  ·
                    rfl

theorem cell22_2002284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_2002284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002284 prefixEnd_2002284 := by exact prefixLift 2002284
  have htrace : WordTrace (prefixWord ++ tailWord_2002284) baseStart_2002284 baseEnd_2002284 := by
    simpa [prefixWord, tailWord_2002284, baseEnd_2002284] using wordTrace_append hprefix tailTrace_2002284
  have hstable : (prefixWord ++ tailWord_2002284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002284).length < 2 ^ (prefixWord ++ tailWord_2002284).sum := by decide
  have hdescent : baseEnd_2002284 < baseStart_2002284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002295 : List Nat := [1, 1, 3, 1, 1, 2, 13]
def baseStart_2002295 : Nat := 118140960795 + 2002295 * 2 ^ 59
def prefixEnd_2002295 : Nat := 4983230072969 + 3 ^ 40 * 2002295 * 2
def baseEnd_2002295 : Nat := 25386166594922191242077

theorem tailTrace_2002295 : CollatzResearch.WordTrace tailWord_2002295 prefixEnd_2002295 25386166594922191242077 := by
  unfold tailWord_2002295
  simp only [CollatzResearch.WordTrace]
  refine ⟨73029698281034654605904339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48686465520689769737269559 73029698281034654605904339)
  ·
    refine ⟨109544547421551981908856509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73029698281034654605904339 109544547421551981908856509)
    ·
      refine ⟨41079205283081993215821191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109544547421551981908856509 41079205283081993215821191)
      ·
        refine ⟨61618807924622989823731787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41079205283081993215821191 61618807924622989823731787)
        ·
          refine ⟨92428211886934484735597681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61618807924622989823731787 92428211886934484735597681)
          ·
            refine ⟨69321158915200863551698261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92428211886934484735597681 69321158915200863551698261)
            ·
              refine ⟨25386166594922191242077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 69321158915200863551698261 25386166594922191242077)
              ·
                rfl

theorem cell22_2002295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 13].length) (baseStart_2002295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002295 prefixEnd_2002295 := by exact prefixLift 2002295
  have htrace : WordTrace (prefixWord ++ tailWord_2002295) baseStart_2002295 baseEnd_2002295 := by
    simpa [prefixWord, tailWord_2002295, baseEnd_2002295] using wordTrace_append hprefix tailTrace_2002295
  have hstable : (prefixWord ++ tailWord_2002295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002295).length < 2 ^ (prefixWord ++ tailWord_2002295).sum := by decide
  have hdescent : baseEnd_2002295 < baseStart_2002295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002297 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_2002297 : Nat := 118140960795 + 2002297 * 2 ^ 59
def prefixEnd_2002297 : Nat := 4983230072969 + 3 ^ 40 * 2002297 * 2
def baseEnd_2002297 : Nat := 685427182703771824986073

theorem tailTrace_2002297 : CollatzResearch.WordTrace tailWord_2002297 prefixEnd_2002297 685427182703771824986073 := by
  unfold tailWord_2002297
  simp only [CollatzResearch.WordTrace]
  refine ⟨73029771227027408947477145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48686514151351605964984763 73029771227027408947477145)
  ·
    refine ⟨54772328420270556710607859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73029771227027408947477145 54772328420270556710607859)
    ·
      refine ⟨82158492630405835065911789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54772328420270556710607859 82158492630405835065911789)
      ·
        refine ⟨30809434736402188149716921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82158492630405835065911789 30809434736402188149716921)
        ·
          refine ⟨23107076052301641112287691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30809434736402188149716921 23107076052301641112287691)
          ·
            refine ⟨34660614078452461668431537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23107076052301641112287691 34660614078452461668431537)
            ·
              refine ⟨25995460558839346251323653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34660614078452461668431537 25995460558839346251323653)
              ·
                refine ⟨4874148854782377422123185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25995460558839346251323653 4874148854782377422123185)
                ·
                  refine ⟨3655611641086783066592389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874148854782377422123185 3655611641086783066592389)
                  ·
                    refine ⟨685427182703771824986073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3655611641086783066592389 685427182703771824986073)
                    ·
                      rfl

theorem cell22_2002297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_2002297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002297 prefixEnd_2002297 := by exact prefixLift 2002297
  have htrace : WordTrace (prefixWord ++ tailWord_2002297) baseStart_2002297 baseEnd_2002297 := by
    simpa [prefixWord, tailWord_2002297, baseEnd_2002297] using wordTrace_append hprefix tailTrace_2002297
  have hstable : (prefixWord ++ tailWord_2002297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002297).length < 2 ^ (prefixWord ++ tailWord_2002297).sum := by decide
  have hdescent : baseEnd_2002297 < baseStart_2002297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002316 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_2002316 : Nat := 118140960795 + 2002316 * 2 ^ 59
def prefixEnd_2002316 : Nat := 4983230072969 + 3 ^ 40 * 2002316 * 2
def baseEnd_2002316 : Nat := 685433686792062108761015

theorem tailTrace_2002316 : CollatzResearch.WordTrace tailWord_2002316 prefixEnd_2002316 685433686792062108761015 := by
  unfold tailWord_2002316
  simp only [CollatzResearch.WordTrace]
  refine ⟨36515232106979287596209401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48686976142639050128279201 36515232106979287596209401)
  ·
    refine ⟨27386424080234465697157051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36515232106979287596209401 27386424080234465697157051)
    ·
      refine ⟨41079636120351698545735577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27386424080234465697157051 41079636120351698545735577)
      ·
        refine ⟨30809727090263773909301683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41079636120351698545735577 30809727090263773909301683)
        ·
          refine ⟨46214590635395660863952525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30809727090263773909301683 46214590635395660863952525)
          ·
            refine ⟨17330471488273372823982197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46214590635395660863952525 17330471488273372823982197)
            ·
              refine ⟨1624731702025628702248331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17330471488273372823982197 1624731702025628702248331)
              ·
                refine ⟨2437097553038443053372497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624731702025628702248331 2437097553038443053372497)
                ·
                  refine ⟨1827823164778832290029373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437097553038443053372497 1827823164778832290029373)
                  ·
                    refine ⟨685433686792062108761015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1827823164778832290029373 685433686792062108761015)
                    ·
                      rfl

theorem cell22_2002316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_2002316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002316 prefixEnd_2002316 := by exact prefixLift 2002316
  have htrace : WordTrace (prefixWord ++ tailWord_2002316) baseStart_2002316 baseEnd_2002316 := by
    simpa [prefixWord, tailWord_2002316, baseEnd_2002316] using wordTrace_append hprefix tailTrace_2002316
  have hstable : (prefixWord ++ tailWord_2002316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002316).length < 2 ^ (prefixWord ++ tailWord_2002316).sum := by decide
  have hdescent : baseEnd_2002316 < baseStart_2002316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002329 : List Nat := [1, 2, 1, 2, 1, 7, 2, 6]
def baseStart_2002329 : Nat := 118140960795 + 2002329 * 2 ^ 59
def prefixEnd_2002329 : Nat := 4983230072969 + 3 ^ 40 * 2002329 * 2
def baseEnd_2002329 : Nat := 76159792995303823131775

theorem tailTrace_2002329 : CollatzResearch.WordTrace tailWord_2002329 prefixEnd_2002329 76159792995303823131775 := by
  unfold tailWord_2002329
  simp only [CollatzResearch.WordTrace]
  refine ⟨73030938362911478412642041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48687292241940985608428027 73030938362911478412642041)
  ·
    refine ⟨54773203772183608809481531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73030938362911478412642041 54773203772183608809481531)
    ·
      refine ⟨82159805658275413214222297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54773203772183608809481531 82159805658275413214222297)
      ·
        refine ⟨61619854243706559910666723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82159805658275413214222297 61619854243706559910666723)
        ·
          refine ⟨92429781365559839866000085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61619854243706559910666723 92429781365559839866000085)
          ·
            refine ⟨2166323000755308746859377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 92429781365559839866000085 2166323000755308746859377)
            ·
              refine ⟨1624742250566481560144533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166323000755308746859377 1624742250566481560144533)
              ·
                refine ⟨76159792995303823131775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1624742250566481560144533 76159792995303823131775)
                ·
                  rfl

theorem cell22_2002329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 6].length) (baseStart_2002329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002329 prefixEnd_2002329 := by exact prefixLift 2002329
  have htrace : WordTrace (prefixWord ++ tailWord_2002329) baseStart_2002329 baseEnd_2002329 := by
    simpa [prefixWord, tailWord_2002329, baseEnd_2002329] using wordTrace_append hprefix tailTrace_2002329
  have hstable : (prefixWord ++ tailWord_2002329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002329).length < 2 ^ (prefixWord ++ tailWord_2002329).sum := by decide
  have hdescent : baseEnd_2002329 < baseStart_2002329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002404 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_2002404 : Nat := 118140960795 + 2002404 * 2 ^ 59
def prefixEnd_2002404 : Nat := 4983230072969 + 3 ^ 40 * 2002404 * 2
def baseEnd_2002404 : Nat := 685463810990459212560745

theorem tailTrace_2002404 : CollatzResearch.WordTrace tailWord_2002404 prefixEnd_2002404 685463810990459212560745 := by
  unfold tailWord_2002404
  simp only [CollatzResearch.WordTrace]
  refine ⟨36516836918819883110811133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48689115891759844147748177 36516836918819883110811133)
  ·
    refine ⟨13693813844557456166554175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36516836918819883110811133 13693813844557456166554175)
    ·
      refine ⟨20540720766836184249831263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13693813844557456166554175 20540720766836184249831263)
      ·
        refine ⟨30811081150254276374746895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20540720766836184249831263 30811081150254276374746895)
        ·
          refine ⟨46216621725381414562120343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30811081150254276374746895 46216621725381414562120343)
          ·
            refine ⟨69324932588072121843180515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46216621725381414562120343 69324932588072121843180515)
            ·
              refine ⟨103987398882108182764770773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69324932588072121843180515 103987398882108182764770773)
              ·
                refine ⟨2437204661299410533549315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103987398882108182764770773 2437204661299410533549315)
                ·
                  refine ⟨3655806991949115800323973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437204661299410533549315 3655806991949115800323973)
                  ·
                    refine ⟨685463810990459212560745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3655806991949115800323973 685463810990459212560745)
                    ·
                      rfl

theorem cell22_2002404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_2002404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002404 prefixEnd_2002404 := by exact prefixLift 2002404
  have htrace : WordTrace (prefixWord ++ tailWord_2002404) baseStart_2002404 baseEnd_2002404 := by
    simpa [prefixWord, tailWord_2002404, baseEnd_2002404] using wordTrace_append hprefix tailTrace_2002404
  have hstable : (prefixWord ++ tailWord_2002404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002404).length < 2 ^ (prefixWord ++ tailWord_2002404).sum := by decide
  have hdescent : baseEnd_2002404 < baseStart_2002404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002421 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2002421 : Nat := 118140960795 + 2002421 * 2 ^ 59
def prefixEnd_2002421 : Nat := 4983230072969 + 3 ^ 40 * 2002421 * 2
def baseEnd_2002421 : Nat := 685469630437876834885693

theorem tailTrace_2002421 : CollatzResearch.WordTrace tailWord_2002421 prefixEnd_2002421 685469630437876834885693 := by
  unfold tailWord_2002421
  simp only [CollatzResearch.WordTrace]
  refine ⟨73034293878578178124991117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48689529252385452083327411 73034293878578178124991117)
  ·
    refine ⟨27387860204466816796871669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73034293878578178124991117 27387860204466816796871669)
    ·
      refine ⟨2567611894168764074706719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27387860204466816796871669 2567611894168764074706719)
      ·
        refine ⟨3851417841253146112060079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567611894168764074706719 3851417841253146112060079)
        ·
          refine ⟨5777126761879719168090119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851417841253146112060079 5777126761879719168090119)
          ·
            refine ⟨8665690142819578752135179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777126761879719168090119 8665690142819578752135179)
            ·
              refine ⟨12998535214229368128202769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8665690142819578752135179 12998535214229368128202769)
              ·
                refine ⟨9748901410672026096152077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12998535214229368128202769 9748901410672026096152077)
                ·
                  refine ⟨3655838029002009786057029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9748901410672026096152077 3655838029002009786057029)
                  ·
                    refine ⟨685469630437876834885693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3655838029002009786057029 685469630437876834885693)
                    ·
                      rfl

theorem cell22_2002421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2002421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002421 prefixEnd_2002421 := by exact prefixLift 2002421
  have htrace : WordTrace (prefixWord ++ tailWord_2002421) baseStart_2002421 baseEnd_2002421 := by
    simpa [prefixWord, tailWord_2002421, baseEnd_2002421] using wordTrace_append hprefix tailTrace_2002421
  have hstable : (prefixWord ++ tailWord_2002421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002421).length < 2 ^ (prefixWord ++ tailWord_2002421).sum := by decide
  have hdescent : baseEnd_2002421 < baseStart_2002421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002436 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 6]
def baseStart_2002436 : Nat := 118140960795 + 2002436 * 2 ^ 59
def prefixEnd_2002436 : Nat := 4983230072969 + 3 ^ 40 * 2002436 * 2
def baseEnd_2002436 : Nat := 228491588414807265253549

theorem tailTrace_2002436 : CollatzResearch.WordTrace tailWord_2002436 prefixEnd_2002436 228491588414807265253549 := by
  unfold tailWord_2002436
  simp only [CollatzResearch.WordTrace]
  refine ⟨36517420486761917843393581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48689893982349223791191441 36517420486761917843393581)
  ·
    refine ⟨13694032682535719191272593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36517420486761917843393581 13694032682535719191272593)
    ·
      refine ⟨10270524511901789393454445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13694032682535719191272593 10270524511901789393454445)
      ·
        refine ⟨3851446691963171022545417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10270524511901789393454445 3851446691963171022545417)
        ·
          refine ⟨2888585018972378266909063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3851446691963171022545417 2888585018972378266909063)
          ·
            refine ⟨4332877528458567400363595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888585018972378266909063 4332877528458567400363595)
            ·
              refine ⟨6499316292687851100545393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332877528458567400363595 6499316292687851100545393)
              ·
                refine ⟨4874487219515888325409045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6499316292687851100545393 4874487219515888325409045)
                ·
                  refine ⟨228491588414807265253549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4874487219515888325409045 228491588414807265253549)
                  ·
                    rfl

theorem cell22_2002436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_2002436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002436 prefixEnd_2002436 := by exact prefixLift 2002436
  have htrace : WordTrace (prefixWord ++ tailWord_2002436) baseStart_2002436 baseEnd_2002436 := by
    simpa [prefixWord, tailWord_2002436, baseEnd_2002436] using wordTrace_append hprefix tailTrace_2002436
  have hstable : (prefixWord ++ tailWord_2002436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002436).length < 2 ^ (prefixWord ++ tailWord_2002436).sum := by decide
  have hdescent : baseEnd_2002436 < baseStart_2002436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002464 : List Nat := [2, 1, 1, 6, 1, 2, 9]
def baseStart_2002464 : Nat := 118140960795 + 2002464 * 2 ^ 59
def prefixEnd_2002464 : Nat := 4983230072969 + 3 ^ 40 * 2002464 * 2
def baseEnd_2002464 : Nat := 25388309267282928002243

theorem tailTrace_2002464 : CollatzResearch.WordTrace tailWord_2002464 prefixEnd_2002464 25388309267282928002243 := by
  unfold tailWord_2002464
  simp only [CollatzResearch.WordTrace]
  refine ⟨36517931108711198234403223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48690574811614930979204297 36517931108711198234403223)
  ·
    refine ⟨54776896663066797351604835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36517931108711198234403223 54776896663066797351604835)
    ·
      refine ⟨82165344994600196027407253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54776896663066797351604835 82165344994600196027407253)
      ·
        refine ⟨3851500546621884188784715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82165344994600196027407253 3851500546621884188784715)
        ·
          refine ⟨5777250819932826283177073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851500546621884188784715 5777250819932826283177073)
          ·
            refine ⟨4332938114949619712382805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5777250819932826283177073 4332938114949619712382805)
            ·
              refine ⟨25388309267282928002243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4332938114949619712382805 25388309267282928002243)
              ·
                rfl

theorem cell22_2002464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 9].length) (baseStart_2002464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002464 prefixEnd_2002464 := by exact prefixLift 2002464
  have htrace : WordTrace (prefixWord ++ tailWord_2002464) baseStart_2002464 baseEnd_2002464 := by
    simpa [prefixWord, tailWord_2002464, baseEnd_2002464] using wordTrace_append hprefix tailTrace_2002464
  have hstable : (prefixWord ++ tailWord_2002464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002464).length < 2 ^ (prefixWord ++ tailWord_2002464).sum := by decide
  have hdescent : baseEnd_2002464 < baseStart_2002464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002569 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_2002569 : Nat := 118140960795 + 2002569 * 2 ^ 59
def prefixEnd_2002569 : Nat := 4983230072969 + 3 ^ 40 * 2002569 * 2
def baseEnd_2002569 : Nat := 685520293862453782185239

theorem tailTrace_2002569 : CollatzResearch.WordTrace tailWord_2002569 prefixEnd_2002569 685520293862453782185239 := by
  unfold tailWord_2002569
  simp only [CollatzResearch.WordTrace]
  refine ⟨73039691882041999401378761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48693127921361332934252507 73039691882041999401378761)
  ·
    refine ⟨54779768911531499551034071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73039691882041999401378761 54779768911531499551034071)
    ·
      refine ⟨82169653367297249326551107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54779768911531499551034071 82169653367297249326551107)
      ·
        refine ⟨123254480050945873989826661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82169653367297249326551107 123254480050945873989826661)
        ·
          refine ⟨23110215009552351373092499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123254480050945873989826661 23110215009552351373092499)
          ·
            refine ⟨34665322514328527059638749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23110215009552351373092499 34665322514328527059638749)
            ·
              refine ⟨12999495942873197647364531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34665322514328527059638749 12999495942873197647364531)
              ·
                refine ⟨19499243914309796471046797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12999495942873197647364531 19499243914309796471046797)
                ·
                  refine ⟨7312216467866173676642549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19499243914309796471046797 7312216467866173676642549)
                  ·
                    refine ⟨685520293862453782185239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7312216467866173676642549 685520293862453782185239)
                    ·
                      rfl

theorem cell22_2002569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_2002569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002569 prefixEnd_2002569 := by exact prefixLift 2002569
  have htrace : WordTrace (prefixWord ++ tailWord_2002569) baseStart_2002569 baseEnd_2002569 := by
    simpa [prefixWord, tailWord_2002569, baseEnd_2002569] using wordTrace_append hprefix tailTrace_2002569
  have hstable : (prefixWord ++ tailWord_2002569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002569).length < 2 ^ (prefixWord ++ tailWord_2002569).sum := by decide
  have hdescent : baseEnd_2002569 < baseStart_2002569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002571 : List Nat := [1, 1, 1, 1, 4, 1, 4, 5, 4]
def baseStart_2002571 : Nat := 118140960795 + 2002571 * 2 ^ 59
def prefixEnd_2002571 : Nat := 4983230072969 + 3 ^ 40 * 2002571 * 2
def baseEnd_2002571 : Nat := 228506992834442147878411

theorem tailTrace_2002571 : CollatzResearch.WordTrace tailWord_2002571 prefixEnd_2002571 228506992834442147878411 := by
  unfold tailWord_2002571
  simp only [CollatzResearch.WordTrace]
  refine ⟨73039764828034753742951567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48693176552023169161967711 73039764828034753742951567)
  ·
    refine ⟨109559647242052130614427351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73039764828034753742951567 109559647242052130614427351)
    ·
      refine ⟨164339470863078195921641027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109559647242052130614427351 164339470863078195921641027)
      ·
        refine ⟨246509206294617293882461541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164339470863078195921641027 246509206294617293882461541)
        ·
          refine ⟨46220476180240742602961539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246509206294617293882461541 46220476180240742602961539)
          ·
            refine ⟨69330714270361113904442309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46220476180240742602961539 69330714270361113904442309)
            ·
              refine ⟨12999508925692708857082933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69330714270361113904442309 12999508925692708857082933)
              ·
                refine ⟨1218703961783691455351525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12999508925692708857082933 1218703961783691455351525)
                ·
                  refine ⟨228506992834442147878411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1218703961783691455351525 228506992834442147878411)
                  ·
                    rfl

theorem cell22_2002571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 4].length) (baseStart_2002571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002571 prefixEnd_2002571 := by exact prefixLift 2002571
  have htrace : WordTrace (prefixWord ++ tailWord_2002571) baseStart_2002571 baseEnd_2002571 := by
    simpa [prefixWord, tailWord_2002571, baseEnd_2002571] using wordTrace_append hprefix tailTrace_2002571
  have hstable : (prefixWord ++ tailWord_2002571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002571).length < 2 ^ (prefixWord ++ tailWord_2002571).sum := by decide
  have hdescent : baseEnd_2002571 < baseStart_2002571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002618 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_2002618 : Nat := 118140960795 + 2002618 * 2 ^ 59
def prefixEnd_2002618 : Nat := 4983230072969 + 3 ^ 40 * 2002618 * 2
def baseEnd_2002618 : Nat := 685537067563833987710089

theorem tailTrace_2002618 : CollatzResearch.WordTrace tailWord_2002618 prefixEnd_2002618 685537067563833987710089 := by
  unfold tailWord_2002618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18260369764716120192478127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48694319372576320513275005 18260369764716120192478127)
  ·
    refine ⟨27390554647074180288717191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18260369764716120192478127 27390554647074180288717191)
    ·
      refine ⟨41085831970611270433075787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27390554647074180288717191 41085831970611270433075787)
      ·
        refine ⟨61628747955916905649613681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41085831970611270433075787 61628747955916905649613681)
        ·
          refine ⟨46221560966937679237210261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61628747955916905649613681 46221560966937679237210261)
          ·
            refine ⟨2166635670325203714244231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46221560966937679237210261 2166635670325203714244231)
            ·
              refine ⟨3249953505487805571366347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166635670325203714244231 3249953505487805571366347)
              ·
                refine ⟨4874930258231708357049521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249953505487805571366347 4874930258231708357049521)
                ·
                  refine ⟨3656197693673781267787141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874930258231708357049521 3656197693673781267787141)
                  ·
                    refine ⟨685537067563833987710089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3656197693673781267787141 685537067563833987710089)
                    ·
                      rfl

theorem cell22_2002618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_2002618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002618 prefixEnd_2002618 := by exact prefixLift 2002618
  have htrace : WordTrace (prefixWord ++ tailWord_2002618) baseStart_2002618 baseEnd_2002618 := by
    simpa [prefixWord, tailWord_2002618, baseEnd_2002618] using wordTrace_append hprefix tailTrace_2002618
  have hstable : (prefixWord ++ tailWord_2002618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002618).length < 2 ^ (prefixWord ++ tailWord_2002618).sum := by decide
  have hdescent : baseEnd_2002618 < baseStart_2002618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002629 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_2002629 : Nat := 118140960795 + 2002629 * 2 ^ 59
def prefixEnd_2002629 : Nat := 4983230072969 + 3 ^ 40 * 2002629 * 2
def baseEnd_2002629 : Nat := 685540833088633625685055

theorem tailTrace_2002629 : CollatzResearch.WordTrace tailWord_2002629 prefixEnd_2002629 685540833088633625685055 := by
  unfold tailWord_2002629
  simp only [CollatzResearch.WordTrace]
  refine ⟨73041880261824629648562941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48694586841216419765708627 73041880261824629648562941)
  ·
    refine ⟨27390705098184236118211103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73041880261824629648562941 27390705098184236118211103)
    ·
      refine ⟨41086057647276354177316655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27390705098184236118211103 41086057647276354177316655)
      ·
        refine ⟨61629086470914531265974983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41086057647276354177316655 61629086470914531265974983)
        ·
          refine ⟨92443629706371796898962475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61629086470914531265974983 92443629706371796898962475)
          ·
            refine ⟨138665444559557695348443713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92443629706371796898962475 138665444559557695348443713)
            ·
              refine ⟨103999083419668271511332785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138665444559557695348443713 103999083419668271511332785)
              ·
                refine ⟨77999312564751203633499589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103999083419668271511332785 77999312564751203633499589)
                ·
                  refine ⟨14624871105890850681281173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77999312564751203633499589 14624871105890850681281173)
                  ·
                    refine ⟨685540833088633625685055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14624871105890850681281173 685540833088633625685055)
                    ·
                      rfl

theorem cell22_2002629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_2002629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002629 prefixEnd_2002629 := by exact prefixLift 2002629
  have htrace : WordTrace (prefixWord ++ tailWord_2002629) baseStart_2002629 baseEnd_2002629 := by
    simpa [prefixWord, tailWord_2002629, baseEnd_2002629] using wordTrace_append hprefix tailTrace_2002629
  have hstable : (prefixWord ++ tailWord_2002629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002629).length < 2 ^ (prefixWord ++ tailWord_2002629).sum := by decide
  have hdescent : baseEnd_2002629 < baseStart_2002629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002631 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 5, 3]
def baseStart_2002631 : Nat := 118140960795 + 2002631 * 2 ^ 59
def prefixEnd_2002631 : Nat := 4983230072969 + 3 ^ 40 * 2002631 * 2
def baseEnd_2002631 : Nat := 685541517729506287135049

theorem tailTrace_2002631 : CollatzResearch.WordTrace tailWord_2002631 prefixEnd_2002631 685541517729506287135049 := by
  unfold tailWord_2002631
  simp only [CollatzResearch.WordTrace]
  refine ⟨73041953207817383990135747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48694635471878255993423831 73041953207817383990135747)
  ·
    refine ⟨109562929811726075985203621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73041953207817383990135747 109562929811726075985203621)
    ·
      refine ⟨20543049339698639247225679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109562929811726075985203621 20543049339698639247225679)
      ·
        refine ⟨30814574009547958870838519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20543049339698639247225679 30814574009547958870838519)
        ·
          refine ⟨46221861014321938306257779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30814574009547958870838519 46221861014321938306257779)
          ·
            refine ⟨69332791521482907459386669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46221861014321938306257779 69332791521482907459386669)
            ·
              refine ⟨25999796820556090297270001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69332791521482907459386669 25999796820556090297270001)
              ·
                refine ⟨19499847615417067722952501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25999796820556090297270001 19499847615417067722952501)
                ·
                  refine ⟨1828110713945350099026797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19499847615417067722952501 1828110713945350099026797)
                  ·
                    refine ⟨685541517729506287135049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828110713945350099026797 685541517729506287135049)
                    ·
                      rfl

theorem cell22_2002631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_2002631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002631 prefixEnd_2002631 := by exact prefixLift 2002631
  have htrace : WordTrace (prefixWord ++ tailWord_2002631) baseStart_2002631 baseEnd_2002631 := by
    simpa [prefixWord, tailWord_2002631, baseEnd_2002631] using wordTrace_append hprefix tailTrace_2002631
  have hstable : (prefixWord ++ tailWord_2002631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002631).length < 2 ^ (prefixWord ++ tailWord_2002631).sum := by decide
  have hdescent : baseEnd_2002631 < baseStart_2002631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002637 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2002637 : Nat := 118140960795 + 2002637 * 2 ^ 59
def prefixEnd_2002637 : Nat := 4983230072969 + 3 ^ 40 * 2002637 * 2
def baseEnd_2002637 : Nat := 685543571652124271485031

theorem tailTrace_2002637 : CollatzResearch.WordTrace tailWord_2002637 prefixEnd_2002637 685543571652124271485031 := by
  unfold tailWord_2002637
  simp only [CollatzResearch.WordTrace]
  refine ⟨73042172045795647014854165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48694781363863764676569443 73042172045795647014854165)
  ·
    refine ⟨3423851814646670953821289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73042172045795647014854165 3423851814646670953821289)
    ·
      refine ⟨2567888860985003215365967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3423851814646670953821289 2567888860985003215365967)
      ·
        refine ⟨3851833291477504823048951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567888860985003215365967 3851833291477504823048951)
        ·
          refine ⟨5777749937216257234573427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851833291477504823048951 5777749937216257234573427)
          ·
            refine ⟨8666624905824385851860141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777749937216257234573427 8666624905824385851860141)
            ·
              refine ⟨3249984339684144694447553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8666624905824385851860141 3249984339684144694447553)
              ·
                refine ⟨2437488254763108520835665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3249984339684144694447553 2437488254763108520835665)
                ·
                  refine ⟨1828116191072331390626749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437488254763108520835665 1828116191072331390626749)
                  ·
                    refine ⟨685543571652124271485031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828116191072331390626749 685543571652124271485031)
                    ·
                      rfl

theorem cell22_2002637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2002637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002637 prefixEnd_2002637 := by exact prefixLift 2002637
  have htrace : WordTrace (prefixWord ++ tailWord_2002637) baseStart_2002637 baseEnd_2002637 := by
    simpa [prefixWord, tailWord_2002637, baseEnd_2002637] using wordTrace_append hprefix tailTrace_2002637
  have hstable : (prefixWord ++ tailWord_2002637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002637).length < 2 ^ (prefixWord ++ tailWord_2002637).sum := by decide
  have hdescent : baseEnd_2002637 < baseStart_2002637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002648 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 3, 3]
def baseStart_2002648 : Nat := 118140960795 + 2002648 * 2 ^ 59
def prefixEnd_2002648 : Nat := 4983230072969 + 3 ^ 40 * 2002648 * 2
def baseEnd_2002648 : Nat := 685547337176923909459997

theorem tailTrace_2002648 : CollatzResearch.WordTrace tailWord_2002648 prefixEnd_2002648 685547337176923909459997 := by
  unfold tailWord_2002648
  simp only [CollatzResearch.WordTrace]
  refine ⟨36521286624377897946752299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48695048832503863929003065 36521286624377897946752299)
  ·
    refine ⟨54781929936566846920128449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36521286624377897946752299 54781929936566846920128449)
    ·
      refine ⟨41086447452425135190096337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54781929936566846920128449 41086447452425135190096337)
      ·
        refine ⟨30814835589318851392572253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41086447452425135190096337 30814835589318851392572253)
        ·
          refine ⟨11555563345994569272214595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30814835589318851392572253 11555563345994569272214595)
          ·
            refine ⟨17333345018991853908321893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11555563345994569272214595 17333345018991853908321893)
            ·
              refine ⟨3250002191060972607810355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17333345018991853908321893 3250002191060972607810355)
              ·
                refine ⟨4875003286591458911715533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250002191060972607810355 4875003286591458911715533)
                ·
                  refine ⟨1828126232471797091893325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4875003286591458911715533 1828126232471797091893325)
                  ·
                    refine ⟨685547337176923909459997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828126232471797091893325 685547337176923909459997)
                    ·
                      rfl

theorem cell22_2002648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_2002648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002648 prefixEnd_2002648 := by exact prefixLift 2002648
  have htrace : WordTrace (prefixWord ++ tailWord_2002648) baseStart_2002648 baseEnd_2002648 := by
    simpa [prefixWord, tailWord_2002648, baseEnd_2002648] using wordTrace_append hprefix tailTrace_2002648
  have hstable : (prefixWord ++ tailWord_2002648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002648).length < 2 ^ (prefixWord ++ tailWord_2002648).sum := by decide
  have hdescent : baseEnd_2002648 < baseStart_2002648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002725 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_2002725 : Nat := 118140960795 + 2002725 * 2 ^ 59
def prefixEnd_2002725 : Nat := 4983230072969 + 3 ^ 40 * 2002725 * 2
def baseEnd_2002725 : Nat := 685573695850521375284761

theorem tailTrace_2002725 : CollatzResearch.WordTrace tailWord_2002725 prefixEnd_2002725 685573695850521375284761 := by
  unfold tailWord_2002725
  simp only [CollatzResearch.WordTrace]
  refine ⟨73045381669476838044057629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48696921112984558696038419 73045381669476838044057629)
  ·
    refine ⟨27392018126053814266521611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73045381669476838044057629 27392018126053814266521611)
    ·
      refine ⟨41088027189080721399782417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27392018126053814266521611 41088027189080721399782417)
      ·
        refine ⟨30816020391810541049836813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41088027189080721399782417 30816020391810541049836813)
        ·
          refine ⟨11556007646928952893688805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30816020391810541049836813 11556007646928952893688805)
          ·
            refine ⟨2166751433799178667566651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11556007646928952893688805 2166751433799178667566651)
            ·
              refine ⟨3250127150698768001349977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166751433799178667566651 3250127150698768001349977)
              ·
                refine ⟨2437595363024076001012483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250127150698768001349977 2437595363024076001012483)
                ·
                  refine ⟨3656393044536114001518725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437595363024076001012483 3656393044536114001518725)
                  ·
                    refine ⟨685573695850521375284761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3656393044536114001518725 685573695850521375284761)
                    ·
                      rfl

theorem cell22_2002725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_2002725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002725 prefixEnd_2002725 := by exact prefixLift 2002725
  have htrace : WordTrace (prefixWord ++ tailWord_2002725) baseStart_2002725 baseEnd_2002725 := by
    simpa [prefixWord, tailWord_2002725, baseEnd_2002725] using wordTrace_append hprefix tailTrace_2002725
  have hstable : (prefixWord ++ tailWord_2002725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002725).length < 2 ^ (prefixWord ++ tailWord_2002725).sum := by decide
  have hdescent : baseEnd_2002725 < baseStart_2002725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002738 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2002738 : Nat := 118140960795 + 2002738 * 2 ^ 59
def prefixEnd_2002738 : Nat := 4983230072969 + 3 ^ 40 * 2002738 * 2
def baseEnd_2002738 : Nat := 685578146016193674709721

theorem tailTrace_2002738 : CollatzResearch.WordTrace tailWord_2002738 prefixEnd_2002738 685578146016193674709721 := by
  unfold tailWord_2002738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18261463954607435316070217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48697237212286494176187245 18261463954607435316070217)
  ·
    refine ⟨13696097965955576487052663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18261463954607435316070217 13696097965955576487052663)
    ·
      refine ⟨20544146948933364730578995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13696097965955576487052663 20544146948933364730578995)
      ·
        refine ⟨30816220423400047095868493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20544146948933364730578995 30816220423400047095868493)
        ·
          refine ⟨11556082658775017660950685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30816220423400047095868493 11556082658775017660950685)
          ·
            refine ⟨4333530997040631622856507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11556082658775017660950685 4333530997040631622856507)
            ·
              refine ⟨6500296495560947434284761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333530997040631622856507 6500296495560947434284761)
              ·
                refine ⟨4875222371670710575713571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6500296495560947434284761 4875222371670710575713571)
                ·
                  refine ⟨7312833557506065863570357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4875222371670710575713571 7312833557506065863570357)
                  ·
                    refine ⟨685578146016193674709721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7312833557506065863570357 685578146016193674709721)
                    ·
                      rfl

theorem cell22_2002738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2002738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002738 prefixEnd_2002738 := by exact prefixLift 2002738
  have htrace : WordTrace (prefixWord ++ tailWord_2002738) baseStart_2002738 baseEnd_2002738 := by
    simpa [prefixWord, tailWord_2002738, baseEnd_2002738] using wordTrace_append hprefix tailTrace_2002738
  have hstable : (prefixWord ++ tailWord_2002738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002738).length < 2 ^ (prefixWord ++ tailWord_2002738).sum := by decide
  have hdescent : baseEnd_2002738 < baseStart_2002738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002751 : List Nat := [1, 1, 2, 2, 6, 10]
def baseStart_2002751 : Nat := 118140960795 + 2002751 * 2 ^ 59
def prefixEnd_2002751 : Nat := 4983230072969 + 3 ^ 40 * 2002751 * 2
def baseEnd_2002751 : Nat := 8463982668911925606601

theorem tailTrace_2002751 : CollatzResearch.WordTrace tailWord_2002751 prefixEnd_2002751 8463982668911925606601 := by
  unfold tailWord_2002751
  simp only [CollatzResearch.WordTrace]
  refine ⟨73046329967382644484504107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48697553311588429656336071 73046329967382644484504107)
  ·
    refine ⟨109569494951073966726756161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73046329967382644484504107 109569494951073966726756161)
    ·
      refine ⟨82177121213305475045067121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109569494951073966726756161 82177121213305475045067121)
      ·
        refine ⟨61632840909979106283800341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82177121213305475045067121 61632840909979106283800341)
        ·
          refine ⟨2889039417655270607053141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61632840909979106283800341 2889039417655270607053141)
          ·
            refine ⟨8463982668911925606601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2889039417655270607053141 8463982668911925606601)
            ·
              rfl

theorem cell22_2002751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 10].length) (baseStart_2002751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002751 prefixEnd_2002751 := by exact prefixLift 2002751
  have htrace : WordTrace (prefixWord ++ tailWord_2002751) baseStart_2002751 baseEnd_2002751 := by
    simpa [prefixWord, tailWord_2002751, baseEnd_2002751] using wordTrace_append hprefix tailTrace_2002751
  have hstable : (prefixWord ++ tailWord_2002751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002751).length < 2 ^ (prefixWord ++ tailWord_2002751).sum := by decide
  have hdescent : baseEnd_2002751 < baseStart_2002751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002755 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 2, 3]
def baseStart_2002755 : Nat := 118140960795 + 2002755 * 2 ^ 59
def prefixEnd_2002755 : Nat := 4983230072969 + 3 ^ 40 * 2002755 * 2
def baseEnd_2002755 : Nat := 685583965463611297034669

theorem tailTrace_2002755 : CollatzResearch.WordTrace tailWord_2002755 prefixEnd_2002755 685583965463611297034669 := by
  unfold tailWord_2002755
  simp only [CollatzResearch.WordTrace]
  refine ⟨73046475859368153167649719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48697650572912102111766479 73046475859368153167649719)
  ·
    refine ⟨109569713789052229751474579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73046475859368153167649719 109569713789052229751474579)
    ·
      refine ⟨164354570683578344627211869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109569713789052229751474579 164354570683578344627211869)
      ·
        refine ⟨61632964006341879235204451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164354570683578344627211869 61632964006341879235204451)
        ·
          refine ⟨92449446009512818852806677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61632964006341879235204451 92449446009512818852806677)
          ·
            refine ⟨4333567781695913383725313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92449446009512818852806677 4333567781695913383725313)
            ·
              refine ⟨3250175836271935037793985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4333567781695913383725313 3250175836271935037793985)
              ·
                refine ⟨2437631877203951278345489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250175836271935037793985 2437631877203951278345489)
                ·
                  refine ⟨1828223907902963458759117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437631877203951278345489 1828223907902963458759117)
                  ·
                    refine ⟨685583965463611297034669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828223907902963458759117 685583965463611297034669)
                    ·
                      rfl

theorem cell22_2002755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 3].length) (baseStart_2002755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002755 prefixEnd_2002755 := by exact prefixLift 2002755
  have htrace : WordTrace (prefixWord ++ tailWord_2002755) baseStart_2002755 baseEnd_2002755 := by
    simpa [prefixWord, tailWord_2002755, baseEnd_2002755] using wordTrace_append hprefix tailTrace_2002755
  have hstable : (prefixWord ++ tailWord_2002755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002755).length < 2 ^ (prefixWord ++ tailWord_2002755).sum := by decide
  have hdescent : baseEnd_2002755 < baseStart_2002755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002766 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2002766 : Nat := 118140960795 + 2002766 * 2 ^ 59
def prefixEnd_2002766 : Nat := 4983230072969 + 3 ^ 40 * 2002766 * 2
def baseEnd_2002766 : Nat := 685587730988410935009635

theorem tailTrace_2002766 : CollatzResearch.WordTrace tailWord_2002766 prefixEnd_2002766 685587730988410935009635 := by
  unfold tailWord_2002766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9130859632791037755787519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48697918041552201364200101 9130859632791037755787519)
  ·
    refine ⟨13696289449186556633681279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9130859632791037755787519 13696289449186556633681279)
    ·
      refine ⟨20544434173779834950521919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13696289449186556633681279 20544434173779834950521919)
      ·
        refine ⟨30816651260669752425782879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20544434173779834950521919 30816651260669752425782879)
        ·
          refine ⟨46224976891004628638674319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30816651260669752425782879 46224976891004628638674319)
          ·
            refine ⟨69337465336506942958011479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46224976891004628638674319 69337465336506942958011479)
            ·
              refine ⟨104006198004760414437017219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69337465336506942958011479 104006198004760414437017219)
              ·
                refine ⟨156009297007140621655525829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104006198004760414437017219 156009297007140621655525829)
                ·
                  refine ⟨29251743188838866560411093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156009297007140621655525829 29251743188838866560411093)
                  ·
                    refine ⟨685587730988410935009635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29251743188838866560411093 685587730988410935009635)
                    ·
                      rfl

theorem cell22_2002766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2002766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002766 prefixEnd_2002766 := by exact prefixLift 2002766
  have htrace : WordTrace (prefixWord ++ tailWord_2002766) baseStart_2002766 baseEnd_2002766 := by
    simpa [prefixWord, tailWord_2002766, baseEnd_2002766] using wordTrace_append hprefix tailTrace_2002766
  have hstable : (prefixWord ++ tailWord_2002766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002766).length < 2 ^ (prefixWord ++ tailWord_2002766).sum := by decide
  have hdescent : baseEnd_2002766 < baseStart_2002766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002783 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 5, 3]
def baseStart_2002783 : Nat := 118140960795 + 2002783 * 2 ^ 59
def prefixEnd_2002783 : Nat := 4983230072969 + 3 ^ 40 * 2002783 * 2
def baseEnd_2002783 : Nat := 685593550435828557334583

theorem tailTrace_2002783 : CollatzResearch.WordTrace tailWord_2002783 prefixEnd_2002783 685593550435828557334583 := by
  unfold tailWord_2002783
  simp only [CollatzResearch.WordTrace]
  refine ⟨73047497103266713949669003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48698331402177809299779335 73047497103266713949669003)
  ·
    refine ⟨109571245654900070924503505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73047497103266713949669003 109571245654900070924503505)
    ·
      refine ⟨82178434241175053193377629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109571245654900070924503505 82178434241175053193377629)
      ·
        refine ⟨30816912840440644947516611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82178434241175053193377629 30816912840440644947516611)
        ·
          refine ⟨46225369260660967421274917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30816912840440644947516611 46225369260660967421274917)
          ·
            refine ⟨8667256736373931391489047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46225369260660967421274917 8667256736373931391489047)
            ·
              refine ⟨13000885104560897087233571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8667256736373931391489047 13000885104560897087233571)
              ·
                refine ⟨19501327656841345630850357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13000885104560897087233571 19501327656841345630850357)
                ·
                  refine ⟨1828249467828876152892221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19501327656841345630850357 1828249467828876152892221)
                  ·
                    refine ⟨685593550435828557334583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828249467828876152892221 685593550435828557334583)
                    ·
                      rfl

theorem cell22_2002783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_2002783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002783 prefixEnd_2002783 := by exact prefixLift 2002783
  have htrace : WordTrace (prefixWord ++ tailWord_2002783) baseStart_2002783 baseEnd_2002783 := by
    simpa [prefixWord, tailWord_2002783, baseEnd_2002783] using wordTrace_append hprefix tailTrace_2002783
  have hstable : (prefixWord ++ tailWord_2002783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002783).length < 2 ^ (prefixWord ++ tailWord_2002783).sum := by decide
  have hdescent : baseEnd_2002783 < baseStart_2002783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002787 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 2, 4]
def baseStart_2002787 : Nat := 118140960795 + 2002787 * 2 ^ 59
def prefixEnd_2002787 : Nat := 4983230072969 + 3 ^ 40 * 2002787 * 2
def baseEnd_2002787 : Nat := 685594919717573880234571

theorem tailTrace_2002787 : CollatzResearch.WordTrace tailWord_2002787 prefixEnd_2002787 685594919717573880234571 := by
  unfold tailWord_2002787
  simp only [CollatzResearch.WordTrace]
  refine ⟨73047642995252222632814615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48698428663501481755209743 73047642995252222632814615)
  ·
    refine ⟨109571464492878333949221923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73047642995252222632814615 109571464492878333949221923)
    ·
      refine ⟨164357196739317500923832885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109571464492878333949221923 164357196739317500923832885)
      ·
        refine ⟨15408487194311015711609333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164357196739317500923832885 15408487194311015711609333)
        ·
          refine ⟨1444545674466657722963375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15408487194311015711609333 1444545674466657722963375)
          ·
            refine ⟨2166818511699986584445063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444545674466657722963375 2166818511699986584445063)
            ·
              refine ⟨3250227767549979876667595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166818511699986584445063 3250227767549979876667595)
              ·
                refine ⟨4875341651324969815001393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250227767549979876667595 4875341651324969815001393)
                ·
                  refine ⟨3656506238493727361251045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4875341651324969815001393 3656506238493727361251045)
                  ·
                    refine ⟨685594919717573880234571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3656506238493727361251045 685594919717573880234571)
                    ·
                      rfl

theorem cell22_2002787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 4].length) (baseStart_2002787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002787 prefixEnd_2002787 := by exact prefixLift 2002787
  have htrace : WordTrace (prefixWord ++ tailWord_2002787) baseStart_2002787 baseEnd_2002787 := by
    simpa [prefixWord, tailWord_2002787, baseEnd_2002787] using wordTrace_append hprefix tailTrace_2002787
  have hstable : (prefixWord ++ tailWord_2002787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002787).length < 2 ^ (prefixWord ++ tailWord_2002787).sum := by decide
  have hdescent : baseEnd_2002787 < baseStart_2002787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002806 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_2002806 : Nat := 118140960795 + 2002806 * 2 ^ 59
def prefixEnd_2002806 : Nat := 4983230072969 + 3 ^ 40 * 2002806 * 2
def baseEnd_2002806 : Nat := 685601423805864164009513

theorem tailTrace_2002806 : CollatzResearch.WordTrace tailWord_2002806 prefixEnd_2002806 685601423805864164009513 := by
  unfold tailWord_2002806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4565520998886461804859767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48698890654788925918504181 4565520998886461804859767)
  ·
    refine ⟨6848281498329692707289651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4565520998886461804859767 6848281498329692707289651)
    ·
      refine ⟨10272422247494539060934477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6848281498329692707289651 10272422247494539060934477)
      ·
        refine ⟨3852158342810452147850429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10272422247494539060934477 3852158342810452147850429)
        ·
          refine ⟨1444559378553919555443911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3852158342810452147850429 1444559378553919555443911)
          ·
            refine ⟨2166839067830879333165867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444559378553919555443911 2166839067830879333165867)
            ·
              refine ⟨3250258601746318999748801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166839067830879333165867 3250258601746318999748801)
              ·
                refine ⟨2437693951309739249811601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250258601746318999748801 2437693951309739249811601)
                ·
                  refine ⟨1828270463482304437358701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437693951309739249811601 1828270463482304437358701)
                  ·
                    refine ⟨685601423805864164009513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828270463482304437358701 685601423805864164009513)
                    ·
                      rfl

theorem cell22_2002806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_2002806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002806 prefixEnd_2002806 := by exact prefixLift 2002806
  have htrace : WordTrace (prefixWord ++ tailWord_2002806) baseStart_2002806 baseEnd_2002806 := by
    simpa [prefixWord, tailWord_2002806, baseEnd_2002806] using wordTrace_append hprefix tailTrace_2002806
  have hstable : (prefixWord ++ tailWord_2002806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002806).length < 2 ^ (prefixWord ++ tailWord_2002806).sum := by decide
  have hdescent : baseEnd_2002806 < baseStart_2002806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002868 : List Nat := [2, 5, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2002868 : Nat := 118140960795 + 2002868 * 2 ^ 59
def prefixEnd_2002868 : Nat := 4983230072969 + 3 ^ 40 * 2002868 * 2
def baseEnd_2002868 : Nat := 685622647672916668959323

theorem tailTrace_2002868 : CollatzResearch.WordTrace tailWord_2002868 prefixEnd_2002868 685622647672916668959323 := by
  unfold tailWord_2002868
  simp only [CollatzResearch.WordTrace]
  refine ⟨36525298653979386733256629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48700398205305848977675505 36525298653979386733256629)
  ·
    refine ⟨3424246748810567506242809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36525298653979386733256629 3424246748810567506242809)
    ·
      refine ⟨2568185061607925629682107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3424246748810567506242809 2568185061607925629682107)
      ·
        refine ⟨3852277592411888444523161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568185061607925629682107 3852277592411888444523161)
        ·
          refine ⟨2889208194308916333392371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3852277592411888444523161 2889208194308916333392371)
          ·
            refine ⟨4333812291463374500088557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889208194308916333392371 4333812291463374500088557)
            ·
              refine ⟨1625179609298765437533209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4333812291463374500088557 1625179609298765437533209)
              ·
                refine ⟨1218884706974074078149907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1625179609298765437533209 1218884706974074078149907)
                ·
                  refine ⟨1828327060461111117224861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218884706974074078149907 1828327060461111117224861)
                  ·
                    refine ⟨685622647672916668959323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828327060461111117224861 685622647672916668959323)
                    ·
                      rfl

theorem cell22_2002868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2002868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2002868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2002868 prefixEnd_2002868 := by exact prefixLift 2002868
  have htrace : WordTrace (prefixWord ++ tailWord_2002868) baseStart_2002868 baseEnd_2002868 := by
    simpa [prefixWord, tailWord_2002868, baseEnd_2002868] using wordTrace_append hprefix tailTrace_2002868
  have hstable : (prefixWord ++ tailWord_2002868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002868).length < 2 ^ (prefixWord ++ tailWord_2002868).sum := by decide
  have hdescent : baseEnd_2002868 < baseStart_2002868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003040 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_2003040 : Nat := 118140960795 + 2003040 * 2 ^ 59
def prefixEnd_2003040 : Nat := 4983230072969 + 3 ^ 40 * 2003040 * 2
def baseEnd_2003040 : Nat := 685681526787965553658795

theorem tailTrace_2003040 : CollatzResearch.WordTrace tailWord_2003040 prefixEnd_2003040 685681526787965553658795 := by
  unfold tailWord_2003040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36528435331667823420887287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48704580442223764561183049 36528435331667823420887287)
  ·
    refine ⟨54792652997501735131330931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36528435331667823420887287 54792652997501735131330931)
    ·
      refine ⟨82188979496252602696996397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54792652997501735131330931 82188979496252602696996397)
      ·
        refine ⟨30820867311094726011373649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82188979496252602696996397 30820867311094726011373649)
        ·
          refine ⟨23115650483321044508530237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30820867311094726011373649 23115650483321044508530237)
          ·
            refine ⟨8668368931245391690698839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23115650483321044508530237 8668368931245391690698839)
            ·
              refine ⟨13002553396868087536048259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668368931245391690698839 13002553396868087536048259)
              ·
                refine ⟨19503830095302131304072389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13002553396868087536048259 19503830095302131304072389)
                ·
                  refine ⟨3656968142869149619513573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19503830095302131304072389 3656968142869149619513573)
                  ·
                    refine ⟨685681526787965553658795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3656968142869149619513573 685681526787965553658795)
                    ·
                      rfl

theorem cell22_2003040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_2003040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003040 prefixEnd_2003040 := by exact prefixLift 2003040
  have htrace : WordTrace (prefixWord ++ tailWord_2003040) baseStart_2003040 baseEnd_2003040 := by
    simpa [prefixWord, tailWord_2003040, baseEnd_2003040] using wordTrace_append hprefix tailTrace_2003040
  have hstable : (prefixWord ++ tailWord_2003040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003040).length < 2 ^ (prefixWord ++ tailWord_2003040).sum := by decide
  have hdescent : baseEnd_2003040 < baseStart_2003040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003055 : List Nat := [1, 1, 2, 1, 3, 5, 2, 7]
def baseStart_2003055 : Nat := 118140960795 + 2003055 * 2 ^ 59
def prefixEnd_2003055 : Nat := 4983230072969 + 3 ^ 40 * 2003055 * 2
def baseEnd_2003055 : Nat := 76187406843834501614861

theorem tailTrace_2003055 : CollatzResearch.WordTrace tailWord_2003055 prefixEnd_2003055 76187406843834501614861 := by
  unfold tailWord_2003055
  simp only [CollatzResearch.WordTrace]
  refine ⟨73057417758281304403570619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48704945172187536269047079 73057417758281304403570619)
  ·
    refine ⟨109586126637421956605355929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73057417758281304403570619 109586126637421956605355929)
    ·
      refine ⟨82189594978066467454016947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109586126637421956605355929 82189594978066467454016947)
      ·
        refine ⟨123284392467099701181025421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82189594978066467454016947 123284392467099701181025421)
        ·
          refine ⟨46231647175162387942884533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123284392467099701181025421 46231647175162387942884533)
          ·
            refine ⟨4334216922671473869645425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46231647175162387942884533 4334216922671473869645425)
            ·
              refine ⟨3250662692003605402234069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334216922671473869645425 3250662692003605402234069)
              ·
                refine ⟨76187406843834501614861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3250662692003605402234069 76187406843834501614861)
                ·
                  rfl

theorem cell22_2003055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 7].length) (baseStart_2003055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003055 prefixEnd_2003055 := by exact prefixLift 2003055
  have htrace : WordTrace (prefixWord ++ tailWord_2003055) baseStart_2003055 baseEnd_2003055 := by
    simpa [prefixWord, tailWord_2003055, baseEnd_2003055] using wordTrace_append hprefix tailTrace_2003055
  have hstable : (prefixWord ++ tailWord_2003055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003055).length < 2 ^ (prefixWord ++ tailWord_2003055).sum := by decide
  have hdescent : baseEnd_2003055 < baseStart_2003055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003147 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 1, 4]
def baseStart_2003147 : Nat := 118140960795 + 2003147 * 2 ^ 59
def prefixEnd_2003147 : Nat := 4983230072969 + 3 ^ 40 * 2003147 * 2
def baseEnd_2003147 : Nat := 685718155074652941233467

theorem tailTrace_2003147 : CollatzResearch.WordTrace tailWord_2003147 prefixEnd_2003147 685718155074652941233467 := by
  unfold tailWord_2003147
  simp only [CollatzResearch.WordTrace]
  refine ⟨73060773273948004115919695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48707182182632002743946463 73060773273948004115919695)
  ·
    refine ⟨109591159910922006173879543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73060773273948004115919695 109591159910922006173879543)
    ·
      refine ⟨164386739866383009260819315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109591159910922006173879543 164386739866383009260819315)
      ·
        refine ⟨246580109799574513891228973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164386739866383009260819315 246580109799574513891228973)
        ·
          refine ⟨92467541174840442709210865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246580109799574513891228973 92467541174840442709210865)
          ·
            refine ⟨69350655881130332031908149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92467541174840442709210865 69350655881130332031908149)
            ·
              refine ⟨6501623988855968627991389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69350655881130332031908149 6501623988855968627991389)
              ·
                refine ⟨2438108995820988235496771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6501623988855968627991389 2438108995820988235496771)
                ·
                  refine ⟨3657163493731482353245157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438108995820988235496771 3657163493731482353245157)
                  ·
                    refine ⟨685718155074652941233467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657163493731482353245157 685718155074652941233467)
                    ·
                      rfl

theorem cell22_2003147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 4].length) (baseStart_2003147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003147 prefixEnd_2003147 := by exact prefixLift 2003147
  have htrace : WordTrace (prefixWord ++ tailWord_2003147) baseStart_2003147 baseEnd_2003147 := by
    simpa [prefixWord, tailWord_2003147, baseEnd_2003147] using wordTrace_append hprefix tailTrace_2003147
  have hstable : (prefixWord ++ tailWord_2003147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003147).length < 2 ^ (prefixWord ++ tailWord_2003147).sum := by decide
  have hdescent : baseEnd_2003147 < baseStart_2003147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003181 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2003181 : Nat := 118140960795 + 2003181 * 2 ^ 59
def prefixEnd_2003181 : Nat := 4983230072969 + 3 ^ 40 * 2003181 * 2
def baseEnd_2003181 : Nat := 685729793969488185883363

theorem tailTrace_2003181 : CollatzResearch.WordTrace tailWord_2003181 prefixEnd_2003181 685729793969488185883363 := by
  unfold tailWord_2003181
  simp only [CollatzResearch.WordTrace]
  refine ⟨73062013355824827922657397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48708008903883218615104931 73062013355824827922657397)
  ·
    refine ⟨6849563752108577617749131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73062013355824827922657397 6849563752108577617749131)
    ·
      refine ⟨10274345628162866426623697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6849563752108577617749131 10274345628162866426623697)
      ·
        refine ⟨7705759221122149819967773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10274345628162866426623697 7705759221122149819967773)
        ·
          refine ⟨2889659707920806182487915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7705759221122149819967773 2889659707920806182487915)
          ·
            refine ⟨4334489561881209273731873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889659707920806182487915 4334489561881209273731873)
            ·
              refine ⟨3250867171410906955298905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334489561881209273731873 3250867171410906955298905)
              ·
                refine ⟨2438150378558180216474179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250867171410906955298905 2438150378558180216474179)
                ·
                  refine ⟨3657225567837270324711269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438150378558180216474179 3657225567837270324711269)
                  ·
                    refine ⟨685729793969488185883363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657225567837270324711269 685729793969488185883363)
                    ·
                      rfl

theorem cell22_2003181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2003181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003181 prefixEnd_2003181 := by exact prefixLift 2003181
  have htrace : WordTrace (prefixWord ++ tailWord_2003181) baseStart_2003181 baseEnd_2003181 := by
    simpa [prefixWord, tailWord_2003181, baseEnd_2003181] using wordTrace_append hprefix tailTrace_2003181
  have hstable : (prefixWord ++ tailWord_2003181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003181).length < 2 ^ (prefixWord ++ tailWord_2003181).sum := by decide
  have hdescent : baseEnd_2003181 < baseStart_2003181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003196 : List Nat := [2, 2, 2, 1, 4, 3, 1, 3, 4]
def baseStart_2003196 : Nat := 118140960795 + 2003196 * 2 ^ 59
def prefixEnd_2003196 : Nat := 4983230072969 + 3 ^ 40 * 2003196 * 2
def baseEnd_2003196 : Nat := 228578309592011048919439

theorem tailTrace_2003196 : CollatzResearch.WordTrace tailWord_2003196 prefixEnd_2003196 228578309592011048919439 := by
  unfold tailWord_2003196
  simp only [CollatzResearch.WordTrace]
  refine ⟨36531280225385242742226721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48708373633846990322968961 36531280225385242742226721)
  ·
    refine ⟨27398460169038932056670041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36531280225385242742226721 27398460169038932056670041)
    ·
      refine ⟨20548845126779199042502531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27398460169038932056670041 20548845126779199042502531)
      ·
        refine ⟨30823267690168798563753797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20548845126779199042502531 30823267690168798563753797)
        ·
          refine ⟨5779362691906649730703837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30823267690168798563753797 5779362691906649730703837)
          ·
            refine ⟨2167261009464993649013939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5779362691906649730703837 2167261009464993649013939)
            ·
              refine ⟨3250891514197490473520909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167261009464993649013939 3250891514197490473520909)
              ·
                refine ⟨1219084317824058927570341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3250891514197490473520909 1219084317824058927570341)
                ·
                  refine ⟨228578309592011048919439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219084317824058927570341 228578309592011048919439)
                  ·
                    rfl

theorem cell22_2003196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_2003196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003196 prefixEnd_2003196 := by exact prefixLift 2003196
  have htrace : WordTrace (prefixWord ++ tailWord_2003196) baseStart_2003196 baseEnd_2003196 := by
    simpa [prefixWord, tailWord_2003196, baseEnd_2003196] using wordTrace_append hprefix tailTrace_2003196
  have hstable : (prefixWord ++ tailWord_2003196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003196).length < 2 ^ (prefixWord ++ tailWord_2003196).sum := by decide
  have hdescent : baseEnd_2003196 < baseStart_2003196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003284 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2003284 : Nat := 118140960795 + 2003284 * 2 ^ 59
def prefixEnd_2003284 : Nat := 4983230072969 + 3 ^ 40 * 2003284 * 2
def baseEnd_2003284 : Nat := 685765052974430250558047

theorem tailTrace_2003284 : CollatzResearch.WordTrace tailWord_2003284 prefixEnd_2003284 685765052974430250558047 := by
  unfold tailWord_2003284
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532885037225838256828453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48710513382967784342437937 36532885037225838256828453)
  ·
    refine ⟨6849915944479844673155335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36532885037225838256828453 6849915944479844673155335)
    ·
      refine ⟨10274873916719767009733003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6849915944479844673155335 10274873916719767009733003)
      ·
        refine ⟨15412310875079650514599505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10274873916719767009733003 15412310875079650514599505)
        ·
          refine ⟨11559233156309737885949629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15412310875079650514599505 11559233156309737885949629)
          ·
            refine ⟨4334712433616151707231111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11559233156309737885949629 4334712433616151707231111)
            ·
              refine ⟨6502068650424227560846667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334712433616151707231111 6502068650424227560846667)
              ·
                refine ⟨9753102975636341341270001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6502068650424227560846667 9753102975636341341270001)
                ·
                  refine ⟨7314827231727256005952501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9753102975636341341270001 7314827231727256005952501)
                  ·
                    refine ⟨685765052974430250558047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7314827231727256005952501 685765052974430250558047)
                    ·
                      rfl

theorem cell22_2003284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2003284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003284 prefixEnd_2003284 := by exact prefixLift 2003284
  have htrace : WordTrace (prefixWord ++ tailWord_2003284) baseStart_2003284 baseEnd_2003284 := by
    simpa [prefixWord, tailWord_2003284, baseEnd_2003284] using wordTrace_append hprefix tailTrace_2003284
  have hstable : (prefixWord ++ tailWord_2003284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003284).length < 2 ^ (prefixWord ++ tailWord_2003284).sum := by decide
  have hdescent : baseEnd_2003284 < baseStart_2003284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003294 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2003294 : Nat := 118140960795 + 2003294 * 2 ^ 59
def prefixEnd_2003294 : Nat := 4983230072969 + 3 ^ 40 * 2003294 * 2
def baseEnd_2003294 : Nat := 685768476178793557808017

theorem tailTrace_2003294 : CollatzResearch.WordTrace tailWord_2003294 prefixEnd_2003294 685768476178793557808017 := by
  unfold tailWord_2003294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133266850551931027690117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48710756536276965481013957 9133266850551931027690117)
  ·
    refine ⟨1712487534478487067691897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9133266850551931027690117 1712487534478487067691897)
    ·
      refine ⟨1284365650858865300768923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1712487534478487067691897 1284365650858865300768923)
      ·
        refine ⟨1926548476288297951153385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284365650858865300768923 1926548476288297951153385)
        ·
          refine ⟨1444911357216223463365039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1926548476288297951153385 1444911357216223463365039)
          ·
            refine ⟨2167367035824335195047559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444911357216223463365039 2167367035824335195047559)
            ·
              refine ⟨3251050553736502792571339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167367035824335195047559 3251050553736502792571339)
              ·
                refine ⟨4876575830604754188857009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251050553736502792571339 4876575830604754188857009)
                ·
                  refine ⟨3657431872953565641642757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876575830604754188857009 3657431872953565641642757)
                  ·
                    refine ⟨685768476178793557808017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657431872953565641642757 685768476178793557808017)
                    ·
                      rfl

theorem cell22_2003294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2003294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003294 prefixEnd_2003294 := by exact prefixLift 2003294
  have htrace : WordTrace (prefixWord ++ tailWord_2003294) baseStart_2003294 baseEnd_2003294 := by
    simpa [prefixWord, tailWord_2003294, baseEnd_2003294] using wordTrace_append hprefix tailTrace_2003294
  have hstable : (prefixWord ++ tailWord_2003294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003294).length < 2 ^ (prefixWord ++ tailWord_2003294).sum := by decide
  have hdescent : baseEnd_2003294 < baseStart_2003294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003299 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 1, 4]
def baseStart_2003299 : Nat := 118140960795 + 2003299 * 2 ^ 59
def prefixEnd_2003299 : Nat := 4983230072969 + 3 ^ 40 * 2003299 * 2
def baseEnd_2003299 : Nat := 685770187780975211433001

theorem tailTrace_2003299 : CollatzResearch.WordTrace tailWord_2003299 prefixEnd_2003299 685770187780975211433001 := by
  unfold tailWord_2003299
  simp only [CollatzResearch.WordTrace]
  refine ⟨73066317169397334075452951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48710878112931556050301967 73066317169397334075452951)
  ·
    refine ⟨109599475754096001113179427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73066317169397334075452951 109599475754096001113179427)
    ·
      refine ⟨164399213631144001669769141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109599475754096001113179427 164399213631144001669769141)
      ·
        refine ⟨15412426277919750156540857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164399213631144001669769141 15412426277919750156540857)
        ·
          refine ⟨11559319708439812617405643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15412426277919750156540857 11559319708439812617405643)
          ·
            refine ⟨17338979562659718926108465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11559319708439812617405643 17338979562659718926108465)
            ·
              refine ⟨13004234671994789194581349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17338979562659718926108465 13004234671994789194581349)
              ·
                refine ⟨2438294000999022973984003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13004234671994789194581349 2438294000999022973984003)
                ·
                  refine ⟨3657441001498534460976005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438294000999022973984003 3657441001498534460976005)
                  ·
                    refine ⟨685770187780975211433001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657441001498534460976005 685770187780975211433001)
                    ·
                      rfl

theorem cell22_2003299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 4].length) (baseStart_2003299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003299 prefixEnd_2003299 := by exact prefixLift 2003299
  have htrace : WordTrace (prefixWord ++ tailWord_2003299) baseStart_2003299 baseEnd_2003299 := by
    simpa [prefixWord, tailWord_2003299, baseEnd_2003299] using wordTrace_append hprefix tailTrace_2003299
  have hstable : (prefixWord ++ tailWord_2003299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003299).length < 2 ^ (prefixWord ++ tailWord_2003299).sum := by decide
  have hdescent : baseEnd_2003299 < baseStart_2003299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003372 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_2003372 : Nat := 118140960795 + 2003372 * 2 ^ 59
def prefixEnd_2003372 : Nat := 4983230072969 + 3 ^ 40 * 2003372 * 2
def baseEnd_2003372 : Nat := 685795177172827354357777

theorem tailTrace_2003372 : CollatzResearch.WordTrace tailWord_2003372 prefixEnd_2003372 685795177172827354357777 := by
  unfold tailWord_2003372
  simp only [CollatzResearch.WordTrace]
  refine ⟨36534489849066433771430185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48712653132088578361906913 36534489849066433771430185)
  ·
    refine ⟨27400867386799825328572639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36534489849066433771430185 27400867386799825328572639)
    ·
      refine ⟨41101301080199737992858959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27400867386799825328572639 41101301080199737992858959)
      ·
        refine ⟨61651951620299606989288439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41101301080199737992858959 61651951620299606989288439)
        ·
          refine ⟨92477927430449410483932659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61651951620299606989288439 92477927430449410483932659)
          ·
            refine ⟨138716891145674115725898989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92477927430449410483932659 138716891145674115725898989)
            ·
              refine ⟨52018834179627793397212121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138716891145674115725898989 52018834179627793397212121)
              ·
                refine ⟨39014125634720845047909091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52018834179627793397212121 39014125634720845047909091)
                ·
                  refine ⟨58521188452081267571863637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39014125634720845047909091 58521188452081267571863637)
                  ·
                    refine ⟨685795177172827354357777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58521188452081267571863637 685795177172827354357777)
                    ·
                      rfl

theorem cell22_2003372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_2003372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003372 prefixEnd_2003372 := by exact prefixLift 2003372
  have htrace : WordTrace (prefixWord ++ tailWord_2003372) baseStart_2003372 baseEnd_2003372 := by
    simpa [prefixWord, tailWord_2003372, baseEnd_2003372] using wordTrace_append hprefix tailTrace_2003372
  have hstable : (prefixWord ++ tailWord_2003372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003372).length < 2 ^ (prefixWord ++ tailWord_2003372).sum := by decide
  have hdescent : baseEnd_2003372 < baseStart_2003372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003485 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_2003485 : Nat := 118140960795 + 2003485 * 2 ^ 59
def prefixEnd_2003485 : Nat := 4983230072969 + 3 ^ 40 * 2003485 * 2
def baseEnd_2003485 : Nat := 685833859382132726282431

theorem tailTrace_2003485 : CollatzResearch.WordTrace tailWord_2003485 prefixEnd_2003485 685833859382132726282431 := by
  unfold tailWord_2003485
  simp only [CollatzResearch.WordTrace]
  refine ⟨73073101146723487841723909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48715400764482325227815939 73073101146723487841723909)
  ·
    refine ⟨13701206465010653970323233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73073101146723487841723909 13701206465010653970323233)
    ·
      refine ⟨10275904848757990477742425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13701206465010653970323233 10275904848757990477742425)
      ·
        refine ⟨7706928636568492858306819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10275904848757990477742425 7706928636568492858306819)
        ·
          refine ⟨11560392954852739287460229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7706928636568492858306819 11560392954852739287460229)
          ·
            refine ⟨2167573679034888616398793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11560392954852739287460229 2167573679034888616398793)
            ·
              refine ⟨1625680259276166462299095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167573679034888616398793 1625680259276166462299095)
              ·
                refine ⟨2438520388914249693448643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625680259276166462299095 2438520388914249693448643)
                ·
                  refine ⟨3657780583371374540172965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438520388914249693448643 3657780583371374540172965)
                  ·
                    refine ⟨685833859382132726282431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3657780583371374540172965 685833859382132726282431)
                    ·
                      rfl

theorem cell22_2003485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_2003485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003485 prefixEnd_2003485 := by exact prefixLift 2003485
  have htrace : WordTrace (prefixWord ++ tailWord_2003485) baseStart_2003485 baseEnd_2003485 := by
    simpa [prefixWord, tailWord_2003485, baseEnd_2003485] using wordTrace_append hprefix tailTrace_2003485
  have hstable : (prefixWord ++ tailWord_2003485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003485).length < 2 ^ (prefixWord ++ tailWord_2003485).sum := by decide
  have hdescent : baseEnd_2003485 < baseStart_2003485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003498 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2003498 : Nat := 118140960795 + 2003498 * 2 ^ 59
def prefixEnd_2003498 : Nat := 4983230072969 + 3 ^ 40 * 2003498 * 2
def baseEnd_2003498 : Nat := 685838309547805025707391

theorem tailTrace_2003498 : CollatzResearch.WordTrace tailWord_2003498 prefixEnd_2003498 685838309547805025707391 := by
  unfold tailWord_2003498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18268393823919097765486787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48715716863784260707964765 18268393823919097765486787)
  ·
    refine ⟨27402590735878646648230181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18268393823919097765486787 27402590735878646648230181)
    ·
      refine ⟨5137985762977246246543159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27402590735878646648230181 5137985762977246246543159)
      ·
        refine ⟨7706978644465869369814739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137985762977246246543159 7706978644465869369814739)
        ·
          refine ⟨11560467966698804054722109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7706978644465869369814739 11560467966698804054722109)
          ·
            refine ⟨4335175487512051520520791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11560467966698804054722109 4335175487512051520520791)
            ·
              refine ⟨6502763231268077280781187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335175487512051520520791 6502763231268077280781187)
              ·
                refine ⟨9754144846902115921171781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6502763231268077280781187 9754144846902115921171781)
                ·
                  refine ⟨1828902158794146735219709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9754144846902115921171781 1828902158794146735219709)
                  ·
                    refine ⟨685838309547805025707391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828902158794146735219709 685838309547805025707391)
                    ·
                      rfl

theorem cell22_2003498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2003498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003498 prefixEnd_2003498 := by exact prefixLift 2003498
  have htrace : WordTrace (prefixWord ++ tailWord_2003498) baseStart_2003498 baseEnd_2003498 := by
    simpa [prefixWord, tailWord_2003498, baseEnd_2003498] using wordTrace_append hprefix tailTrace_2003498
  have hstable : (prefixWord ++ tailWord_2003498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003498).length < 2 ^ (prefixWord ++ tailWord_2003498).sum := by decide
  have hdescent : baseEnd_2003498 < baseStart_2003498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003556 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 5]
def baseStart_2003556 : Nat := 118140960795 + 2003556 * 2 ^ 59
def prefixEnd_2003556 : Nat := 4983230072969 + 3 ^ 40 * 2003556 * 2
def baseEnd_2003556 : Nat := 228619388044370735919071

theorem tailTrace_2003556 : CollatzResearch.WordTrace tailWord_2003556 prefixEnd_2003556 228619388044370735919071 := by
  unfold tailWord_2003556
  simp only [CollatzResearch.WordTrace]
  refine ⟨36537845364733133483779261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48717127152977511311705681 36537845364733133483779261)
  ·
    refine ⟨13701692011774925056417223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36537845364733133483779261 13701692011774925056417223)
    ·
      refine ⟨20552538017662387584625835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13701692011774925056417223 20552538017662387584625835)
      ·
        refine ⟨30828807026493581376938753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20552538017662387584625835 30828807026493581376938753)
        ·
          refine ⟨23121605269870186032704065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30828807026493581376938753 23121605269870186032704065)
          ·
            refine ⟨17341203952402639524528049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23121605269870186032704065 17341203952402639524528049)
            ·
              refine ⟨13005902964301979643396037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17341203952402639524528049 13005902964301979643396037)
              ·
                refine ⟨2438606805806621183136757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13005902964301979643396037 2438606805806621183136757)
                ·
                  refine ⟨228619388044370735919071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2438606805806621183136757 228619388044370735919071)
                  ·
                    rfl

theorem cell22_2003556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_2003556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003556 prefixEnd_2003556 := by exact prefixLift 2003556
  have htrace : WordTrace (prefixWord ++ tailWord_2003556) baseStart_2003556 baseEnd_2003556 := by
    simpa [prefixWord, tailWord_2003556, baseEnd_2003556] using wordTrace_append hprefix tailTrace_2003556
  have hstable : (prefixWord ++ tailWord_2003556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003556).length < 2 ^ (prefixWord ++ tailWord_2003556).sum := by decide
  have hdescent : baseEnd_2003556 < baseStart_2003556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003569 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_2003569 : Nat := 118140960795 + 2003569 * 2 ^ 59
def prefixEnd_2003569 : Nat := 4983230072969 + 3 ^ 40 * 2003569 * 2
def baseEnd_2003569 : Nat := 685862614298784507182173

theorem tailTrace_2003569 : CollatzResearch.WordTrace tailWord_2003569 prefixEnd_2003569 685862614298784507182173 := by
  unfold tailWord_2003569
  simp only [CollatzResearch.WordTrace]
  refine ⟨73076164878419170187781761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48717443252279446791854507 73076164878419170187781761)
  ·
    refine ⟨54807123658814377640836321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73076164878419170187781761 54807123658814377640836321)
    ·
      refine ⟨41105342744110783230627241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54807123658814377640836321 41105342744110783230627241)
      ·
        refine ⟨30829007058083087422970431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41105342744110783230627241 30829007058083087422970431)
        ·
          refine ⟨46243510587124631134455647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30829007058083087422970431 46243510587124631134455647)
          ·
            refine ⟨69365265880686946701683471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46243510587124631134455647 69365265880686946701683471)
            ·
              refine ⟨104047898821030420052525207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69365265880686946701683471 104047898821030420052525207)
              ·
                refine ⟨156071848231545630078787811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104047898821030420052525207 156071848231545630078787811)
                ·
                  refine ⟨234107772347318445118181717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156071848231545630078787811 234107772347318445118181717)
                  ·
                    refine ⟨685862614298784507182173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 234107772347318445118181717 685862614298784507182173)
                    ·
                      rfl

theorem cell22_2003569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_2003569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003569 prefixEnd_2003569 := by exact prefixLift 2003569
  have htrace : WordTrace (prefixWord ++ tailWord_2003569) baseStart_2003569 baseEnd_2003569 := by
    simpa [prefixWord, tailWord_2003569, baseEnd_2003569] using wordTrace_append hprefix tailTrace_2003569
  have hstable : (prefixWord ++ tailWord_2003569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003569).length < 2 ^ (prefixWord ++ tailWord_2003569).sum := by decide
  have hdescent : baseEnd_2003569 < baseStart_2003569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003648 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_2003648 : Nat := 118140960795 + 2003648 * 2 ^ 59
def prefixEnd_2003648 : Nat := 4983230072969 + 3 ^ 40 * 2003648 * 2
def baseEnd_2003648 : Nat := 685889657613254634456931

theorem tailTrace_2003648 : CollatzResearch.WordTrace tailWord_2003648 prefixEnd_2003648 685889657613254634456931 := by
  unfold tailWord_2003648
  simp only [CollatzResearch.WordTrace]
  refine ⟨36539523122566483339953799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48719364163421977786605065 36539523122566483339953799)
  ·
    refine ⟨54809284683849725009930699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36539523122566483339953799 54809284683849725009930699)
    ·
      refine ⟨82213927025774587514896049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54809284683849725009930699 82213927025774587514896049)
      ·
        refine ⟨61660445269330940636172037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82213927025774587514896049 61660445269330940636172037)
        ·
          refine ⟨11561333487999551369282257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61660445269330940636172037 11561333487999551369282257)
          ·
            refine ⟨8671000115999663526961693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11561333487999551369282257 8671000115999663526961693)
            ·
              refine ⟨3251625043499873822610635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8671000115999663526961693 3251625043499873822610635)
              ·
                refine ⟨4877437565249810733915953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251625043499873822610635 4877437565249810733915953)
                ·
                  refine ⟨3658078173937358050436965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4877437565249810733915953 3658078173937358050436965)
                  ·
                    refine ⟨685889657613254634456931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658078173937358050436965 685889657613254634456931)
                    ·
                      rfl

theorem cell22_2003648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_2003648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003648 prefixEnd_2003648 := by exact prefixLift 2003648
  have htrace : WordTrace (prefixWord ++ tailWord_2003648) baseStart_2003648 baseEnd_2003648 := by
    simpa [prefixWord, tailWord_2003648, baseEnd_2003648] using wordTrace_append hprefix tailTrace_2003648
  have hstable : (prefixWord ++ tailWord_2003648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003648).length < 2 ^ (prefixWord ++ tailWord_2003648).sum := by decide
  have hdescent : baseEnd_2003648 < baseStart_2003648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003654 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2003654 : Nat := 118140960795 + 2003654 * 2 ^ 59
def prefixEnd_2003654 : Nat := 4983230072969 + 3 ^ 40 * 2003654 * 2
def baseEnd_2003654 : Nat := 685891711535872618806913

theorem tailTrace_2003654 : CollatzResearch.WordTrace tailWord_2003654 prefixEnd_2003654 685891711535872618806913 := by
  unfold tailWord_2003654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283727033847225928269563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48719510055407486469750677 2283727033847225928269563)
  ·
    refine ⟨3425590550770838892404345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2283727033847225928269563 3425590550770838892404345)
    ·
      refine ⟨2569192913078129169303259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3425590550770838892404345 2569192913078129169303259)
      ·
        refine ⟨3853789369617193753954889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569192913078129169303259 3853789369617193753954889)
        ·
          refine ⟨2890342027212895315466167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853789369617193753954889 2890342027212895315466167)
          ·
            refine ⟨4335513040819342973199251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890342027212895315466167 4335513040819342973199251)
            ·
              refine ⟨6503269561229014459798877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335513040819342973199251 6503269561229014459798877)
              ·
                refine ⟨2438726085460880422424579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6503269561229014459798877 2438726085460880422424579)
                ·
                  refine ⟨3658089128191320633636869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438726085460880422424579 3658089128191320633636869)
                  ·
                    refine ⟨685891711535872618806913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658089128191320633636869 685891711535872618806913)
                    ·
                      rfl

theorem cell22_2003654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2003654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003654 prefixEnd_2003654 := by exact prefixLift 2003654
  have htrace : WordTrace (prefixWord ++ tailWord_2003654) baseStart_2003654 baseEnd_2003654 := by
    simpa [prefixWord, tailWord_2003654, baseEnd_2003654] using wordTrace_append hprefix tailTrace_2003654
  have hstable : (prefixWord ++ tailWord_2003654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003654).length < 2 ^ (prefixWord ++ tailWord_2003654).sum := by decide
  have hdescent : baseEnd_2003654 < baseStart_2003654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003706 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_2003706 : Nat := 118140960795 + 2003706 * 2 ^ 59
def prefixEnd_2003706 : Nat := 4983230072969 + 3 ^ 40 * 2003706 * 2
def baseEnd_2003706 : Nat := 685909512198561816506753

theorem tailTrace_2003706 : CollatzResearch.WordTrace tailWord_2003706 prefixEnd_2003706 685909512198561816506753 := by
  unfold tailWord_2003706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18270290419730710646379743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48720774452615228390345981 18270290419730710646379743)
  ·
    refine ⟨27405435629596065969569615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18270290419730710646379743 27405435629596065969569615)
    ·
      refine ⟨41108153444394098954354423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27405435629596065969569615 41108153444394098954354423)
      ·
        refine ⟨61662230166591148431531635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41108153444394098954354423 61662230166591148431531635)
        ·
          refine ⟨92493345249886722647297453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61662230166591148431531635 92493345249886722647297453)
          ·
            refine ⟨34685004468707520992736545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92493345249886722647297453 34685004468707520992736545)
            ·
              refine ⟨26013753351530640744552409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34685004468707520992736545 26013753351530640744552409)
              ·
                refine ⟨19510315013647980558414307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26013753351530640744552409 19510315013647980558414307)
                ·
                  refine ⟨29265472520471970837621461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19510315013647980558414307 29265472520471970837621461)
                  ·
                    refine ⟨685909512198561816506753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29265472520471970837621461 685909512198561816506753)
                    ·
                      rfl

theorem cell22_2003706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_2003706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003706 prefixEnd_2003706 := by exact prefixLift 2003706
  have htrace : WordTrace (prefixWord ++ tailWord_2003706) baseStart_2003706 baseEnd_2003706 := by
    simpa [prefixWord, tailWord_2003706, baseEnd_2003706] using wordTrace_append hprefix tailTrace_2003706
  have hstable : (prefixWord ++ tailWord_2003706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003706).length < 2 ^ (prefixWord ++ tailWord_2003706).sum := by decide
  have hdescent : baseEnd_2003706 < baseStart_2003706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003738 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_2003738 : Nat := 118140960795 + 2003738 * 2 ^ 59
def prefixEnd_2003738 : Nat := 4983230072969 + 3 ^ 40 * 2003738 * 2
def baseEnd_2003738 : Nat := 685920466452524399706655

theorem tailTrace_2003738 : CollatzResearch.WordTrace tailWord_2003738 prefixEnd_2003738 685920466452524399706655 := by
  unfold tailWord_2003738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18270582203701728012670967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48721552543204608033789245 18270582203701728012670967)
  ·
    refine ⟨27405873305552592019006451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18270582203701728012670967 27405873305552592019006451)
    ·
      refine ⟨41108809958328888028509677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27405873305552592019006451 41108809958328888028509677)
      ·
        refine ⟨15415803734373333010691129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41108809958328888028509677 15415803734373333010691129)
        ·
          refine ⟨11561852800779999758018347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15415803734373333010691129 11561852800779999758018347)
          ·
            refine ⟨17342779201169999637027521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11561852800779999758018347 17342779201169999637027521)
            ·
              refine ⟨13007084400877499727770641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17342779201169999637027521 13007084400877499727770641)
              ·
                refine ⟨9755313300658124795827981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13007084400877499727770641 9755313300658124795827981)
                ·
                  refine ⟨3658242487746796798435493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9755313300658124795827981 3658242487746796798435493)
                  ·
                    refine ⟨685920466452524399706655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658242487746796798435493 685920466452524399706655)
                    ·
                      rfl

theorem cell22_2003738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_2003738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003738 prefixEnd_2003738 := by exact prefixLift 2003738
  have htrace : WordTrace (prefixWord ++ tailWord_2003738) baseStart_2003738 baseEnd_2003738 := by
    simpa [prefixWord, tailWord_2003738, baseEnd_2003738] using wordTrace_append hprefix tailTrace_2003738
  have hstable : (prefixWord ++ tailWord_2003738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003738).length < 2 ^ (prefixWord ++ tailWord_2003738).sum := by decide
  have hdescent : baseEnd_2003738 < baseStart_2003738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003768 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_2003768 : Nat := 118140960795 + 2003768 * 2 ^ 59
def prefixEnd_2003768 : Nat := 4983230072969 + 3 ^ 40 * 2003768 * 2
def baseEnd_2003768 : Nat := 685930736065614321456563

theorem tailTrace_2003768 : CollatzResearch.WordTrace tailWord_2003768 prefixEnd_2003768 685930736065614321456563 := by
  unfold tailWord_2003768
  simp only [CollatzResearch.WordTrace]
  refine ⟨36541711502349113587137979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48722282003132151449517305 36541711502349113587137979)
  ·
    refine ⟨54812567253523670380706969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36541711502349113587137979 54812567253523670380706969)
    ·
      refine ⟨41109425440142752785530227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54812567253523670380706969 41109425440142752785530227)
      ·
        refine ⟨61664138160214129178295341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41109425440142752785530227 61664138160214129178295341)
        ·
          refine ⟨23124051810080298441860753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61664138160214129178295341 23124051810080298441860753)
          ·
            refine ⟨17343038857560223831395565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23124051810080298441860753 17343038857560223831395565)
            ·
              refine ⟨6503639571585083936773337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17343038857560223831395565 6503639571585083936773337)
              ·
                refine ⟨4877729678688812952580003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6503639571585083936773337 4877729678688812952580003)
                ·
                  refine ⟨7316594518033219428870005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877729678688812952580003 7316594518033219428870005)
                  ·
                    refine ⟨685930736065614321456563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7316594518033219428870005 685930736065614321456563)
                    ·
                      rfl

theorem cell22_2003768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_2003768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003768 prefixEnd_2003768 := by exact prefixLift 2003768
  have htrace : WordTrace (prefixWord ++ tailWord_2003768) baseStart_2003768 baseEnd_2003768 := by
    simpa [prefixWord, tailWord_2003768, baseEnd_2003768] using wordTrace_append hprefix tailTrace_2003768
  have hstable : (prefixWord ++ tailWord_2003768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003768).length < 2 ^ (prefixWord ++ tailWord_2003768).sum := by decide
  have hdescent : baseEnd_2003768 < baseStart_2003768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003780 : List Nat := [2, 3, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2003780 : Nat := 118140960795 + 2003780 * 2 ^ 59
def prefixEnd_2003780 : Nat := 4983230072969 + 3 ^ 40 * 2003780 * 2
def baseEnd_2003780 : Nat := 685934843910850290156527

theorem tailTrace_2003780 : CollatzResearch.WordTrace tailWord_2003780 prefixEnd_2003780 685934843910850290156527 := by
  unfold tailWord_2003780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36541930340327376611856397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48722573787103168815808529 36541930340327376611856397)
  ·
    refine ⟨13703223877622766229446149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36541930340327376611856397 13703223877622766229446149)
    ·
      refine ⟨2569354477054268668021153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13703223877622766229446149 2569354477054268668021153)
      ·
        refine ⟨1927015857790701501015865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2569354477054268668021153 1927015857790701501015865)
        ·
          refine ⟨1445261893343026125761899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1927015857790701501015865 1445261893343026125761899)
          ·
            refine ⟨2167892840014539188642849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445261893343026125761899 2167892840014539188642849)
            ·
              refine ⟨1625919630010904391482137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167892840014539188642849 1625919630010904391482137)
              ·
                refine ⟨1219439722508178293611603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1625919630010904391482137 1219439722508178293611603)
                ·
                  refine ⟨1829159583762267440417405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219439722508178293611603 1829159583762267440417405)
                  ·
                    refine ⟨685934843910850290156527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829159583762267440417405 685934843910850290156527)
                    ·
                      rfl

theorem cell22_2003780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2003780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003780 prefixEnd_2003780 := by exact prefixLift 2003780
  have htrace : WordTrace (prefixWord ++ tailWord_2003780) baseStart_2003780 baseEnd_2003780 := by
    simpa [prefixWord, tailWord_2003780, baseEnd_2003780] using wordTrace_append hprefix tailTrace_2003780
  have hstable : (prefixWord ++ tailWord_2003780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003780).length < 2 ^ (prefixWord ++ tailWord_2003780).sum := by decide
  have hdescent : baseEnd_2003780 < baseStart_2003780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003785 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 2, 3]
def baseStart_2003785 : Nat := 118140960795 + 2003785 * 2 ^ 59
def prefixEnd_2003785 : Nat := 4983230072969 + 3 ^ 40 * 2003785 * 2
def baseEnd_2003785 : Nat := 685936555513031943781511

theorem tailTrace_2003785 : CollatzResearch.WordTrace tailWord_2003785 prefixEnd_2003785 685936555513031943781511 := by
  unfold tailWord_2003785
  simp only [CollatzResearch.WordTrace]
  refine ⟨73084043045636639077644809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48722695363757759385096539 73084043045636639077644809)
  ·
    refine ⟨54813032284227479308233607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73084043045636639077644809 54813032284227479308233607)
    ·
      refine ⟨82219548426341218962350411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54813032284227479308233607 82219548426341218962350411)
      ·
        refine ⟨123329322639511828443525617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82219548426341218962350411 123329322639511828443525617)
        ·
          refine ⟨92496991979633871332644213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123329322639511828443525617 92496991979633871332644213)
          ·
            refine ⟨8671592998090675437435395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92496991979633871332644213 8671592998090675437435395)
            ·
              refine ⟨13007389497136013156153093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671592998090675437435395 13007389497136013156153093)
              ·
                refine ⟨2438885530713002466778705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13007389497136013156153093 2438885530713002466778705)
                ·
                  refine ⟨1829164148034751850084029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2438885530713002466778705 1829164148034751850084029)
                  ·
                    refine ⟨685936555513031943781511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829164148034751850084029 685936555513031943781511)
                    ·
                      rfl

theorem cell22_2003785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_2003785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003785 prefixEnd_2003785 := by exact prefixLift 2003785
  have htrace : WordTrace (prefixWord ++ tailWord_2003785) baseStart_2003785 baseEnd_2003785 := by
    simpa [prefixWord, tailWord_2003785, baseEnd_2003785] using wordTrace_append hprefix tailTrace_2003785
  have hstable : (prefixWord ++ tailWord_2003785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003785).length < 2 ^ (prefixWord ++ tailWord_2003785).sum := by decide
  have hdescent : baseEnd_2003785 < baseStart_2003785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003815 : List Nat := [1, 1, 5, 1, 2, 3, 3, 6]
def baseStart_2003815 : Nat := 118140960795 + 2003815 * 2 ^ 59
def prefixEnd_2003815 : Nat := 4983230072969 + 3 ^ 40 * 2003815 * 2
def baseEnd_2003815 : Nat := 76216313902902429503491

theorem tailTrace_2003815 : CollatzResearch.WordTrace tailWord_2003815 prefixEnd_2003815 76216313902902429503491 := by
  unfold tailWord_2003815
  simp only [CollatzResearch.WordTrace]
  refine ⟨73085137235527954201236899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48723424823685302800824599 73085137235527954201236899)
  ·
    refine ⟨109627705853291931301855349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73085137235527954201236899 109627705853291931301855349)
    ·
      refine ⟨10277597423746118559548939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109627705853291931301855349 10277597423746118559548939)
      ·
        refine ⟨15416396135619177839323409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10277597423746118559548939 15416396135619177839323409)
        ·
          refine ⟨11562297101714383379492557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15416396135619177839323409 11562297101714383379492557)
          ·
            refine ⟨4335861413142893767309709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11562297101714383379492557 4335861413142893767309709)
            ·
              refine ⟨1625948029928585162741141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4335861413142893767309709 1625948029928585162741141)
              ·
                refine ⟨76216313902902429503491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1625948029928585162741141 76216313902902429503491)
                ·
                  rfl

theorem cell22_2003815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 6].length) (baseStart_2003815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003815 prefixEnd_2003815 := by exact prefixLift 2003815
  have htrace : WordTrace (prefixWord ++ tailWord_2003815) baseStart_2003815 baseEnd_2003815 := by
    simpa [prefixWord, tailWord_2003815, baseEnd_2003815] using wordTrace_append hprefix tailTrace_2003815
  have hstable : (prefixWord ++ tailWord_2003815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003815).length < 2 ^ (prefixWord ++ tailWord_2003815).sum := by decide
  have hdescent : baseEnd_2003815 < baseStart_2003815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003843 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 7]
def baseStart_2003843 : Nat := 118140960795 + 2003843 * 2 ^ 59
def prefixEnd_2003843 : Nat := 4983230072969 + 3 ^ 40 * 2003843 * 2
def baseEnd_2003843 : Nat := 228652136699446375277111

theorem tailTrace_2003843 : CollatzResearch.WordTrace tailWord_2003843 prefixEnd_2003843 228652136699446375277111 := by
  unfold tailWord_2003843
  simp only [CollatzResearch.WordTrace]
  refine ⟨73086158479426514983256183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48724105652951009988837455 73086158479426514983256183)
  ·
    refine ⟨109629237719139772474884275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73086158479426514983256183 109629237719139772474884275)
    ·
      refine ⟨164443856578709658712326413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109629237719139772474884275 164443856578709658712326413)
      ·
        refine ⟨61666446217016122017122405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164443856578709658712326413 61666446217016122017122405)
        ·
          refine ⟨11562458665690522878210451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61666446217016122017122405 11562458665690522878210451)
          ·
            refine ⟨17343687998535784317315677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11562458665690522878210451 17343687998535784317315677)
            ·
              refine ⟨6503882999450919118993379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17343687998535784317315677 6503882999450919118993379)
              ·
                refine ⟨9755824499176378678490069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503882999450919118993379 9755824499176378678490069)
                ·
                  refine ⟨228652136699446375277111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9755824499176378678490069 228652136699446375277111)
                  ·
                    rfl

theorem cell22_2003843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 7].length) (baseStart_2003843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003843 prefixEnd_2003843 := by exact prefixLift 2003843
  have htrace : WordTrace (prefixWord ++ tailWord_2003843) baseStart_2003843 baseEnd_2003843 := by
    simpa [prefixWord, tailWord_2003843, baseEnd_2003843] using wordTrace_append hprefix tailTrace_2003843
  have hstable : (prefixWord ++ tailWord_2003843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003843).length < 2 ^ (prefixWord ++ tailWord_2003843).sum := by decide
  have hdescent : baseEnd_2003843 < baseStart_2003843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003847 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 3, 3]
def baseStart_2003847 : Nat := 118140960795 + 2003847 * 2 ^ 59
def prefixEnd_2003847 : Nat := 4983230072969 + 3 ^ 40 * 2003847 * 2
def baseEnd_2003847 : Nat := 685957779380084448731321

theorem tailTrace_2003847 : CollatzResearch.WordTrace tailWord_2003847 prefixEnd_2003847 685957779380084448731321 := by
  unfold tailWord_2003847
  simp only [CollatzResearch.WordTrace]
  refine ⟨73086304371412023666401795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48724202914274682444267863 73086304371412023666401795)
  ·
    refine ⟨109629456557118035499602693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73086304371412023666401795 109629456557118035499602693)
    ·
      refine ⟨20555523104459631656175505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109629456557118035499602693 20555523104459631656175505)
      ·
        refine ⟨15416642328344723742131629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20555523104459631656175505 15416642328344723742131629)
        ·
          refine ⟨5781240873129271403299361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15416642328344723742131629 5781240873129271403299361)
          ·
            refine ⟨4335930654846953552474521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781240873129271403299361 4335930654846953552474521)
            ·
              refine ⟨3251947991135215164355891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4335930654846953552474521 3251947991135215164355891)
              ·
                refine ⟨4877921986702822746533837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251947991135215164355891 4877921986702822746533837)
                ·
                  refine ⟨1829220745013558529950189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4877921986702822746533837 1829220745013558529950189)
                  ·
                    refine ⟨685957779380084448731321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829220745013558529950189 685957779380084448731321)
                    ·
                      rfl

theorem cell22_2003847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_2003847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003847 prefixEnd_2003847 := by exact prefixLift 2003847
  have htrace : WordTrace (prefixWord ++ tailWord_2003847) baseStart_2003847 baseEnd_2003847 := by
    simpa [prefixWord, tailWord_2003847, baseEnd_2003847] using wordTrace_append hprefix tailTrace_2003847
  have hstable : (prefixWord ++ tailWord_2003847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003847).length < 2 ^ (prefixWord ++ tailWord_2003847).sum := by decide
  have hdescent : baseEnd_2003847 < baseStart_2003847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003903 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 5, 5]
def baseStart_2003903 : Nat := 118140960795 + 2003903 * 2 ^ 59
def prefixEnd_2003903 : Nat := 4983230072969 + 3 ^ 40 * 2003903 * 2
def baseEnd_2003903 : Nat := 685976949324518969331149

theorem tailTrace_2003903 : CollatzResearch.WordTrace tailWord_2003903 prefixEnd_2003903 685976949324518969331149 := by
  unfold tailWord_2003903
  simp only [CollatzResearch.WordTrace]
  refine ⟨73088346859209145230440363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48725564572806096820293575 73088346859209145230440363)
  ·
    refine ⟨109632520288813717845660545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73088346859209145230440363 109632520288813717845660545)
    ·
      refine ⟨82224390216610288384245409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109632520288813717845660545 82224390216610288384245409)
      ·
        refine ⟨61668292662457716288184057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82224390216610288384245409 61668292662457716288184057)
        ·
          refine ⟨46251219496843287216138043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61668292662457716288184057 46251219496843287216138043)
          ·
            refine ⟨69376829245264930824207065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46251219496843287216138043 69376829245264930824207065)
            ·
              refine ⟨52032621933948698118155299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69376829245264930824207065 52032621933948698118155299)
              ·
                refine ⟨78048932900923047177232949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52032621933948698118155299 78048932900923047177232949)
                ·
                  refine ⟨7317087459461535672865589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78048932900923047177232949 7317087459461535672865589)
                  ·
                    refine ⟨685976949324518969331149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7317087459461535672865589 685976949324518969331149)
                    ·
                      rfl

theorem cell22_2003903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_2003903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003903 prefixEnd_2003903 := by exact prefixLift 2003903
  have htrace : WordTrace (prefixWord ++ tailWord_2003903) baseStart_2003903 baseEnd_2003903 := by
    simpa [prefixWord, tailWord_2003903, baseEnd_2003903] using wordTrace_append hprefix tailTrace_2003903
  have hstable : (prefixWord ++ tailWord_2003903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003903).length < 2 ^ (prefixWord ++ tailWord_2003903).sum := by decide
  have hdescent : baseEnd_2003903 < baseStart_2003903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003924 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2003924 : Nat := 118140960795 + 2003924 * 2 ^ 59
def prefixEnd_2003924 : Nat := 4983230072969 + 3 ^ 40 * 2003924 * 2
def baseEnd_2003924 : Nat := 685984138053681914556085

theorem tailTrace_2003924 : CollatzResearch.WordTrace tailWord_2003924 prefixEnd_2003924 685984138053681914556085 := by
  unfold tailWord_2003924
  simp only [CollatzResearch.WordTrace]
  refine ⟨36544556396066532908477413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48726075194755377211303217 36544556396066532908477413)
  ·
    refine ⟨6852104324262474920339515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36544556396066532908477413 6852104324262474920339515)
    ·
      refine ⟨10278156486393712380509273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6852104324262474920339515 10278156486393712380509273)
      ·
        refine ⟨7708617364795284285381955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10278156486393712380509273 7708617364795284285381955)
        ·
          refine ⟨11562926047192926428072933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708617364795284285381955 11562926047192926428072933)
          ·
            refine ⟨2168048633848673705263675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11562926047192926428072933 2168048633848673705263675)
            ·
              refine ⟨3252072950773010557895513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168048633848673705263675 3252072950773010557895513)
              ·
                refine ⟨2439054713079757918421635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3252072950773010557895513 2439054713079757918421635)
                ·
                  refine ⟨3658582069619636877632453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439054713079757918421635 3658582069619636877632453)
                  ·
                    refine ⟨685984138053681914556085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658582069619636877632453 685984138053681914556085)
                    ·
                      rfl

theorem cell22_2003924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2003924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003924 prefixEnd_2003924 := by exact prefixLift 2003924
  have htrace : WordTrace (prefixWord ++ tailWord_2003924) baseStart_2003924 baseEnd_2003924 := by
    simpa [prefixWord, tailWord_2003924, baseEnd_2003924] using wordTrace_append hprefix tailTrace_2003924
  have hstable : (prefixWord ++ tailWord_2003924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003924).length < 2 ^ (prefixWord ++ tailWord_2003924).sum := by decide
  have hdescent : baseEnd_2003924 < baseStart_2003924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003941 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_2003941 : Nat := 118140960795 + 2003941 * 2 ^ 59
def prefixEnd_2003941 : Nat := 4983230072969 + 3 ^ 40 * 2003941 * 2
def baseEnd_2003941 : Nat := 685989957501099536881033

theorem tailTrace_2003941 : CollatzResearch.WordTrace tailWord_2003941 prefixEnd_2003941 685989957501099536881033 := by
  unfold tailWord_2003941
  simp only [CollatzResearch.WordTrace]
  refine ⟨73089732833071477720323677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48726488555380985146882451 73089732833071477720323677)
  ·
    refine ⟨27408649812401804145121379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73089732833071477720323677 27408649812401804145121379)
    ·
      refine ⟨41112974718602706217682069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27408649812401804145121379 41112974718602706217682069)
      ·
        refine ⟨1927170689934501853953847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41112974718602706217682069 1927170689934501853953847)
        ·
          refine ⟨2890756034901752780930771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927170689934501853953847 2890756034901752780930771)
          ·
            refine ⟨4336134052352629171396157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890756034901752780930771 4336134052352629171396157)
            ·
              refine ⟨1626050269632235939273559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4336134052352629171396157 1626050269632235939273559)
              ·
                refine ⟨2439075404448353908910339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626050269632235939273559 2439075404448353908910339)
                ·
                  refine ⟨3658613106672530863365509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439075404448353908910339 3658613106672530863365509)
                  ·
                    refine ⟨685989957501099536881033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658613106672530863365509 685989957501099536881033)
                    ·
                      rfl

theorem cell22_2003941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_2003941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003941 prefixEnd_2003941 := by exact prefixLift 2003941
  have htrace : WordTrace (prefixWord ++ tailWord_2003941) baseStart_2003941 baseEnd_2003941 := by
    simpa [prefixWord, tailWord_2003941, baseEnd_2003941] using wordTrace_append hprefix tailTrace_2003941
  have hstable : (prefixWord ++ tailWord_2003941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003941).length < 2 ^ (prefixWord ++ tailWord_2003941).sum := by decide
  have hdescent : baseEnd_2003941 < baseStart_2003941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003950 : List Nat := [4, 1, 2, 1, 4, 10]
def baseStart_2003950 : Nat := 118140960795 + 2003950 * 2 ^ 59
def prefixEnd_2003950 : Nat := 4983230072969 + 3 ^ 40 * 2003950 * 2
def baseEnd_2003950 : Nat := 8469049856605265597605

theorem tailTrace_2003950 : CollatzResearch.WordTrace tailWord_2003950 prefixEnd_2003950 8469049856605265597605 := by
  unfold tailWord_2003950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136257636254859032175163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48726707393359248171600869 9136257636254859032175163)
  ·
    refine ⟨13704386454382288548262745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9136257636254859032175163 13704386454382288548262745)
    ·
      refine ⟨10278289840786716411197059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13704386454382288548262745 10278289840786716411197059)
      ·
        refine ⟨15417434761180074616795589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10278289840786716411197059 15417434761180074616795589)
        ·
          refine ⟨2890769017721263990649173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15417434761180074616795589 2890769017721263990649173)
          ·
            refine ⟨8469049856605265597605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2890769017721263990649173 8469049856605265597605)
            ·
              rfl

theorem cell22_2003950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 10].length) (baseStart_2003950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003950 prefixEnd_2003950 := by exact prefixLift 2003950
  have htrace : WordTrace (prefixWord ++ tailWord_2003950) baseStart_2003950 baseEnd_2003950 := by
    simpa [prefixWord, tailWord_2003950, baseEnd_2003950] using wordTrace_append hprefix tailTrace_2003950
  have hstable : (prefixWord ++ tailWord_2003950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003950).length < 2 ^ (prefixWord ++ tailWord_2003950).sum := by decide
  have hdescent : baseEnd_2003950 < baseStart_2003950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003982 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_2003982 : Nat := 118140960795 + 2003982 * 2 ^ 59
def prefixEnd_2003982 : Nat := 4983230072969 + 3 ^ 40 * 2003982 * 2
def baseEnd_2003982 : Nat := 686003992638989096605907

theorem tailTrace_2003982 : CollatzResearch.WordTrace tailWord_2003982 prefixEnd_2003982 686003992638989096605907 := by
  unfold tailWord_2003982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136403528240367715320775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48727485483948627815044133 9136403528240367715320775)
  ·
    refine ⟨13704605292360551572981163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9136403528240367715320775 13704605292360551572981163)
    ·
      refine ⟨20556907938540827359471745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13704605292360551572981163 20556907938540827359471745)
      ·
        refine ⟨15417680953905620519603809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20556907938540827359471745 15417680953905620519603809)
        ·
          refine ⟨11563260715429215389702857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15417680953905620519603809 11563260715429215389702857)
          ·
            refine ⟨8672445536571911542277143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11563260715429215389702857 8672445536571911542277143)
            ·
              refine ⟨13008668304857867313415715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672445536571911542277143 13008668304857867313415715)
              ·
                refine ⟨19513002457286800970123573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13008668304857867313415715 19513002457286800970123573)
                ·
                  refine ⟨1829343980370637590949085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19513002457286800970123573 1829343980370637590949085)
                  ·
                    refine ⟨686003992638989096605907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829343980370637590949085 686003992638989096605907)
                    ·
                      rfl

theorem cell22_2003982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_2003982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003982 prefixEnd_2003982 := by exact prefixLift 2003982
  have htrace : WordTrace (prefixWord ++ tailWord_2003982) baseStart_2003982 baseEnd_2003982 := by
    simpa [prefixWord, tailWord_2003982, baseEnd_2003982] using wordTrace_append hprefix tailTrace_2003982
  have hstable : (prefixWord ++ tailWord_2003982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003982).length < 2 ^ (prefixWord ++ tailWord_2003982).sum := by decide
  have hdescent : baseEnd_2003982 < baseStart_2003982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003986 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2003986 : Nat := 118140960795 + 2003986 * 2 ^ 59
def prefixEnd_2003986 : Nat := 4983230072969 + 3 ^ 40 * 2003986 * 2
def baseEnd_2003986 : Nat := 686005361920734419505895

theorem tailTrace_2003986 : CollatzResearch.WordTrace tailWord_2003986 prefixEnd_2003986 686005361920734419505895 := by
  unfold tailWord_2003986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18272843529477112601427953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48727582745272300270474541 18272843529477112601427953)
  ·
    refine ⟨13704632647107834451070965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18272843529477112601427953 13704632647107834451070965)
    ·
      refine ⟨1284809310666359479787903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13704632647107834451070965 1284809310666359479787903)
      ·
        refine ⟨1927213965999539219681855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284809310666359479787903 1927213965999539219681855)
        ·
          refine ⟨2890820948999308829522783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927213965999539219681855 2890820948999308829522783)
          ·
            refine ⟨4336231423498963244284175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890820948999308829522783 4336231423498963244284175)
            ·
              refine ⟨6504347135248444866426263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336231423498963244284175 6504347135248444866426263)
              ·
                refine ⟨9756520702872667299639395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504347135248444866426263 9756520702872667299639395)
                ·
                  refine ⟨14634781054309000949459093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9756520702872667299639395 14634781054309000949459093)
                  ·
                    refine ⟨686005361920734419505895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14634781054309000949459093 686005361920734419505895)
                    ·
                      rfl

theorem cell22_2003986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2003986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003986 prefixEnd_2003986 := by exact prefixLift 2003986
  have htrace : WordTrace (prefixWord ++ tailWord_2003986) baseStart_2003986 baseEnd_2003986 := by
    simpa [prefixWord, tailWord_2003986, baseEnd_2003986] using wordTrace_append hprefix tailTrace_2003986
  have hstable : (prefixWord ++ tailWord_2003986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003986).length < 2 ^ (prefixWord ++ tailWord_2003986).sum := by decide
  have hdescent : baseEnd_2003986 < baseStart_2003986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003999 : List Nat := [1, 1, 2, 4, 1, 3, 1, 5, 1, 3]
def baseStart_2003999 : Nat := 118140960795 + 2003999 * 2 ^ 59
def prefixEnd_2003999 : Nat := 4983230072969 + 3 ^ 40 * 2003999 * 2
def baseEnd_2003999 : Nat := 686009812086406718930855

theorem tailTrace_2003999 : CollatzResearch.WordTrace tailWord_2003999 prefixEnd_2003999 686009812086406718930855 := by
  unfold tailWord_2003999
  simp only [CollatzResearch.WordTrace]
  refine ⟨73091848266861353625935051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48727898844574235750623367 73091848266861353625935051)
  ·
    refine ⟨109637772400292030438902577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73091848266861353625935051 109637772400292030438902577)
    ·
      refine ⟨82228329300219022829176933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109637772400292030438902577 82228329300219022829176933)
      ·
        refine ⟨15417811743791066780470675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82228329300219022829176933 15417811743791066780470675)
        ·
          refine ⟨23126717615686600170706013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15417811743791066780470675 23126717615686600170706013)
          ·
            refine ⟨8672519105882475064014755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23126717615686600170706013 8672519105882475064014755)
            ·
              refine ⟨13008778658823712596022133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672519105882475064014755 13008778658823712596022133)
              ·
                refine ⟨1219572999264723055877075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13008778658823712596022133 1219572999264723055877075)
                ·
                  refine ⟨1829359498897084583815613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219572999264723055877075 1829359498897084583815613)
                  ·
                    refine ⟨686009812086406718930855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829359498897084583815613 686009812086406718930855)
                    ·
                      rfl

theorem cell22_2003999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 3].length) (baseStart_2003999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2003999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2003999 prefixEnd_2003999 := by exact prefixLift 2003999
  have htrace : WordTrace (prefixWord ++ tailWord_2003999) baseStart_2003999 baseEnd_2003999 := by
    simpa [prefixWord, tailWord_2003999, baseEnd_2003999] using wordTrace_append hprefix tailTrace_2003999
  have hstable : (prefixWord ++ tailWord_2003999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003999).length < 2 ^ (prefixWord ++ tailWord_2003999).sum := by decide
  have hdescent : baseEnd_2003999 < baseStart_2003999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004029 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 5]
def baseStart_2004029 : Nat := 118140960795 + 2004029 * 2 ^ 59
def prefixEnd_2004029 : Nat := 4983230072969 + 3 ^ 40 * 2004029 * 2
def baseEnd_2004029 : Nat := 228673360566498880226921

theorem tailTrace_2004029 : CollatzResearch.WordTrace tailWord_2004029 prefixEnd_2004029 228673360566498880226921 := by
  unfold tailWord_2004029
  simp only [CollatzResearch.WordTrace]
  refine ⟨73092942456752668749527141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48728628304501779166351427 73092942456752668749527141)
  ·
    refine ⟨13704926710641125390536339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73092942456752668749527141 13704926710641125390536339)
    ·
      refine ⟨20557390065961688085804509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13704926710641125390536339 20557390065961688085804509)
      ·
        refine ⟨7709021274735633032176691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20557390065961688085804509 7709021274735633032176691)
        ·
          refine ⟨11563531912103449548265037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709021274735633032176691 11563531912103449548265037)
          ·
            refine ⟨4336324467038793580599389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11563531912103449548265037 4336324467038793580599389)
            ·
              refine ⟨1626121675139547592724771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4336324467038793580599389 1626121675139547592724771)
              ·
                refine ⟨2439182512709321389087157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626121675139547592724771 2439182512709321389087157)
                ·
                  refine ⟨228673360566498880226921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2439182512709321389087157 228673360566498880226921)
                  ·
                    rfl

theorem cell22_2004029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_2004029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004029 prefixEnd_2004029 := by exact prefixLift 2004029
  have htrace : WordTrace (prefixWord ++ tailWord_2004029) baseStart_2004029 baseEnd_2004029 := by
    simpa [prefixWord, tailWord_2004029, baseEnd_2004029] using wordTrace_append hprefix tailTrace_2004029
  have hstable : (prefixWord ++ tailWord_2004029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004029).length < 2 ^ (prefixWord ++ tailWord_2004029).sum := by decide
  have hdescent : baseEnd_2004029 < baseStart_2004029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004040 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 6]
def baseStart_2004040 : Nat := 118140960795 + 2004040 * 2 ^ 59
def prefixEnd_2004040 : Nat := 4983230072969 + 3 ^ 40 * 2004040 * 2
def baseEnd_2004040 : Nat := 228674615741432092885243

theorem tailTrace_2004040 : CollatzResearch.WordTrace tailWord_2004040 prefixEnd_2004040 228674615741432092885243 := by
  unfold tailWord_2004040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36546671829856408814088787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48728895773141878418785049 36546671829856408814088787)
  ·
    refine ⟨54820007744784613221133181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36546671829856408814088787 54820007744784613221133181)
    ·
      refine ⟨20557502904294229957924943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54820007744784613221133181 20557502904294229957924943)
      ·
        refine ⟨30836254356441344936887415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20557502904294229957924943 30836254356441344936887415)
        ·
          refine ⟨46254381534662017405331123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30836254356441344936887415 46254381534662017405331123)
          ·
            refine ⟨69381572301993026107996685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46254381534662017405331123 69381572301993026107996685)
            ·
              refine ⟨26018089613247384790498757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69381572301993026107996685 26018089613247384790498757)
              ·
                refine ⟨4878391802483884648218517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26018089613247384790498757 4878391802483884648218517)
                ·
                  refine ⟨228674615741432092885243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4878391802483884648218517 228674615741432092885243)
                  ·
                    rfl

theorem cell22_2004040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_2004040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004040 prefixEnd_2004040 := by exact prefixLift 2004040
  have htrace : WordTrace (prefixWord ++ tailWord_2004040) baseStart_2004040 baseEnd_2004040 := by
    simpa [prefixWord, tailWord_2004040, baseEnd_2004040] using wordTrace_append hprefix tailTrace_2004040
  have hstable : (prefixWord ++ tailWord_2004040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004040).length < 2 ^ (prefixWord ++ tailWord_2004040).sum := by decide
  have hdescent : baseEnd_2004040 < baseStart_2004040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004042 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_2004042 : Nat := 118140960795 + 2004042 * 2 ^ 59
def prefixEnd_2004042 : Nat := 4983230072969 + 3 ^ 40 * 2004042 * 2
def baseEnd_2004042 : Nat := 686024531865168940105723

theorem tailTrace_2004042 : CollatzResearch.WordTrace tailWord_2004042 prefixEnd_2004042 686024531865168940105723 := by
  unfold tailWord_2004042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273354151426392992437595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48728944403803714646500253 18273354151426392992437595)
  ·
    refine ⟨27410031227139589488656393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18273354151426392992437595 27410031227139589488656393)
    ·
      refine ⟨20557523420354692116492295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27410031227139589488656393 20557523420354692116492295)
      ·
        refine ⟨30836285130532038174738443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20557523420354692116492295 30836285130532038174738443)
        ·
          refine ⟨46254427695798057262107665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30836285130532038174738443 46254427695798057262107665)
          ·
            refine ⟨34690820771848542946580749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46254427695798057262107665 34690820771848542946580749)
            ·
              refine ⟨13009057789443203604967781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34690820771848542946580749 13009057789443203604967781)
              ·
                refine ⟨2439198335520600675931459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13009057789443203604967781 2439198335520600675931459)
                ·
                  refine ⟨3658797503280901013897189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439198335520600675931459 3658797503280901013897189)
                  ·
                    refine ⟨686024531865168940105723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658797503280901013897189 686024531865168940105723)
                    ·
                      rfl

theorem cell22_2004042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_2004042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004042 prefixEnd_2004042 := by exact prefixLift 2004042
  have htrace : WordTrace (prefixWord ++ tailWord_2004042) baseStart_2004042 baseEnd_2004042 := by
    simpa [prefixWord, tailWord_2004042, baseEnd_2004042] using wordTrace_append hprefix tailTrace_2004042
  have hstable : (prefixWord ++ tailWord_2004042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004042).length < 2 ^ (prefixWord ++ tailWord_2004042).sum := by decide
  have hdescent : baseEnd_2004042 < baseStart_2004042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004055 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2004055 : Nat := 118140960795 + 2004055 * 2 ^ 59
def prefixEnd_2004055 : Nat := 4983230072969 + 3 ^ 40 * 2004055 * 2
def baseEnd_2004055 : Nat := 686028982030841239530683

theorem tailTrace_2004055 : CollatzResearch.WordTrace tailWord_2004055 prefixEnd_2004055 686028982030841239530683 := by
  unfold tailWord_2004055
  simp only [CollatzResearch.WordTrace]
  refine ⟨73093890754658475189973619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48729260503105650126649079 73093890754658475189973619)
  ·
    refine ⟨109640836131987712784960429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73093890754658475189973619 109640836131987712784960429)
    ·
      refine ⟨41115313549495392294360161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109640836131987712784960429 41115313549495392294360161)
      ·
        refine ⟨30836485162121544220770121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41115313549495392294360161 30836485162121544220770121)
        ·
          refine ⟨23127363871591158165577591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30836485162121544220770121 23127363871591158165577591)
          ·
            refine ⟨34691045807386737248366387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23127363871591158165577591 34691045807386737248366387)
            ·
              refine ⟨52036568711080105872549581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34691045807386737248366387 52036568711080105872549581)
              ·
                refine ⟨19513713266655039702206093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52036568711080105872549581 19513713266655039702206093)
                ·
                  refine ⟨7317642474995639888327285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19513713266655039702206093 7317642474995639888327285)
                  ·
                    refine ⟨686028982030841239530683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7317642474995639888327285 686028982030841239530683)
                    ·
                      rfl

theorem cell22_2004055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2004055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004055 prefixEnd_2004055 := by exact prefixLift 2004055
  have htrace : WordTrace (prefixWord ++ tailWord_2004055) baseStart_2004055 baseEnd_2004055 := by
    simpa [prefixWord, tailWord_2004055, baseEnd_2004055] using wordTrace_append hprefix tailTrace_2004055
  have hstable : (prefixWord ++ tailWord_2004055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004055).length < 2 ^ (prefixWord ++ tailWord_2004055).sum := by decide
  have hdescent : baseEnd_2004055 < baseStart_2004055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004057 : List Nat := [1, 2, 1, 2, 2, 1, 2, 7, 4]
def baseStart_2004057 : Nat := 118140960795 + 2004057 * 2 ^ 59
def prefixEnd_2004057 : Nat := 4983230072969 + 3 ^ 40 * 2004057 * 2
def baseEnd_2004057 : Nat := 228676555557237966993559

theorem tailTrace_2004057 : CollatzResearch.WordTrace tailWord_2004057 prefixEnd_2004057 228676555557237966993559 := by
  unfold tailWord_2004057
  simp only [CollatzResearch.WordTrace]
  refine ⟨73093963700651229531546425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48729309133767486354364283 73093963700651229531546425)
  ·
    refine ⟨54820472775488422148659819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73093963700651229531546425 54820472775488422148659819)
    ·
      refine ⟨82230709163232633222989729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54820472775488422148659819 82230709163232633222989729)
      ·
        refine ⟨61673031872424474917242297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82230709163232633222989729 61673031872424474917242297)
        ·
          refine ⟨46254773904318356187931723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61673031872424474917242297 46254773904318356187931723)
          ·
            refine ⟨69382160856477534281897585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46254773904318356187931723 69382160856477534281897585)
            ·
              refine ⟨52036620642358150711423189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69382160856477534281897585 52036620642358150711423189)
              ·
                refine ⟨1219608296305269157298981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52036620642358150711423189 1219608296305269157298981)
                ·
                  refine ⟨228676555557237966993559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219608296305269157298981 228676555557237966993559)
                  ·
                    rfl

theorem cell22_2004057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 4].length) (baseStart_2004057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004057 prefixEnd_2004057 := by exact prefixLift 2004057
  have htrace : WordTrace (prefixWord ++ tailWord_2004057) baseStart_2004057 baseEnd_2004057 := by
    simpa [prefixWord, tailWord_2004057, baseEnd_2004057] using wordTrace_append hprefix tailTrace_2004057
  have hstable : (prefixWord ++ tailWord_2004057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004057).length < 2 ^ (prefixWord ++ tailWord_2004057).sum := by decide
  have hdescent : baseEnd_2004057 < baseStart_2004057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004074 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_2004074 : Nat := 118140960795 + 2004074 * 2 ^ 59
def prefixEnd_2004074 : Nat := 4983230072969 + 3 ^ 40 * 2004074 * 2
def baseEnd_2004074 : Nat := 228678495373043841101875

theorem tailTrace_2004074 : CollatzResearch.WordTrace tailWord_2004074 prefixEnd_2004074 228678495373043841101875 := by
  unfold tailWord_2004074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273645935397410358728819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48729722494393094289943517 18273645935397410358728819)
  ·
    refine ⟨27410468903096115538093229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18273645935397410358728819 27410468903096115538093229)
    ·
      refine ⟨10278925838661043326784961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27410468903096115538093229 10278925838661043326784961)
      ·
        refine ⟨7709194378995782495088721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10278925838661043326784961 7709194378995782495088721)
        ·
          refine ⟨5781895784246836871316541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7709194378995782495088721 5781895784246836871316541)
          ·
            refine ⟨2168210919092563826743703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5781895784246836871316541 2168210919092563826743703)
            ·
              refine ⟨3252316378638845740115555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168210919092563826743703 3252316378638845740115555)
              ·
                refine ⟨4878474567958268610173333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252316378638845740115555 4878474567958268610173333)
                ·
                  refine ⟨228678495373043841101875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4878474567958268610173333 228678495373043841101875)
                  ·
                    rfl

theorem cell22_2004074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_2004074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004074 prefixEnd_2004074 := by exact prefixLift 2004074
  have htrace : WordTrace (prefixWord ++ tailWord_2004074) baseStart_2004074 baseEnd_2004074 := by
    simpa [prefixWord, tailWord_2004074, baseEnd_2004074] using wordTrace_append hprefix tailTrace_2004074
  have hstable : (prefixWord ++ tailWord_2004074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004074).length < 2 ^ (prefixWord ++ tailWord_2004074).sum := by decide
  have hdescent : baseEnd_2004074 < baseStart_2004074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004117 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_2004117 : Nat := 118140960795 + 2004117 * 2 ^ 59
def prefixEnd_2004117 : Nat := 4983230072969 + 3 ^ 40 * 2004117 * 2
def baseEnd_2004117 : Nat := 686050205897893744480493

theorem tailTrace_2004117 : CollatzResearch.WordTrace tailWord_2004117 prefixEnd_2004117 686050205897893744480493 := by
  unfold tailWord_2004117
  simp only [CollatzResearch.WordTrace]
  refine ⟨73096152080433859778730605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48730768053622573185820403 73096152080433859778730605)
  ·
    refine ⟨27411057030162697417023977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73096152080433859778730605 27411057030162697417023977)
    ·
      refine ⟨20558292772622023062767983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27411057030162697417023977 20558292772622023062767983)
      ·
        refine ⟨30837439158933034594151975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20558292772622023062767983 30837439158933034594151975)
        ·
          refine ⟨46256158738399551891227963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30837439158933034594151975 46256158738399551891227963)
          ·
            refine ⟨69384238107599327836841945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46256158738399551891227963 69384238107599327836841945)
            ·
              refine ⟨52038178580699495877631459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69384238107599327836841945 52038178580699495877631459)
              ·
                refine ⟨78057267871049243816447189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52038178580699495877631459 78057267871049243816447189)
                ·
                  refine ⟨1829467215727716651947981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 78057267871049243816447189 1829467215727716651947981)
                  ·
                    refine ⟨686050205897893744480493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829467215727716651947981 686050205897893744480493)
                    ·
                      rfl

theorem cell22_2004117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_2004117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004117 prefixEnd_2004117 := by exact prefixLift 2004117
  have htrace : WordTrace (prefixWord ++ tailWord_2004117) baseStart_2004117 baseEnd_2004117 := by
    simpa [prefixWord, tailWord_2004117, baseEnd_2004117] using wordTrace_append hprefix tailTrace_2004117
  have hstable : (prefixWord ++ tailWord_2004117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004117).length < 2 ^ (prefixWord ++ tailWord_2004117).sum := by decide
  have hdescent : baseEnd_2004117 < baseStart_2004117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004132 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_2004132 : Nat := 118140960795 + 2004132 * 2 ^ 59
def prefixEnd_2004132 : Nat := 4983230072969 + 3 ^ 40 * 2004132 * 2
def baseEnd_2004132 : Nat := 686055340704438705355447

theorem tailTrace_2004132 : CollatzResearch.WordTrace tailWord_2004132 prefixEnd_2004132 686055340704438705355447 := by
  unfold tailWord_2004132
  simp only [CollatzResearch.WordTrace]
  refine ⟨36548349587689758670263325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48731132783586344893684433 36548349587689758670263325)
  ·
    refine ⟨13705631095383659501348747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36548349587689758670263325 13705631095383659501348747)
    ·
      refine ⟨20558446643075489252023121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13705631095383659501348747 20558446643075489252023121)
      ·
        refine ⟨15418834982306616939017341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20558446643075489252023121 15418834982306616939017341)
        ·
          refine ⟨5782063118364981352131503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15418834982306616939017341 5782063118364981352131503)
          ·
            refine ⟨8673094677547472028197255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5782063118364981352131503 8673094677547472028197255)
            ·
              refine ⟨13009642016321208042295883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673094677547472028197255 13009642016321208042295883)
              ·
                refine ⟨19514463024481812063443825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13009642016321208042295883 19514463024481812063443825)
                ·
                  refine ⟨14635847268361359047582869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19514463024481812063443825 14635847268361359047582869)
                  ·
                    refine ⟨686055340704438705355447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14635847268361359047582869 686055340704438705355447)
                    ·
                      rfl

theorem cell22_2004132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_2004132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004132 prefixEnd_2004132 := by exact prefixLift 2004132
  have htrace : WordTrace (prefixWord ++ tailWord_2004132) baseStart_2004132 baseEnd_2004132 := by
    simpa [prefixWord, tailWord_2004132, baseEnd_2004132] using wordTrace_append hprefix tailTrace_2004132
  have hstable : (prefixWord ++ tailWord_2004132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004132).length < 2 ^ (prefixWord ++ tailWord_2004132).sum := by decide
  have hdescent : baseEnd_2004132 < baseStart_2004132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004147 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 5]
def baseStart_2004147 : Nat := 118140960795 + 2004147 * 2 ^ 59
def prefixEnd_2004147 : Nat := 4983230072969 + 3 ^ 40 * 2004147 * 2
def baseEnd_2004147 : Nat := 228686825170327888743467

theorem tailTrace_2004147 : CollatzResearch.WordTrace tailWord_2004147 prefixEnd_2004147 228686825170327888743467 := by
  unfold tailWord_2004147
  simp only [CollatzResearch.WordTrace]
  refine ⟨73097246270325174902322695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48731497513550116601548463 73097246270325174902322695)
  ·
    refine ⟨109645869405487762353484043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73097246270325174902322695 109645869405487762353484043)
    ·
      refine ⟨164468804108231643530226065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109645869405487762353484043 164468804108231643530226065)
      ·
        refine ⟨123351603081173732647669549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164468804108231643530226065 123351603081173732647669549)
        ·
          refine ⟨46256851155440149742876081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123351603081173732647669549 46256851155440149742876081)
          ·
            refine ⟨34692638366580112307157061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46256851155440149742876081 34692638366580112307157061)
            ·
              refine ⟨6504869693733771057591949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34692638366580112307157061 6504869693733771057591949)
              ·
                refine ⟨2439326135150164146596981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6504869693733771057591949 2439326135150164146596981)
                ·
                  refine ⟨228686825170327888743467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2439326135150164146596981 228686825170327888743467)
                  ·
                    rfl

theorem cell22_2004147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 5].length) (baseStart_2004147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004147 prefixEnd_2004147 := by exact prefixLift 2004147
  have htrace : WordTrace (prefixWord ++ tailWord_2004147) baseStart_2004147 baseEnd_2004147 := by
    simpa [prefixWord, tailWord_2004147, baseEnd_2004147] using wordTrace_append hprefix tailTrace_2004147
  have hstable : (prefixWord ++ tailWord_2004147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004147).length < 2 ^ (prefixWord ++ tailWord_2004147).sum := by decide
  have hdescent : baseEnd_2004147 < baseStart_2004147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004181 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 5]
def baseStart_2004181 : Nat := 118140960795 + 2004181 * 2 ^ 59
def prefixEnd_2004181 : Nat := 4983230072969 + 3 ^ 40 * 2004181 * 2
def baseEnd_2004181 : Nat := 228690704801939636960099

theorem tailTrace_2004181 : CollatzResearch.WordTrace tailWord_2004181 prefixEnd_2004181 228690704801939636960099 := by
  unfold tailWord_2004181
  simp only [CollatzResearch.WordTrace]
  refine ⟨73098486352201998709060397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48732324234801332472706931 73098486352201998709060397)
  ·
    refine ⟨27411932382075749515897649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73098486352201998709060397 27411932382075749515897649)
    ·
      refine ⟨20558949286556812136923237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27411932382075749515897649 20558949286556812136923237)
      ·
        refine ⟨3854802991229402275673107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20558949286556812136923237 3854802991229402275673107)
        ·
          refine ⟨5782204486844103413509661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854802991229402275673107 5782204486844103413509661)
          ·
            refine ⟨2168326682566538780066123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5782204486844103413509661 2168326682566538780066123)
            ·
              refine ⟨3252490023849808170099185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168326682566538780066123 3252490023849808170099185)
              ·
                refine ⟨2439367517887356127574389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3252490023849808170099185 2439367517887356127574389)
                ·
                  refine ⟨228690704801939636960099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2439367517887356127574389 228690704801939636960099)
                  ·
                    rfl

theorem cell22_2004181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_2004181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004181 prefixEnd_2004181 := by exact prefixLift 2004181
  have htrace : WordTrace (prefixWord ++ tailWord_2004181) baseStart_2004181 baseEnd_2004181 := by
    simpa [prefixWord, tailWord_2004181, baseEnd_2004181] using wordTrace_append hprefix tailTrace_2004181
  have hstable : (prefixWord ++ tailWord_2004181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004181).length < 2 ^ (prefixWord ++ tailWord_2004181).sum := by decide
  have hdescent : baseEnd_2004181 < baseStart_2004181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004192 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 6]
def baseStart_2004192 : Nat := 118140960795 + 2004192 * 2 ^ 59
def prefixEnd_2004192 : Nat := 4983230072969 + 3 ^ 40 * 2004192 * 2
def baseEnd_2004192 : Nat := 228691959976872849618421

theorem tailTrace_2004192 : CollatzResearch.WordTrace tailWord_2004192 prefixEnd_2004192 228691959976872849618421 := by
  unfold tailWord_2004192
  simp only [CollatzResearch.WordTrace]
  refine ⟨36549443777581073793855415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48732591703441431725140553 36549443777581073793855415)
  ·
    refine ⟨54824165666371610690783123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36549443777581073793855415 54824165666371610690783123)
    ·
      refine ⟨82236248499557416036174685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54824165666371610690783123 82236248499557416036174685)
      ·
        refine ⟨30838593187334031013565507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82236248499557416036174685 30838593187334031013565507)
        ·
          refine ⟨46257889781001046520348261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30838593187334031013565507 46257889781001046520348261)
          ·
            refine ⟨8673354333937696222565299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46257889781001046520348261 8673354333937696222565299)
            ·
              refine ⟨13010031500906544333847949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673354333937696222565299 13010031500906544333847949)
              ·
                refine ⟨4878761812839954125192981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13010031500906544333847949 4878761812839954125192981)
                ·
                  refine ⟨228691959976872849618421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4878761812839954125192981 228691959976872849618421)
                  ·
                    rfl

theorem cell22_2004192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_2004192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004192 prefixEnd_2004192 := by exact prefixLift 2004192
  have htrace : WordTrace (prefixWord ++ tailWord_2004192) baseStart_2004192 baseEnd_2004192 := by
    simpa [prefixWord, tailWord_2004192, baseEnd_2004192] using wordTrace_append hprefix tailTrace_2004192
  have hstable : (prefixWord ++ tailWord_2004192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004192).length < 2 ^ (prefixWord ++ tailWord_2004192).sum := by decide
  have hdescent : baseEnd_2004192 < baseStart_2004192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004258 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_2004258 : Nat := 118140960795 + 2004258 * 2 ^ 59
def prefixEnd_2004258 : Nat := 4983230072969 + 3 ^ 40 * 2004258 * 2
def baseEnd_2004258 : Nat := 686098473079416376705061

theorem tailTrace_2004258 : CollatzResearch.WordTrace tailWord_2004258 prefixEnd_2004258 686098473079416376705061 := by
  unfold tailWord_2004258
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275323693230760214903357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48734196515282027239742285 18275323693230760214903357)
  ·
    refine ⟨6853246384961535080588759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18275323693230760214903357 6853246384961535080588759)
    ·
      refine ⟨10279869577442302620883139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6853246384961535080588759 10279869577442302620883139)
      ·
        refine ⟨15419804366163453931324709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10279869577442302620883139 15419804366163453931324709)
        ·
          refine ⟨2891213318655647612123383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15419804366163453931324709 2891213318655647612123383)
          ·
            refine ⟨4336819977983471418185075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891213318655647612123383 4336819977983471418185075)
            ·
              refine ⟨6505229966975207127277613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336819977983471418185075 6505229966975207127277613)
              ·
                refine ⟨2439461237615702672729105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6505229966975207127277613 2439461237615702672729105)
                ·
                  refine ⟨1829595928211777004546829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2439461237615702672729105 1829595928211777004546829)
                  ·
                    refine ⟨686098473079416376705061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829595928211777004546829 686098473079416376705061)
                    ·
                      rfl

theorem cell22_2004258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_2004258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004258 prefixEnd_2004258 := by exact prefixLift 2004258
  have htrace : WordTrace (prefixWord ++ tailWord_2004258) baseStart_2004258 baseEnd_2004258 := by
    simpa [prefixWord, tailWord_2004258, baseEnd_2004258] using wordTrace_append hprefix tailTrace_2004258
  have hstable : (prefixWord ++ tailWord_2004258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004258).length < 2 ^ (prefixWord ++ tailWord_2004258).sum := by decide
  have hdescent : baseEnd_2004258 < baseStart_2004258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004294 : List Nat := [6, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2004294 : Nat := 118140960795 + 2004294 * 2 ^ 59
def prefixEnd_2004294 : Nat := 4983230072969 + 3 ^ 40 * 2004294 * 2
def baseEnd_2004294 : Nat := 228703598871708094268317

theorem tailTrace_2004294 : CollatzResearch.WordTrace tailWord_2004294 prefixEnd_2004294 228703598871708094268317 := by
  unfold tailWord_2004294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284456493774769343997623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48735071867195079338615957 2284456493774769343997623)
  ·
    refine ⟨3426684740662154015996435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2284456493774769343997623 3426684740662154015996435)
    ·
      refine ⟨5140027110993231023994653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426684740662154015996435 5140027110993231023994653)
      ·
        refine ⟨1927510166622461633997995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5140027110993231023994653 1927510166622461633997995)
        ·
          refine ⟨2891265249933692450996993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927510166622461633997995 2891265249933692450996993)
          ·
            refine ⟨2168448937450269338247745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2891265249933692450996993 2168448937450269338247745)
            ·
              refine ⟨1626336703087702003685809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168448937450269338247745 1626336703087702003685809)
              ·
                refine ⟨1219752527315776502764357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626336703087702003685809 1219752527315776502764357)
                ·
                  refine ⟨228703598871708094268317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219752527315776502764357 228703598871708094268317)
                  ·
                    rfl

theorem cell22_2004294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2004294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004294 prefixEnd_2004294 := by exact prefixLift 2004294
  have htrace : WordTrace (prefixWord ++ tailWord_2004294) baseStart_2004294 baseEnd_2004294 := by
    simpa [prefixWord, tailWord_2004294, baseEnd_2004294] using wordTrace_append hprefix tailTrace_2004294
  have hstable : (prefixWord ++ tailWord_2004294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004294).length < 2 ^ (prefixWord ++ tailWord_2004294).sum := by decide
  have hdescent : baseEnd_2004294 < baseStart_2004294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004361 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 6]
def baseStart_2004361 : Nat := 118140960795 + 2004361 * 2 ^ 59
def prefixEnd_2004361 : Nat := 4983230072969 + 3 ^ 40 * 2004361 * 2
def baseEnd_2004361 : Nat := 228711244028119480459915

theorem tailTrace_2004361 : CollatzResearch.WordTrace tailWord_2004361 prefixEnd_2004361 228711244028119480459915 := by
  unfold tailWord_2004361
  simp only [CollatzResearch.WordTrace]
  refine ⟨73105051491549889450612937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48736700994366592967075291 73105051491549889450612937)
  ·
    refine ⟨54828788618662417087959703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73105051491549889450612937 54828788618662417087959703)
    ·
      refine ⟨82243182927993625631939555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54828788618662417087959703 82243182927993625631939555)
      ·
        refine ⟨123364774391990438447909333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82243182927993625631939555 123364774391990438447909333)
        ·
          refine ⟨2891361899812275901122875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 123364774391990438447909333 2891361899812275901122875)
          ·
            refine ⟨4337042849718413851684313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891361899812275901122875 4337042849718413851684313)
            ·
              refine ⟨3252782137288810388763235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4337042849718413851684313 3252782137288810388763235)
              ·
                refine ⟨4879173205933215583144853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252782137288810388763235 4879173205933215583144853)
                ·
                  refine ⟨228711244028119480459915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4879173205933215583144853 228711244028119480459915)
                  ·
                    rfl

theorem cell22_2004361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_2004361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004361 prefixEnd_2004361 := by exact prefixLift 2004361
  have htrace : WordTrace (prefixWord ++ tailWord_2004361) baseStart_2004361 baseEnd_2004361 := by
    simpa [prefixWord, tailWord_2004361, baseEnd_2004361] using wordTrace_append hprefix tailTrace_2004361
  have hstable : (prefixWord ++ tailWord_2004361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004361).length < 2 ^ (prefixWord ++ tailWord_2004361).sum := by decide
  have hdescent : baseEnd_2004361 < baseStart_2004361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004380 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_2004380 : Nat := 118140960795 + 2004380 * 2 ^ 59
def prefixEnd_2004380 : Nat := 4983230072969 + 3 ^ 40 * 2004380 * 2
def baseEnd_2004380 : Nat := 686140236172648725154687

theorem tailTrace_2004380 : CollatzResearch.WordTrace tailWord_2004380 prefixEnd_2004380 686140236172648725154687 := by
  unfold tailWord_2004380
  simp only [CollatzResearch.WordTrace]
  refine ⟨36552872239240527847777297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48737162985654037130369729 36552872239240527847777297)
  ·
    refine ⟨27414654179430395885832973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36552872239240527847777297 27414654179430395885832973)
    ·
      refine ⟨10280495317286398457187365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27414654179430395885832973 10280495317286398457187365)
      ·
        refine ⟨1927592871991199710722631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10280495317286398457187365 1927592871991199710722631)
        ·
          refine ⟨2891389307986799566083947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927592871991199710722631 2891389307986799566083947)
          ·
            refine ⟨4337083961980199349125921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891389307986799566083947 4337083961980199349125921)
            ·
              refine ⟨3252812971485149511844441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4337083961980199349125921 3252812971485149511844441)
              ·
                refine ⟨2439609728613862133883331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3252812971485149511844441 2439609728613862133883331)
                ·
                  refine ⟨3659414592920793200824997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439609728613862133883331 3659414592920793200824997)
                  ·
                    refine ⟨686140236172648725154687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3659414592920793200824997 686140236172648725154687)
                    ·
                      rfl

theorem cell22_2004380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_2004380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004380 prefixEnd_2004380 := by exact prefixLift 2004380
  have htrace : WordTrace (prefixWord ++ tailWord_2004380) baseStart_2004380 baseEnd_2004380 := by
    simpa [prefixWord, tailWord_2004380, baseEnd_2004380] using wordTrace_append hprefix tailTrace_2004380
  have hstable : (prefixWord ++ tailWord_2004380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004380).length < 2 ^ (prefixWord ++ tailWord_2004380).sum := by decide
  have hdescent : baseEnd_2004380 < baseStart_2004380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004391 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2004391 : Nat := 118140960795 + 2004391 * 2 ^ 59
def prefixEnd_2004391 : Nat := 4983230072969 + 3 ^ 40 * 2004391 * 2
def baseEnd_2004391 : Nat := 686144001697448363129653

theorem tailTrace_2004391 : CollatzResearch.WordTrace tailWord_2004391 prefixEnd_2004391 686144001697448363129653 := by
  unfold tailWord_2004391
  simp only [CollatzResearch.WordTrace]
  refine ⟨73106145681441204574205027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48737430454294136382803351 73106145681441204574205027)
  ·
    refine ⟨109659218522161806861307541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73106145681441204574205027 109659218522161806861307541)
    ·
      refine ⟨5140275868226334696623791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109659218522161806861307541 5140275868226334696623791)
      ·
        refine ⟨7710413802339502044935687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140275868226334696623791 7710413802339502044935687)
        ·
          refine ⟨11565620703509253067403531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710413802339502044935687 11565620703509253067403531)
          ·
            refine ⟨17348431055263879601105297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11565620703509253067403531 17348431055263879601105297)
            ·
              refine ⟨13011323291447909700828973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17348431055263879601105297 13011323291447909700828973)
              ·
                refine ⟨4879246234292966137810865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13011323291447909700828973 4879246234292966137810865)
                ·
                  refine ⟨3659434675719724603358149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4879246234292966137810865 3659434675719724603358149)
                  ·
                    refine ⟨686144001697448363129653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3659434675719724603358149 686144001697448363129653)
                    ·
                      rfl

theorem cell22_2004391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2004391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004391 prefixEnd_2004391 := by exact prefixLift 2004391
  have htrace : WordTrace (prefixWord ++ tailWord_2004391) baseStart_2004391 baseEnd_2004391 := by
    simpa [prefixWord, tailWord_2004391, baseEnd_2004391] using wordTrace_append hprefix tailTrace_2004391
  have hstable : (prefixWord ++ tailWord_2004391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004391).length < 2 ^ (prefixWord ++ tailWord_2004391).sum := by decide
  have hdescent : baseEnd_2004391 < baseStart_2004391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004472 : List Nat := [2, 1, 2, 1, 1, 7, 2, 2, 1, 3]
def baseStart_2004472 : Nat := 118140960795 + 2004472 * 2 ^ 59
def prefixEnd_2004472 : Nat := 4983230072969 + 3 ^ 40 * 2004472 * 2
def baseEnd_2004472 : Nat := 686171729652791151854405

theorem tailTrace_2004472 : CollatzResearch.WordTrace tailWord_2004472 prefixEnd_2004472 686171729652791151854405 := by
  unfold tailWord_2004472
  simp only [CollatzResearch.WordTrace]
  refine ⟨36554549997073877703951835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48739399996098503605269113 36554549997073877703951835)
  ·
    refine ⟨54831824995610816555927753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36554549997073877703951835 54831824995610816555927753)
    ·
      refine ⟨41123868746708112416945815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54831824995610816555927753 41123868746708112416945815)
      ·
        refine ⟨61685803120062168625418723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41123868746708112416945815 61685803120062168625418723)
        ·
          refine ⟨92528704680093252938128085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61685803120062168625418723 92528704680093252938128085)
          ·
            refine ⟨2168641515939685615737377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 92528704680093252938128085 2168641515939685615737377)
            ·
              refine ⟨1626481136954764211803033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168641515939685615737377 1626481136954764211803033)
              ·
                refine ⟨1219860852716073158852275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626481136954764211803033 1219860852716073158852275)
                ·
                  refine ⟨1829791279074109738278413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219860852716073158852275 1829791279074109738278413)
                  ·
                    refine ⟨686171729652791151854405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829791279074109738278413 686171729652791151854405)
                    ·
                      rfl

theorem cell22_2004472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_2004472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004472 prefixEnd_2004472 := by exact prefixLift 2004472
  have htrace : WordTrace (prefixWord ++ tailWord_2004472) baseStart_2004472 baseEnd_2004472 := by
    simpa [prefixWord, tailWord_2004472, baseEnd_2004472] using wordTrace_append hprefix tailTrace_2004472
  have hstable : (prefixWord ++ tailWord_2004472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004472).length < 2 ^ (prefixWord ++ tailWord_2004472).sum := by decide
  have hdescent : baseEnd_2004472 < baseStart_2004472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004511 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 1, 5]
def baseStart_2004511 : Nat := 118140960795 + 2004511 * 2 ^ 59
def prefixEnd_2004511 : Nat := 4983230072969 + 3 ^ 40 * 2004511 * 2
def baseEnd_2004511 : Nat := 686185080149808050129285

theorem tailTrace_2004511 : CollatzResearch.WordTrace tailWord_2004511 prefixEnd_2004511 686185080149808050129285 := by
  unfold tailWord_2004511
  simp only [CollatzResearch.WordTrace]
  refine ⟨73110522441006465068573387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48740348294004310045715591 73110522441006465068573387)
  ·
    refine ⟨109665783661509697602860081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73110522441006465068573387 109665783661509697602860081)
    ·
      refine ⟨82249337746132273202145061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109665783661509697602860081 82249337746132273202145061)
      ·
        refine ⟨15421750827399801225402199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82249337746132273202145061 15421750827399801225402199)
        ·
          refine ⟨23132626241099701838103299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15421750827399801225402199 23132626241099701838103299)
          ·
            refine ⟨34698939361649552757154949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23132626241099701838103299 34698939361649552757154949)
            ·
              refine ⟨6506051130309291141966553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34698939361649552757154949 6506051130309291141966553)
              ·
                refine ⟨4879538347731968356474915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6506051130309291141966553 4879538347731968356474915)
                ·
                  refine ⟨7319307521597952534712373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879538347731968356474915 7319307521597952534712373)
                  ·
                    refine ⟨686185080149808050129285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7319307521597952534712373 686185080149808050129285)
                    ·
                      rfl

theorem cell22_2004511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_2004511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004511 prefixEnd_2004511 := by exact prefixLift 2004511
  have htrace : WordTrace (prefixWord ++ tailWord_2004511) baseStart_2004511 baseEnd_2004511 := by
    simpa [prefixWord, tailWord_2004511, baseEnd_2004511] using wordTrace_append hprefix tailTrace_2004511
  have hstable : (prefixWord ++ tailWord_2004511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004511).length < 2 ^ (prefixWord ++ tailWord_2004511).sum := by decide
  have hdescent : baseEnd_2004511 < baseStart_2004511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004513 : List Nat := [1, 2, 3, 2, 2, 2, 1, 5, 4]
def baseStart_2004513 : Nat := 118140960795 + 2004513 * 2 ^ 59
def prefixEnd_2004513 : Nat := 4983230072969 + 3 ^ 40 * 2004513 * 2
def baseEnd_2004513 : Nat := 228728588263560237193093

theorem tailTrace_2004513 : CollatzResearch.WordTrace tailWord_2004513 prefixEnd_2004513 228728588263560237193093 := by
  unfold tailWord_2004513
  simp only [CollatzResearch.WordTrace]
  refine ⟨73110595386999219410146193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48740396924666146273430795 73110595386999219410146193)
  ·
    refine ⟨54832946540249414557609645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73110595386999219410146193 54832946540249414557609645)
    ·
      refine ⟨20562354952593530459103617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54832946540249414557609645 20562354952593530459103617)
      ·
        refine ⟨15421766214445147844327713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20562354952593530459103617 15421766214445147844327713)
        ·
          refine ⟨11566324660833860883245785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15421766214445147844327713 11566324660833860883245785)
          ·
            refine ⟨8674743495625395662434339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11566324660833860883245785 8674743495625395662434339)
            ·
              refine ⟨13012115243438093493651509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8674743495625395662434339 13012115243438093493651509)
              ·
                refine ⟨1219885804072321265029829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13012115243438093493651509 1219885804072321265029829)
                ·
                  refine ⟨228728588263560237193093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219885804072321265029829 228728588263560237193093)
                  ·
                    rfl

theorem cell22_2004513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 4].length) (baseStart_2004513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004513 prefixEnd_2004513 := by exact prefixLift 2004513
  have htrace : WordTrace (prefixWord ++ tailWord_2004513) baseStart_2004513 baseEnd_2004513 := by
    simpa [prefixWord, tailWord_2004513, baseEnd_2004513] using wordTrace_append hprefix tailTrace_2004513
  have hstable : (prefixWord ++ tailWord_2004513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004513).length < 2 ^ (prefixWord ++ tailWord_2004513).sum := by decide
  have hdescent : baseEnd_2004513 < baseStart_2004513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004601 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_2004601 : Nat := 118140960795 + 2004601 * 2 ^ 59
def prefixEnd_2004601 : Nat := 4983230072969 + 3 ^ 40 * 2004601 * 2
def baseEnd_2004601 : Nat := 686215888989077815379009

theorem tailTrace_2004601 : CollatzResearch.WordTrace tailWord_2004601 prefixEnd_2004601 686215888989077815379009 := by
  unfold tailWord_2004601
  simp only [CollatzResearch.WordTrace]
  refine ⟨73113805010680410439349657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48742536673786940292899771 73113805010680410439349657)
  ·
    refine ⟨54835353758010307829512243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73113805010680410439349657 54835353758010307829512243)
    ·
      refine ⟨82253030637015461744268365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54835353758010307829512243 82253030637015461744268365)
      ·
        refine ⟨30844886488880798154100637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82253030637015461744268365 30844886488880798154100637)
        ·
          refine ⟨11566832433330299307787739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30844886488880798154100637 11566832433330299307787739)
          ·
            refine ⟨17350248649995448961681609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11566832433330299307787739 17350248649995448961681609)
            ·
              refine ⟨13012686487496586721261207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17350248649995448961681609 13012686487496586721261207)
              ·
                refine ⟨19519029731244880081891811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13012686487496586721261207 19519029731244880081891811)
                ·
                  refine ⟨29278544596867320122837717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19519029731244880081891811 29278544596867320122837717)
                  ·
                    refine ⟨686215888989077815379009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29278544596867320122837717 686215888989077815379009)
                    ·
                      rfl

theorem cell22_2004601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_2004601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004601 prefixEnd_2004601 := by exact prefixLift 2004601
  have htrace : WordTrace (prefixWord ++ tailWord_2004601) baseStart_2004601 baseEnd_2004601 := by
    simpa [prefixWord, tailWord_2004601, baseEnd_2004601] using wordTrace_append hprefix tailTrace_2004601
  have hstable : (prefixWord ++ tailWord_2004601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004601).length < 2 ^ (prefixWord ++ tailWord_2004601).sum := by decide
  have hdescent : baseEnd_2004601 < baseStart_2004601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004663 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 1, 5]
def baseStart_2004663 : Nat := 118140960795 + 2004663 * 2 ^ 59
def prefixEnd_2004663 : Nat := 4983230072969 + 3 ^ 40 * 2004663 * 2
def baseEnd_2004663 : Nat := 686237112856130320328819

theorem tailTrace_2004663 : CollatzResearch.WordTrace tailWord_2004663 prefixEnd_2004663 686237112856130320328819 := by
  unfold tailWord_2004663
  simp only [CollatzResearch.WordTrace]
  refine ⟨73116066336455795028106643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48744044224303863352071095 73116066336455795028106643)
  ·
    refine ⟨109674099504683692542159965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73116066336455795028106643 109674099504683692542159965)
    ·
      refine ⟨41127787314256384703309987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109674099504683692542159965 41127787314256384703309987)
      ·
        refine ⟨61691680971384577054964981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41127787314256384703309987 61691680971384577054964981)
        ·
          refine ⟨5783595091067304098902967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61691680971384577054964981 5783595091067304098902967)
          ·
            refine ⟨8675392636600956148354451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5783595091067304098902967 8675392636600956148354451)
            ·
              refine ⟨13013088954901434222531677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8675392636600956148354451 13013088954901434222531677)
              ·
                refine ⟨4879908358088037833449379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13013088954901434222531677 4879908358088037833449379)
                ·
                  refine ⟨7319862537132056750174069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879908358088037833449379 7319862537132056750174069)
                  ·
                    refine ⟨686237112856130320328819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7319862537132056750174069 686237112856130320328819)
                    ·
                      rfl

theorem cell22_2004663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_2004663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004663 prefixEnd_2004663 := by exact prefixLift 2004663
  have htrace : WordTrace (prefixWord ++ tailWord_2004663) baseStart_2004663 baseEnd_2004663 := by
    simpa [prefixWord, tailWord_2004663, baseEnd_2004663] using wordTrace_append hprefix tailTrace_2004663
  have hstable : (prefixWord ++ tailWord_2004663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004663).length < 2 ^ (prefixWord ++ tailWord_2004663).sum := by decide
  have hdescent : baseEnd_2004663 < baseStart_2004663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004682 : List Nat := [3, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_2004682 : Nat := 118140960795 + 2004682 * 2 ^ 59
def prefixEnd_2004682 : Nat := 4983230072969 + 3 ^ 40 * 2004682 * 2
def baseEnd_2004682 : Nat := 228747872314806868034587

theorem tailTrace_2004682 : CollatzResearch.WordTrace tailWord_2004682 prefixEnd_2004682 228747872314806868034587 := by
  unfold tailWord_2004682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18279189830846740318262075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48744506215591307515365533 18279189830846740318262075)
  ·
    refine ⟨27418784746270110477393113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18279189830846740318262075 27418784746270110477393113)
    ·
      refine ⟨20564088559702582858044835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27418784746270110477393113 20564088559702582858044835)
      ·
        refine ⟨30846132839553874287067253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20564088559702582858044835 30846132839553874287067253)
        ·
          refine ⟨2891824953708175714412555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30846132839553874287067253 2891824953708175714412555)
          ·
            refine ⟨4337737430562263571618833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891824953708175714412555 4337737430562263571618833)
            ·
              refine ⟨3253303072921697678714125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4337737430562263571618833 3253303072921697678714125)
              ·
                refine ⟨1219988652345636629517797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3253303072921697678714125 1219988652345636629517797)
                ·
                  refine ⟨228747872314806868034587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219988652345636629517797 228747872314806868034587)
                  ·
                    rfl

theorem cell22_2004682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_2004682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004682 prefixEnd_2004682 := by exact prefixLift 2004682
  have htrace : WordTrace (prefixWord ++ tailWord_2004682) baseStart_2004682 baseEnd_2004682 := by
    simpa [prefixWord, tailWord_2004682, baseEnd_2004682] using wordTrace_append hprefix tailTrace_2004682
  have hstable : (prefixWord ++ tailWord_2004682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004682).length < 2 ^ (prefixWord ++ tailWord_2004682).sum := by decide
  have hdescent : baseEnd_2004682 < baseStart_2004682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004684 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_2004684 : Nat := 118140960795 + 2004684 * 2 ^ 59
def prefixEnd_2004684 : Nat := 4983230072969 + 3 ^ 40 * 2004684 * 2
def baseEnd_2004684 : Nat := 686244301585293265553755

theorem tailTrace_2004684 : CollatzResearch.WordTrace tailWord_2004684 prefixEnd_2004684 686244301585293265553755 := by
  unfold tailWord_2004684
  simp only [CollatzResearch.WordTrace]
  refine ⟨36558416134689857807310553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48744554846253143743080737 36558416134689857807310553)
  ·
    refine ⟨27418812101017393355482915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36558416134689857807310553 27418812101017393355482915)
    ·
      refine ⟨41128218151526090033224373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27418812101017393355482915 41128218151526090033224373)
      ·
        refine ⟨3855770451705570940614785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41128218151526090033224373 3855770451705570940614785)
        ·
          refine ⟨2891827838779178205461089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3855770451705570940614785 2891827838779178205461089)
          ·
            refine ⟨2168870879084383654095817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2891827838779178205461089 2168870879084383654095817)
            ·
              refine ⟨1626653159313287740571863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168870879084383654095817 1626653159313287740571863)
              ·
                refine ⟨2439979738969931610857795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626653159313287740571863 2439979738969931610857795)
                ·
                  refine ⟨3659969608454897416286693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439979738969931610857795 3659969608454897416286693)
                  ·
                    refine ⟨686244301585293265553755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3659969608454897416286693 686244301585293265553755)
                    ·
                      rfl

theorem cell22_2004684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_2004684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004684 prefixEnd_2004684 := by exact prefixLift 2004684
  have htrace : WordTrace (prefixWord ++ tailWord_2004684) baseStart_2004684 baseEnd_2004684 := by
    simpa [prefixWord, tailWord_2004684, baseEnd_2004684] using wordTrace_append hprefix tailTrace_2004684
  have hstable : (prefixWord ++ tailWord_2004684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004684).length < 2 ^ (prefixWord ++ tailWord_2004684).sum := by decide
  have hdescent : baseEnd_2004684 < baseStart_2004684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004697 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 2, 3]
def baseStart_2004697 : Nat := 118140960795 + 2004697 * 2 ^ 59
def prefixEnd_2004697 : Nat := 4983230072969 + 3 ^ 40 * 2004697 * 2
def baseEnd_2004697 : Nat := 686248751750965564978715

theorem tailTrace_2004697 : CollatzResearch.WordTrace tailWord_2004697 prefixEnd_2004697 686248751750965564978715 := by
  unfold tailWord_2004697
  simp only [CollatzResearch.WordTrace]
  refine ⟨73117306418332618834844345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48744870945555079223229563 73117306418332618834844345)
  ·
    refine ⟨54837979813749464126133259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73117306418332618834844345 54837979813749464126133259)
    ·
      refine ⟨82256969720624196189199889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54837979813749464126133259 82256969720624196189199889)
      ·
        refine ⟨61692727290468147141899917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82256969720624196189199889 61692727290468147141899917)
        ·
          refine ⟨23134772733925555178212469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61692727290468147141899917 23134772733925555178212469)
          ·
            refine ⟨2168884943805520797957419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23134772733925555178212469 2168884943805520797957419)
            ·
              refine ⟨3253327415708281196936129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168884943805520797957419 3253327415708281196936129)
              ·
                refine ⟨2439995561781210897702097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3253327415708281196936129 2439995561781210897702097)
                ·
                  refine ⟨1829996671335908173276573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2439995561781210897702097 1829996671335908173276573)
                  ·
                    refine ⟨686248751750965564978715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829996671335908173276573 686248751750965564978715)
                    ·
                      rfl

theorem cell22_2004697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_2004697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004697 prefixEnd_2004697 := by exact prefixLift 2004697
  have htrace : WordTrace (prefixWord ++ tailWord_2004697) baseStart_2004697 baseEnd_2004697 := by
    simpa [prefixWord, tailWord_2004697, baseEnd_2004697] using wordTrace_append hprefix tailTrace_2004697
  have hstable : (prefixWord ++ tailWord_2004697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004697).length < 2 ^ (prefixWord ++ tailWord_2004697).sum := by decide
  have hdescent : baseEnd_2004697 < baseStart_2004697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004772 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 5]
def baseStart_2004772 : Nat := 118140960795 + 2004772 * 2 ^ 59
def prefixEnd_2004772 : Nat := 4983230072969 + 3 ^ 40 * 2004772 * 2
def baseEnd_2004772 : Nat := 228758141927896789784495

theorem tailTrace_2004772 : CollatzResearch.WordTrace tailWord_2004772 prefixEnd_2004772 228758141927896789784495 := by
  unfold tailWord_2004772
  simp only [CollatzResearch.WordTrace]
  refine ⟨36560020946530453321912285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48746694595373937762549713 36560020946530453321912285)
  ·
    refine ⟨13710007854948919995717107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36560020946530453321912285 13710007854948919995717107)
    ·
      refine ⟨20565011782423379993575661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13710007854948919995717107 20565011782423379993575661)
      ·
        refine ⟨7711879418408767497590873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20565011782423379993575661 7711879418408767497590873)
        ·
          refine ⟨5783909563806575623193155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7711879418408767497590873 5783909563806575623193155)
          ·
            refine ⟨8675864345709863434789733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5783909563806575623193155 8675864345709863434789733)
            ·
              refine ⟨1626724564820599394023075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8675864345709863434789733 1626724564820599394023075)
              ·
                refine ⟨2440086847230899091034613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626724564820599394023075 2440086847230899091034613)
                ·
                  refine ⟨228758141927896789784495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2440086847230899091034613 228758141927896789784495)
                  ·
                    rfl

theorem cell22_2004772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_2004772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004772 prefixEnd_2004772 := by exact prefixLift 2004772
  have htrace : WordTrace (prefixWord ++ tailWord_2004772) baseStart_2004772 baseEnd_2004772 := by
    simpa [prefixWord, tailWord_2004772, baseEnd_2004772] using wordTrace_append hprefix tailTrace_2004772
  have hstable : (prefixWord ++ tailWord_2004772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004772).length < 2 ^ (prefixWord ++ tailWord_2004772).sum := by decide
  have hdescent : baseEnd_2004772 < baseStart_2004772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004785 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_2004785 : Nat := 118140960795 + 2004785 * 2 ^ 59
def prefixEnd_2004785 : Nat := 4983230072969 + 3 ^ 40 * 2004785 * 2
def baseEnd_2004785 : Nat := 686278875949362668778445

theorem tailTrace_2004785 : CollatzResearch.WordTrace tailWord_2004785 prefixEnd_2004785 686278875949362668778445 := by
  unfold tailWord_2004785
  simp only [CollatzResearch.WordTrace]
  refine ⟨73120516042013809864047809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48747010694675873242698539 73120516042013809864047809)
  ·
    refine ⟨54840387031510357398035857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73120516042013809864047809 54840387031510357398035857)
    ·
      refine ⟨41130290273632768048526893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54840387031510357398035857 41130290273632768048526893)
      ·
        refine ⟨15423858852612288018197585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41130290273632768048526893 15423858852612288018197585)
        ·
          refine ⟨11567894139459216013648189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15423858852612288018197585 11567894139459216013648189)
          ·
            refine ⟨4337960302297206005118071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11567894139459216013648189 4337960302297206005118071)
            ·
              refine ⟨6506940453445809007677107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337960302297206005118071 6506940453445809007677107)
              ·
                refine ⟨9760410680168713511515661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506940453445809007677107 9760410680168713511515661)
                ·
                  refine ⟨3660154005063267566818373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9760410680168713511515661 3660154005063267566818373)
                  ·
                    refine ⟨686278875949362668778445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660154005063267566818373 686278875949362668778445)
                    ·
                      rfl

theorem cell22_2004785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_2004785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004785 prefixEnd_2004785 := by exact prefixLift 2004785
  have htrace : WordTrace (prefixWord ++ tailWord_2004785) baseStart_2004785 baseEnd_2004785 := by
    simpa [prefixWord, tailWord_2004785, baseEnd_2004785] using wordTrace_append hprefix tailTrace_2004785
  have hstable : (prefixWord ++ tailWord_2004785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004785).length < 2 ^ (prefixWord ++ tailWord_2004785).sum := by decide
  have hdescent : baseEnd_2004785 < baseStart_2004785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004817 : List Nat := [1, 2, 2, 1, 5, 2, 1, 4, 4]
def baseStart_2004817 : Nat := 118140960795 + 2004817 * 2 ^ 59
def prefixEnd_2004817 : Nat := 4983230072969 + 3 ^ 40 * 2004817 * 2
def baseEnd_2004817 : Nat := 228763276734441750659449

theorem tailTrace_2004817 : CollatzResearch.WordTrace tailWord_2004817 prefixEnd_2004817 228763276734441750659449 := by
  unfold tailWord_2004817
  simp only [CollatzResearch.WordTrace]
  refine ⟨73121683177897879329212705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48747788785265252886141803 73121683177897879329212705)
  ·
    refine ⟨54841262383423409496909529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73121683177897879329212705 54841262383423409496909529)
    ·
      refine ⟨41130946787567557122682147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54841262383423409496909529 41130946787567557122682147)
      ·
        refine ⟨61696420181351335684023221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41130946787567557122682147 61696420181351335684023221)
        ·
          refine ⟨5784039392001687720377177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61696420181351335684023221 5784039392001687720377177)
          ·
            refine ⟨4338029544001265790282883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5784039392001687720377177 4338029544001265790282883)
            ·
              refine ⟨6507044316001898685424325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338029544001265790282883 6507044316001898685424325)
              ·
                refine ⟨1220070809250356003517061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6507044316001898685424325 1220070809250356003517061)
                ·
                  refine ⟨228763276734441750659449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1220070809250356003517061 228763276734441750659449)
                  ·
                    rfl

theorem cell22_2004817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 4].length) (baseStart_2004817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004817 prefixEnd_2004817 := by exact prefixLift 2004817
  have htrace : WordTrace (prefixWord ++ tailWord_2004817) baseStart_2004817 baseEnd_2004817 := by
    simpa [prefixWord, tailWord_2004817, baseEnd_2004817] using wordTrace_append hprefix tailTrace_2004817
  have hstable : (prefixWord ++ tailWord_2004817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004817).length < 2 ^ (prefixWord ++ tailWord_2004817).sum := by decide
  have hdescent : baseEnd_2004817 < baseStart_2004817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004832 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 2, 3]
def baseStart_2004832 : Nat := 118140960795 + 2004832 * 2 ^ 59
def prefixEnd_2004832 : Nat := 4983230072969 + 3 ^ 40 * 2004832 * 2
def baseEnd_2004832 : Nat := 686294965009870212853301

theorem tailTrace_2004832 : CollatzResearch.WordTrace tailWord_2004832 prefixEnd_2004832 686294965009870212853301 := by
  unfold tailWord_2004832
  simp only [CollatzResearch.WordTrace]
  refine ⟨36561115136421768445504375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48748153515229024594005833 36561115136421768445504375)
  ·
    refine ⟨54841672704632652668256563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36561115136421768445504375 54841672704632652668256563)
    ·
      refine ⟨82262509056948979002384845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54841672704632652668256563 82262509056948979002384845)
      ·
        refine ⟨30848440896355867125894317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82262509056948979002384845 30848440896355867125894317)
        ·
          refine ⟨11568165336133450172210369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30848440896355867125894317 11568165336133450172210369)
          ·
            refine ⟨8676124002100087629157777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11568165336133450172210369 8676124002100087629157777)
            ·
              refine ⟨6507093001575065721868333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8676124002100087629157777 6507093001575065721868333)
              ·
                refine ⟨2440159875590649645700625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6507093001575065721868333 2440159875590649645700625)
                ·
                  refine ⟨1830119906692987234275469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2440159875590649645700625 1830119906692987234275469)
                  ·
                    refine ⟨686294965009870212853301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1830119906692987234275469 686294965009870212853301)
                    ·
                      rfl

theorem cell22_2004832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_2004832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004832 prefixEnd_2004832 := by exact prefixLift 2004832
  have htrace : WordTrace (prefixWord ++ tailWord_2004832) baseStart_2004832 baseEnd_2004832 := by
    simpa [prefixWord, tailWord_2004832, baseEnd_2004832] using wordTrace_append hprefix tailTrace_2004832
  have hstable : (prefixWord ++ tailWord_2004832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004832).length < 2 ^ (prefixWord ++ tailWord_2004832).sum := by decide
  have hdescent : baseEnd_2004832 < baseStart_2004832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004862 : List Nat := [4, 2, 3, 1, 1, 2, 9]
def baseStart_2004862 : Nat := 118140960795 + 2004862 * 2 ^ 59
def prefixEnd_2004862 : Nat := 4983230072969 + 3 ^ 40 * 2004862 * 2
def baseEnd_2004862 : Nat := 25418712393442967948267

theorem tailTrace_2004862 : CollatzResearch.WordTrace tailWord_2004862 prefixEnd_2004862 25418712393442967948267 := by
  unfold tailWord_2004862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9140415557841856501825105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48748882975156568009733893 9140415557841856501825105)
  ·
    refine ⟨6855311668381392376368829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9140415557841856501825105 6855311668381392376368829)
    ·
      refine ⟨2570741875643022141138311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6855311668381392376368829 2570741875643022141138311)
      ·
        refine ⟨3856112813464533211707467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570741875643022141138311 3856112813464533211707467)
        ·
          refine ⟨5784169220196799817561201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856112813464533211707467 5784169220196799817561201)
          ·
            refine ⟨4338126915147599863170901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5784169220196799817561201 4338126915147599863170901)
            ·
              refine ⟨25418712393442967948267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4338126915147599863170901 25418712393442967948267)
              ·
                rfl

theorem cell22_2004862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 9].length) (baseStart_2004862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004862 prefixEnd_2004862 := by exact prefixLift 2004862
  have htrace : WordTrace (prefixWord ++ tailWord_2004862) baseStart_2004862 baseEnd_2004862 := by
    simpa [prefixWord, tailWord_2004862, baseEnd_2004862] using wordTrace_append hprefix tailTrace_2004862
  have hstable : (prefixWord ++ tailWord_2004862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004862).length < 2 ^ (prefixWord ++ tailWord_2004862).sum := by decide
  have hdescent : baseEnd_2004862 < baseStart_2004862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004997 : List Nat := [1, 3, 1, 1, 2, 6, 1, 7]
def baseStart_2004997 : Nat := 118140960795 + 2004997 * 2 ^ 59
def prefixEnd_2004997 : Nat := 4983230072969 + 3 ^ 40 * 2004997 * 2
def baseEnd_2004997 : Nat := 76261271986873864719755

theorem tailTrace_2004997 : CollatzResearch.WordTrace tailWord_2004997 prefixEnd_2004997 76261271986873864719755 := by
  unfold tailWord_2004997
  simp only [CollatzResearch.WordTrace]
  refine ⟨73128248317245770070765245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48752165544830513380510163 73128248317245770070765245)
  ·
    refine ⟨27423093118967163776536967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73128248317245770070765245 27423093118967163776536967)
    ·
      refine ⟨41134639678450745664805451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27423093118967163776536967 41134639678450745664805451)
      ·
        refine ⟨61701959517676118497208177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41134639678450745664805451 61701959517676118497208177)
        ·
          refine ⟨46276469638257088872906133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61701959517676118497208177 46276469638257088872906133)
          ·
            refine ⟨2169209514293301040917475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46276469638257088872906133 2169209514293301040917475)
            ·
              refine ⟨3253814271439951561376213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169209514293301040917475 3253814271439951561376213)
              ·
                refine ⟨76261271986873864719755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3253814271439951561376213 76261271986873864719755)
                ·
                  rfl

theorem cell22_2004997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 7].length) (baseStart_2004997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2004997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2004997 prefixEnd_2004997 := by exact prefixLift 2004997
  have htrace : WordTrace (prefixWord ++ tailWord_2004997) baseStart_2004997 baseEnd_2004997 := by
    simpa [prefixWord, tailWord_2004997, baseEnd_2004997] using wordTrace_append hprefix tailTrace_2004997
  have hstable : (prefixWord ++ tailWord_2004997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004997).length < 2 ^ (prefixWord ++ tailWord_2004997).sum := by decide
  have hdescent : baseEnd_2004997 < baseStart_2004997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005042 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_2005042 : Nat := 118140960795 + 2005042 * 2 ^ 59
def prefixEnd_2005042 : Nat := 4983230072969 + 3 ^ 40 * 2005042 * 2
def baseEnd_2005042 : Nat := 228788950767166555034219

theorem tailTrace_2005042 : CollatzResearch.WordTrace tailWord_2005042 prefixEnd_2005042 228788950767166555034219 := by
  unfold tailWord_2005042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282472400520685689038345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48753259734721828504102253 18282472400520685689038345)
  ·
    refine ⟨13711854300390514266778759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18282472400520685689038345 13711854300390514266778759)
    ·
      refine ⟨20567781450585771400168139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13711854300390514266778759 20567781450585771400168139)
      ·
        refine ⟨30851672175878657100252209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20567781450585771400168139 30851672175878657100252209)
        ·
          refine ⟨23138754131908992825189157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30851672175878657100252209 23138754131908992825189157)
          ·
            refine ⟨4338516399732936154722967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23138754131908992825189157 4338516399732936154722967)
            ·
              refine ⟨6507774599599404232084451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338516399732936154722967 6507774599599404232084451)
              ·
                refine ⟨9761661899399106348126677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507774599599404232084451 9761661899399106348126677)
                ·
                  refine ⟨228788950767166555034219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9761661899399106348126677 228788950767166555034219)
                  ·
                    rfl

theorem cell22_2005042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_2005042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005042 prefixEnd_2005042 := by exact prefixLift 2005042
  have htrace : WordTrace (prefixWord ++ tailWord_2005042) baseStart_2005042 baseEnd_2005042 := by
    simpa [prefixWord, tailWord_2005042, baseEnd_2005042] using wordTrace_append hprefix tailTrace_2005042
  have hstable : (prefixWord ++ tailWord_2005042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005042).length < 2 ^ (prefixWord ++ tailWord_2005042).sum := by decide
  have hdescent : baseEnd_2005042 < baseStart_2005042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005046 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2005046 : Nat := 118140960795 + 2005046 * 2 ^ 59
def prefixEnd_2005046 : Nat := 4983230072969 + 3 ^ 40 * 2005046 * 2
def baseEnd_2005046 : Nat := 686368221583244988002645

theorem tailTrace_2005046 : CollatzResearch.WordTrace tailWord_2005046 prefixEnd_2005046 686368221583244988002645 := by
  unfold tailWord_2005046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570627218379265714956187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48753356996045500959532661 4570627218379265714956187)
  ·
    refine ⟨6855940827568898572434281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4570627218379265714956187 6855940827568898572434281)
    ·
      refine ⟨5141955620676673929325711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6855940827568898572434281 5141955620676673929325711)
      ·
        refine ⟨7712933431015010893988567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141955620676673929325711 7712933431015010893988567)
        ·
          refine ⟨11569400146522516340982851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712933431015010893988567 11569400146522516340982851)
          ·
            refine ⟨17354100219783774511474277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569400146522516340982851 17354100219783774511474277)
            ·
              refine ⟨3253893791209457720901427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17354100219783774511474277 3253893791209457720901427)
              ·
                refine ⟨4880840686814186581352141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253893791209457720901427 4880840686814186581352141)
                ·
                  refine ⟨1830315257555319968007053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4880840686814186581352141 1830315257555319968007053)
                  ·
                    refine ⟨686368221583244988002645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1830315257555319968007053 686368221583244988002645)
                    ·
                      rfl

theorem cell22_2005046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2005046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005046 prefixEnd_2005046 := by exact prefixLift 2005046
  have htrace : WordTrace (prefixWord ++ tailWord_2005046) baseStart_2005046 baseEnd_2005046 := by
    simpa [prefixWord, tailWord_2005046, baseEnd_2005046] using wordTrace_append hprefix tailTrace_2005046
  have hstable : (prefixWord ++ tailWord_2005046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005046).length < 2 ^ (prefixWord ++ tailWord_2005046).sum := by decide
  have hdescent : baseEnd_2005046 < baseStart_2005046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005104 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 6]
def baseStart_2005104 : Nat := 118140960795 + 2005104 * 2 ^ 59
def prefixEnd_2005104 : Nat := 4983230072969 + 3 ^ 40 * 2005104 * 2
def baseEnd_2005104 : Nat := 228796025389517390017489

theorem tailTrace_2005104 : CollatzResearch.WordTrace tailWord_2005104 prefixEnd_2005104 228796025389517390017489 := by
  unfold tailWord_2005104
  simp only [CollatzResearch.WordTrace]
  refine ⟨36566075463929063672455183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48754767285238751563273577 36566075463929063672455183)
  ·
    refine ⟨54849113195893595508682775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36566075463929063672455183 54849113195893595508682775)
    ·
      refine ⟨82273669793840393263024163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54849113195893595508682775 82273669793840393263024163)
      ·
        refine ⟨123410504690760589894536245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82273669793840393263024163 123410504690760589894536245)
        ·
          refine ⟨11569734814758805302612773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123410504690760589894536245 11569734814758805302612773)
          ·
            refine ⟨2169325277767275994239895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11569734814758805302612773 2169325277767275994239895)
            ·
              refine ⟨3253987916650913991359843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169325277767275994239895 3253987916650913991359843)
              ·
                refine ⟨4880981874976370987039765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253987916650913991359843 4880981874976370987039765)
                ·
                  refine ⟨228796025389517390017489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4880981874976370987039765 228796025389517390017489)
                  ·
                    rfl

theorem cell22_2005104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_2005104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005104 prefixEnd_2005104 := by exact prefixLift 2005104
  have htrace : WordTrace (prefixWord ++ tailWord_2005104) baseStart_2005104 baseEnd_2005104 := by
    simpa [prefixWord, tailWord_2005104, baseEnd_2005104] using wordTrace_append hprefix tailTrace_2005104
  have hstable : (prefixWord ++ tailWord_2005104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005104).length < 2 ^ (prefixWord ++ tailWord_2005104).sum := by decide
  have hdescent : baseEnd_2005104 < baseStart_2005104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005140 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2005140 : Nat := 118140960795 + 2005140 * 2 ^ 59
def prefixEnd_2005140 : Nat := 4983230072969 + 3 ^ 40 * 2005140 * 2
def baseEnd_2005140 : Nat := 686400399704260076152357

theorem tailTrace_2005140 : CollatzResearch.WordTrace tailWord_2005140 prefixEnd_2005140 686400399704260076152357 := by
  unfold tailWord_2005140
  simp only [CollatzResearch.WordTrace]
  refine ⟨36566731977863852746610437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48755642637151803662147249 36566731977863852746610437)
  ·
    refine ⟨6856262245849472389989457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36566731977863852746610437 6856262245849472389989457)
    ·
      refine ⟨5142196684387104292492093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6856262245849472389989457 5142196684387104292492093)
      ·
        refine ⟨1928323756645164109684535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5142196684387104292492093 1928323756645164109684535)
        ·
          refine ⟨2892485634967746164526803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928323756645164109684535 2892485634967746164526803)
          ·
            refine ⟨4338728452451619246790205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892485634967746164526803 4338728452451619246790205)
            ·
              refine ⟨1627023169669357217546327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4338728452451619246790205 1627023169669357217546327)
              ·
                refine ⟨2440534754504035826319491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627023169669357217546327 2440534754504035826319491)
                ·
                  refine ⟨3660802131756053739479237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440534754504035826319491 3660802131756053739479237)
                  ·
                    refine ⟨686400399704260076152357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660802131756053739479237 686400399704260076152357)
                    ·
                      rfl

theorem cell22_2005140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2005140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005140 prefixEnd_2005140 := by exact prefixLift 2005140
  have htrace : WordTrace (prefixWord ++ tailWord_2005140) baseStart_2005140 baseEnd_2005140 := by
    simpa [prefixWord, tailWord_2005140, baseEnd_2005140] using wordTrace_append hprefix tailTrace_2005140
  have hstable : (prefixWord ++ tailWord_2005140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005140).length < 2 ^ (prefixWord ++ tailWord_2005140).sum := by decide
  have hdescent : baseEnd_2005140 < baseStart_2005140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005185 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2005185 : Nat := 118140960795 + 2005185 * 2 ^ 59
def prefixEnd_2005185 : Nat := 4983230072969 + 3 ^ 40 * 2005185 * 2
def baseEnd_2005185 : Nat := 686415804123894958777219

theorem tailTrace_2005185 : CollatzResearch.WordTrace tailWord_2005185 prefixEnd_2005185 686415804123894958777219 := by
  unfold tailWord_2005185
  simp only [CollatzResearch.WordTrace]
  refine ⟨73135105240564678178609009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48756736827043118785739339 73135105240564678178609009)
  ·
    refine ⟨54851328930423508633956757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73135105240564678178609009 54851328930423508633956757)
    ·
      refine ⟨2571156043613601967216723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54851328930423508633956757 2571156043613601967216723)
      ·
        refine ⟨3856734065420402950825085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571156043613601967216723 3856734065420402950825085)
        ·
          refine ⟨1446275274532651106559407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3856734065420402950825085 1446275274532651106559407)
          ·
            refine ⟨2169412911798976659839111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446275274532651106559407 2169412911798976659839111)
            ·
              refine ⟨3254119367698464989758667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169412911798976659839111 3254119367698464989758667)
              ·
                refine ⟨4881179051547697484638001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254119367698464989758667 4881179051547697484638001)
                ·
                  refine ⟨3660884288660773113478501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4881179051547697484638001 3660884288660773113478501)
                  ·
                    refine ⟨686415804123894958777219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3660884288660773113478501 686415804123894958777219)
                    ·
                      rfl

theorem cell22_2005185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2005185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005185 prefixEnd_2005185 := by exact prefixLift 2005185
  have htrace : WordTrace (prefixWord ++ tailWord_2005185) baseStart_2005185 baseEnd_2005185 := by
    simpa [prefixWord, tailWord_2005185, baseEnd_2005185] using wordTrace_append hprefix tailTrace_2005185
  have hstable : (prefixWord ++ tailWord_2005185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005185).length < 2 ^ (prefixWord ++ tailWord_2005185).sum := by decide
  have hdescent : baseEnd_2005185 < baseStart_2005185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005192 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_2005192 : Nat := 118140960795 + 2005192 * 2 ^ 59
def prefixEnd_2005192 : Nat := 4983230072969 + 3 ^ 40 * 2005192 * 2
def baseEnd_2005192 : Nat := 686418200366949273852197

theorem tailTrace_2005192 : CollatzResearch.WordTrace tailWord_2005192 prefixEnd_2005192 686418200366949273852197 := by
  unfold tailWord_2005192
  simp only [CollatzResearch.WordTrace]
  refine ⟨36567680275769659187056915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48756907034359545582742553 36567680275769659187056915)
  ·
    refine ⟨54851520413654488780585373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36567680275769659187056915 54851520413654488780585373)
    ·
      refine ⟨20569320155120433292719515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54851520413654488780585373 20569320155120433292719515)
      ·
        refine ⟨30853980232680649939079273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20569320155120433292719515 30853980232680649939079273)
        ·
          refine ⟨23140485174510487454309455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30853980232680649939079273 23140485174510487454309455)
          ·
            refine ⟨34710727761765731181464183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23140485174510487454309455 34710727761765731181464183)
            ·
              refine ⟨52066091642648596772196275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34710727761765731181464183 52066091642648596772196275)
              ·
                refine ⟨78099137463972895158294413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52066091642648596772196275 78099137463972895158294413)
                ·
                  refine ⟨29287176548989835684360405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78099137463972895158294413 29287176548989835684360405)
                  ·
                    refine ⟨686418200366949273852197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29287176548989835684360405 686418200366949273852197)
                    ·
                      rfl

theorem cell22_2005192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_2005192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005192 prefixEnd_2005192 := by exact prefixLift 2005192
  have htrace : WordTrace (prefixWord ++ tailWord_2005192) baseStart_2005192 baseEnd_2005192 := by
    simpa [prefixWord, tailWord_2005192, baseEnd_2005192] using wordTrace_append hprefix tailTrace_2005192
  have hstable : (prefixWord ++ tailWord_2005192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005192).length < 2 ^ (prefixWord ++ tailWord_2005192).sum := by decide
  have hdescent : baseEnd_2005192 < baseStart_2005192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005198 : List Nat := [4, 1, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2005198 : Nat := 118140960795 + 2005198 * 2 ^ 59
def prefixEnd_2005198 : Nat := 4983230072969 + 3 ^ 40 * 2005198 * 2
def baseEnd_2005198 : Nat := 686420254289567258202179

theorem tailTrace_2005198 : CollatzResearch.WordTrace tailWord_2005198 prefixEnd_2005198 686420254289567258202179 := by
  unfold tailWord_2005198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141947423689697674854031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48757052926345054265888165 9141947423689697674854031)
  ·
    refine ⟨13712921135534546512281047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9141947423689697674854031 13712921135534546512281047)
    ·
      refine ⟨20569381703301819768421571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13712921135534546512281047 20569381703301819768421571)
      ·
        refine ⟨30854072554952729652632357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20569381703301819768421571 30854072554952729652632357)
        ·
          refine ⟨5785138604053636809868567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30854072554952729652632357 5785138604053636809868567)
          ·
            refine ⟨8677707906080455214802851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785138604053636809868567 8677707906080455214802851)
            ·
              refine ⟨13016561859120682822204277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677707906080455214802851 13016561859120682822204277)
              ·
                refine ⟨1220302674292564014581651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13016561859120682822204277 1220302674292564014581651)
                ·
                  refine ⟨1830454011438846021872477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220302674292564014581651 1830454011438846021872477)
                  ·
                    refine ⟨686420254289567258202179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1830454011438846021872477 686420254289567258202179)
                    ·
                      rfl

theorem cell22_2005198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2005198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005198 prefixEnd_2005198 := by exact prefixLift 2005198
  have htrace : WordTrace (prefixWord ++ tailWord_2005198) baseStart_2005198 baseEnd_2005198 := by
    simpa [prefixWord, tailWord_2005198, baseEnd_2005198] using wordTrace_append hprefix tailTrace_2005198
  have hstable : (prefixWord ++ tailWord_2005198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005198).length < 2 ^ (prefixWord ++ tailWord_2005198).sum := by decide
  have hdescent : baseEnd_2005198 < baseStart_2005198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005269 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_2005269 : Nat := 118140960795 + 2005269 * 2 ^ 59
def prefixEnd_2005269 : Nat := 4983230072969 + 3 ^ 40 * 2005269 * 2
def baseEnd_2005269 : Nat := 686444559040546739676961

theorem tailTrace_2005269 : CollatzResearch.WordTrace tailWord_2005269 prefixEnd_2005269 686444559040546739676961 := by
  unfold tailWord_2005269
  simp only [CollatzResearch.WordTrace]
  refine ⟨73138168972260360524666861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48758779314840240349777907 73138168972260360524666861)
  ·
    refine ⟨27426813364597635196750073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73138168972260360524666861 27426813364597635196750073)
    ·
      refine ⟨20570110023448226397562555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27426813364597635196750073 20570110023448226397562555)
      ·
        refine ⟨30855165035172339596343833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20570110023448226397562555 30855165035172339596343833)
        ·
          refine ⟨23141373776379254697257875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30855165035172339596343833 23141373776379254697257875)
          ·
            refine ⟨34712060664568882045886813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23141373776379254697257875 34712060664568882045886813)
            ·
              refine ⟨13017022749213330767207555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34712060664568882045886813 13017022749213330767207555)
              ·
                refine ⟨19525534123819996150811333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13017022749213330767207555 19525534123819996150811333)
                ·
                  refine ⟨3661037648216249278277125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19525534123819996150811333 3661037648216249278277125)
                  ·
                    refine ⟨686444559040546739676961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3661037648216249278277125 686444559040546739676961)
                    ·
                      rfl

theorem cell22_2005269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_2005269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005269 prefixEnd_2005269 := by exact prefixLift 2005269
  have htrace : WordTrace (prefixWord ++ tailWord_2005269) baseStart_2005269 baseEnd_2005269 := by
    simpa [prefixWord, tailWord_2005269, baseEnd_2005269] using wordTrace_append hprefix tailTrace_2005269
  have hstable : (prefixWord ++ tailWord_2005269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005269).length < 2 ^ (prefixWord ++ tailWord_2005269).sum := by decide
  have hdescent : baseEnd_2005269 < baseStart_2005269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005271 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 4, 3]
def baseStart_2005271 : Nat := 118140960795 + 2005271 * 2 ^ 59
def prefixEnd_2005271 : Nat := 4983230072969 + 3 ^ 40 * 2005271 * 2
def baseEnd_2005271 : Nat := 686445243681419401126955

theorem tailTrace_2005271 : CollatzResearch.WordTrace tailWord_2005271 prefixEnd_2005271 686445243681419401126955 := by
  unfold tailWord_2005271
  simp only [CollatzResearch.WordTrace]
  refine ⟨73138241918253114866239667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48758827945502076577493111 73138241918253114866239667)
  ·
    refine ⟨109707362877379672299359501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73138241918253114866239667 109707362877379672299359501)
    ·
      refine ⟨41140261079017377112259813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109707362877379672299359501 41140261079017377112259813)
      ·
        refine ⟨7713798952315758208548715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41140261079017377112259813 7713798952315758208548715)
        ·
          refine ⟨11570698428473637312823073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713798952315758208548715 11570698428473637312823073)
          ·
            refine ⟨8678023821355227984617305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11570698428473637312823073 8678023821355227984617305)
            ·
              refine ⟨6508517866016420988462979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8678023821355227984617305 6508517866016420988462979)
              ·
                refine ⟨9762776799024631482694469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6508517866016420988462979 9762776799024631482694469)
                ·
                  refine ⟨1830520649817118403005213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9762776799024631482694469 1830520649817118403005213)
                  ·
                    refine ⟨686445243681419401126955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1830520649817118403005213 686445243681419401126955)
                    ·
                      rfl

theorem cell22_2005271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_2005271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005271 prefixEnd_2005271 := by exact prefixLift 2005271
  have htrace : WordTrace (prefixWord ++ tailWord_2005271) baseStart_2005271 baseEnd_2005271 := by
    simpa [prefixWord, tailWord_2005271, baseEnd_2005271] using wordTrace_append hprefix tailTrace_2005271
  have hstable : (prefixWord ++ tailWord_2005271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005271).length < 2 ^ (prefixWord ++ tailWord_2005271).sum := by decide
  have hdescent : baseEnd_2005271 < baseStart_2005271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005284 : List Nat := [2, 3, 1, 3, 1, 2, 1, 9]
def baseStart_2005284 : Nat := 118140960795 + 2005284 * 2 ^ 59
def prefixEnd_2005284 : Nat := 4983230072969 + 3 ^ 40 * 2005284 * 2
def baseEnd_2005284 : Nat := 76272188205232411172435

theorem tailTrace_2005284 : CollatzResearch.WordTrace tailWord_2005284 prefixEnd_2005284 76272188205232411172435 := by
  unfold tailWord_2005284
  simp only [CollatzResearch.WordTrace]
  refine ⟨36569358033603009043231453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48759144044804012057641937 36569358033603009043231453)
  ·
    refine ⟨13713509262601128391211795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36569358033603009043231453 13713509262601128391211795)
    ·
      refine ⟨20570263893901692586817693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13713509262601128391211795 20570263893901692586817693)
      ·
        refine ⟨7713848960213134720056635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20570263893901692586817693 7713848960213134720056635)
        ·
          refine ⟨11570773440319702080084953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713848960213134720056635 11570773440319702080084953)
          ·
            refine ⟨8678080080239776560063715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11570773440319702080084953 8678080080239776560063715)
            ·
              refine ⟨13017120120359664840095573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678080080239776560063715 13017120120359664840095573)
              ·
                refine ⟨76272188205232411172435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13017120120359664840095573 76272188205232411172435)
                ·
                  rfl

theorem cell22_2005284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 9].length) (baseStart_2005284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005284 prefixEnd_2005284 := by exact prefixLift 2005284
  have htrace : WordTrace (prefixWord ++ tailWord_2005284) baseStart_2005284 baseEnd_2005284 := by
    simpa [prefixWord, tailWord_2005284, baseEnd_2005284] using wordTrace_append hprefix tailTrace_2005284
  have hstable : (prefixWord ++ tailWord_2005284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005284).length < 2 ^ (prefixWord ++ tailWord_2005284).sum := by decide
  have hdescent : baseEnd_2005284 < baseStart_2005284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005418 : List Nat := [3, 1, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2005418 : Nat := 118140960795 + 2005418 * 2 ^ 59
def prefixEnd_2005418 : Nat := 4983230072969 + 3 ^ 40 * 2005418 * 2
def baseEnd_2005418 : Nat := 686495564785560017701505

theorem tailTrace_2005418 : CollatzResearch.WordTrace tailWord_2005418 prefixEnd_2005418 686495564785560017701505 := by
  unfold tailWord_2005418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18285900862180139742960227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48762402299147039314560605 18285900862180139742960227)
  ·
    refine ⟨27428851293270209614440341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18285900862180139742960227 27428851293270209614440341)
    ·
      refine ⟨1285727404372041075676891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27428851293270209614440341 1285727404372041075676891)
      ·
        refine ⟨1928591106558061613515337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285727404372041075676891 1928591106558061613515337)
        ·
          refine ⟨1446443329918546210136503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928591106558061613515337 1446443329918546210136503)
          ·
            refine ⟨2169664994877819315204755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446443329918546210136503 2169664994877819315204755)
            ·
              refine ⟨3254497492316728972807133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169664994877819315204755 3254497492316728972807133)
              ·
                refine ⟨1220436559618773364802675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3254497492316728972807133 1220436559618773364802675)
                ·
                  refine ⟨1830654839428160047204013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220436559618773364802675 1830654839428160047204013)
                  ·
                    refine ⟨686495564785560017701505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1830654839428160047204013 686495564785560017701505)
                    ·
                      rfl

theorem cell22_2005418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2005418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005418 prefixEnd_2005418 := by exact prefixLift 2005418
  have htrace : WordTrace (prefixWord ++ tailWord_2005418) baseStart_2005418 baseEnd_2005418 := by
    simpa [prefixWord, tailWord_2005418, baseEnd_2005418] using wordTrace_append hprefix tailTrace_2005418
  have hstable : (prefixWord ++ tailWord_2005418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005418).length < 2 ^ (prefixWord ++ tailWord_2005418).sum := by decide
  have hdescent : baseEnd_2005418 < baseStart_2005418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005425 : List Nat := [1, 2, 2, 4, 1, 4, 1, 3, 4]
def baseStart_2005425 : Nat := 118140960795 + 2005425 * 2 ^ 59
def prefixEnd_2005425 : Nat := 4983230072969 + 3 ^ 40 * 2005425 * 2
def baseEnd_2005425 : Nat := 228832653676204777592161

theorem tailTrace_2005425 : CollatzResearch.WordTrace tailWord_2005425 prefixEnd_2005425 228832653676204777592161 := by
  unfold tailWord_2005425
  simp only [CollatzResearch.WordTrace]
  refine ⟨73143858759695199167345729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48762572506463466111563819 73143858759695199167345729)
  ·
    refine ⟨54857894069771399375509297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73143858759695199167345729 54857894069771399375509297)
    ·
      refine ⟨41143420552328549531631973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54857894069771399375509297 41143420552328549531631973)
      ·
        refine ⟨7714391353561603037180995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41143420552328549531631973 7714391353561603037180995)
        ·
          refine ⟨11571587030342404555771493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714391353561603037180995 11571587030342404555771493)
          ·
            refine ⟨2169672568189200854207155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11571587030342404555771493 2169672568189200854207155)
            ·
              refine ⟨3254508852283801281310733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169672568189200854207155 3254508852283801281310733)
              ·
                refine ⟨1220440819606425480491525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3254508852283801281310733 1220440819606425480491525)
                ·
                  refine ⟨228832653676204777592161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1220440819606425480491525 228832653676204777592161)
                  ·
                    rfl

theorem cell22_2005425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 4].length) (baseStart_2005425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005425 prefixEnd_2005425 := by exact prefixLift 2005425
  have htrace : WordTrace (prefixWord ++ tailWord_2005425) baseStart_2005425 baseEnd_2005425 := by
    simpa [prefixWord, tailWord_2005425, baseEnd_2005425] using wordTrace_append hprefix tailTrace_2005425
  have hstable : (prefixWord ++ tailWord_2005425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005425).length < 2 ^ (prefixWord ++ tailWord_2005425).sum := by decide
  have hdescent : baseEnd_2005425 < baseStart_2005425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005436 : List Nat := [2, 2, 2, 4, 1, 1, 10]
def baseStart_2005436 : Nat := 118140960795 + 2005436 * 2 ^ 59
def prefixEnd_2005436 : Nat := 4983230072969 + 3 ^ 40 * 2005436 * 2
def baseEnd_2005436 : Nat := 25425989872348665583387

theorem tailTrace_2005436 : CollatzResearch.WordTrace tailWord_2005436 prefixEnd_2005436 25425989872348665583387 := by
  unfold tailWord_2005436
  simp only [CollatzResearch.WordTrace]
  refine ⟨36572129981327674022998081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48762839975103565363997441 36572129981327674022998081)
  ·
    refine ⟨27429097485995755517248561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36572129981327674022998081 27429097485995755517248561)
    ·
      refine ⟨20571823114496816637936421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27429097485995755517248561 20571823114496816637936421)
      ·
        refine ⟨3857216833968153119613079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20571823114496816637936421 3857216833968153119613079)
        ·
          refine ⟨5785825250952229679419619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857216833968153119613079 5785825250952229679419619)
          ·
            refine ⟨8678737876428344519129429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785825250952229679419619 8678737876428344519129429)
            ·
              refine ⟨25425989872348665583387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8678737876428344519129429 25425989872348665583387)
              ·
                rfl

theorem cell22_2005436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 10].length) (baseStart_2005436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005436 prefixEnd_2005436 := by exact prefixLift 2005436
  have htrace : WordTrace (prefixWord ++ tailWord_2005436) baseStart_2005436 baseEnd_2005436 := by
    simpa [prefixWord, tailWord_2005436, baseEnd_2005436] using wordTrace_append hprefix tailTrace_2005436
  have hstable : (prefixWord ++ tailWord_2005436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005436).length < 2 ^ (prefixWord ++ tailWord_2005436).sum := by decide
  have hdescent : baseEnd_2005436 < baseStart_2005436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005496 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_2005496 : Nat := 118140960795 + 2005496 * 2 ^ 59
def prefixEnd_2005496 : Nat := 4983230072969 + 3 ^ 40 * 2005496 * 2
def baseEnd_2005496 : Nat := 686522265779593814251265

theorem tailTrace_2005496 : CollatzResearch.WordTrace tailWord_2005496 prefixEnd_2005496 686522265779593814251265 := by
  unfold tailWord_2005496
  simp only [CollatzResearch.WordTrace]
  refine ⟨36573224171218989146590171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48764298894958652195453561 36573224171218989146590171)
  ·
    refine ⟨54859836256828483719885257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36573224171218989146590171 54859836256828483719885257)
    ·
      refine ⟨41144877192621362789913943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54859836256828483719885257 41144877192621362789913943)
      ·
        refine ⟨61717315788932044184870915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41144877192621362789913943 61717315788932044184870915)
        ·
          refine ⟨92575973683398066277306373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61717315788932044184870915 92575973683398066277306373)
          ·
            refine ⟨17357995065637137426994945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92575973683398066277306373 17357995065637137426994945)
            ·
              refine ⟨13018496299227853070246209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17357995065637137426994945 13018496299227853070246209)
              ·
                refine ⟨9763872224420889802684657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13018496299227853070246209 9763872224420889802684657)
                ·
                  refine ⟨7322904168315667352013493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9763872224420889802684657 7322904168315667352013493)
                  ·
                    refine ⟨686522265779593814251265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7322904168315667352013493 686522265779593814251265)
                    ·
                      rfl

theorem cell22_2005496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_2005496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005496 prefixEnd_2005496 := by exact prefixLift 2005496
  have htrace : WordTrace (prefixWord ++ tailWord_2005496) baseStart_2005496 baseEnd_2005496 := by
    simpa [prefixWord, tailWord_2005496, baseEnd_2005496] using wordTrace_append hprefix tailTrace_2005496
  have hstable : (prefixWord ++ tailWord_2005496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005496).length < 2 ^ (prefixWord ++ tailWord_2005496).sum := by decide
  have hdescent : baseEnd_2005496 < baseStart_2005496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005528 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_2005528 : Nat := 118140960795 + 2005528 * 2 ^ 59
def prefixEnd_2005528 : Nat := 4983230072969 + 3 ^ 40 * 2005528 * 2
def baseEnd_2005528 : Nat := 686533220033556397451167

theorem tailTrace_2005528 : CollatzResearch.WordTrace tailWord_2005528 prefixEnd_2005528 686533220033556397451167 := by
  unfold tailWord_2005528
  simp only [CollatzResearch.WordTrace]
  refine ⟨36573807739161023879172619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48765076985548031838896825 36573807739161023879172619)
  ·
    refine ⟨54860711608741535818758929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36573807739161023879172619 54860711608741535818758929)
    ·
      refine ⟨41145533706556151864069197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54860711608741535818758929 41145533706556151864069197)
      ·
        refine ⟨15429575139958556949025949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41145533706556151864069197 15429575139958556949025949)
        ·
          refine ⟨5786090677484458855884731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15429575139958556949025949 5786090677484458855884731)
          ·
            refine ⟨8679136016226688283827097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786090677484458855884731 8679136016226688283827097)
            ·
              refine ⟨6509352012170016212870323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8679136016226688283827097 6509352012170016212870323)
              ·
                refine ⟨9764028018255024319305485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6509352012170016212870323 9764028018255024319305485)
                ·
                  refine ⟨3661510506845634119739557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9764028018255024319305485 3661510506845634119739557)
                  ·
                    refine ⟨686533220033556397451167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3661510506845634119739557 686533220033556397451167)
                    ·
                      rfl

theorem cell22_2005528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_2005528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005528 prefixEnd_2005528 := by exact prefixLift 2005528
  have htrace : WordTrace (prefixWord ++ tailWord_2005528) baseStart_2005528 baseEnd_2005528 := by
    simpa [prefixWord, tailWord_2005528, baseEnd_2005528] using wordTrace_append hprefix tailTrace_2005528
  have hstable : (prefixWord ++ tailWord_2005528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005528).length < 2 ^ (prefixWord ++ tailWord_2005528).sum := by decide
  have hdescent : baseEnd_2005528 < baseStart_2005528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005575 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 1, 5]
def baseStart_2005575 : Nat := 118140960795 + 2005575 * 2 ^ 59
def prefixEnd_2005575 : Nat := 4983230072969 + 3 ^ 40 * 2005575 * 2
def baseEnd_2005575 : Nat := 686549309094063941526023

theorem tailTrace_2005575 : CollatzResearch.WordTrace tailWord_2005575 prefixEnd_2005575 686549309094063941526023 := by
  unfold tailWord_2005575
  simp only [CollatzResearch.WordTrace]
  refine ⟨73149329709151774785306179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48766219806101183190204119 73149329709151774785306179)
  ·
    refine ⟨109723994563727662177959269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73149329709151774785306179 109723994563727662177959269)
    ·
      refine ⟨20573248980698936658367363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109723994563727662177959269 20573248980698936658367363)
      ·
        refine ⟨30859873471048404987551045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20573248980698936658367363 30859873471048404987551045)
        ·
          refine ⟨5786226275821575935165821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30859873471048404987551045 5786226275821575935165821)
          ·
            refine ⟨2169834853433090975687183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5786226275821575935165821 2169834853433090975687183)
            ·
              refine ⟨3254752280149636463530775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169834853433090975687183 3254752280149636463530775)
              ·
                refine ⟨4882128420224454695296163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254752280149636463530775 4882128420224454695296163)
                ·
                  refine ⟨7323192630336682042944245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882128420224454695296163 7323192630336682042944245)
                  ·
                    refine ⟨686549309094063941526023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7323192630336682042944245 686549309094063941526023)
                    ·
                      rfl

theorem cell22_2005575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_2005575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005575 prefixEnd_2005575 := by exact prefixLift 2005575
  have htrace : WordTrace (prefixWord ++ tailWord_2005575) baseStart_2005575 baseEnd_2005575 := by
    simpa [prefixWord, tailWord_2005575, baseEnd_2005575] using wordTrace_append hprefix tailTrace_2005575
  have hstable : (prefixWord ++ tailWord_2005575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005575).length < 2 ^ (prefixWord ++ tailWord_2005575).sum := by decide
  have hdescent : baseEnd_2005575 < baseStart_2005575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005588 : List Nat := [2, 4, 1, 1, 1, 4, 1, 8]
def baseStart_2005588 : Nat := 118140960795 + 2005588 * 2 ^ 59
def prefixEnd_2005588 : Nat := 4983230072969 + 3 ^ 40 * 2005588 * 2
def baseEnd_2005588 : Nat := 76283751028859582327887

theorem tailTrace_2005588 : CollatzResearch.WordTrace tailWord_2005588 prefixEnd_2005588 76283751028859582327887 := by
  unfold tailWord_2005588
  simp only [CollatzResearch.WordTrace]
  refine ⟨36574901929052339002764709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48766535905403118670352945 36574901929052339002764709)
  ·
    refine ⟨6857794111697313563018383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36574901929052339002764709 6857794111697313563018383)
    ·
      refine ⟨10286691167545970344527575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6857794111697313563018383 10286691167545970344527575)
      ·
        refine ⟨15430036751318955516791363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10286691167545970344527575 15430036751318955516791363)
        ·
          refine ⟨23145055126978433275187045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15430036751318955516791363 23145055126978433275187045)
          ·
            refine ⟨4339697836308456239097571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23145055126978433275187045 4339697836308456239097571)
            ·
              refine ⟨6509546754462684358646357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339697836308456239097571 6509546754462684358646357)
              ·
                refine ⟨76283751028859582327887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6509546754462684358646357 76283751028859582327887)
                ·
                  rfl

theorem cell22_2005588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 8].length) (baseStart_2005588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005588 prefixEnd_2005588 := by exact prefixLift 2005588
  have htrace : WordTrace (prefixWord ++ tailWord_2005588) baseStart_2005588 baseEnd_2005588 := by
    simpa [prefixWord, tailWord_2005588, baseEnd_2005588] using wordTrace_append hprefix tailTrace_2005588
  have hstable : (prefixWord ++ tailWord_2005588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005588).length < 2 ^ (prefixWord ++ tailWord_2005588).sum := by decide
  have hdescent : baseEnd_2005588 < baseStart_2005588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005605 : List Nat := [1, 3, 1, 3, 5, 1, 8]
def baseStart_2005605 : Nat := 118140960795 + 2005605 * 2 ^ 59
def prefixEnd_2005605 : Nat := 4983230072969 + 3 ^ 40 * 2005605 * 2
def baseEnd_2005605 : Nat := 25428132544709402343553

theorem tailTrace_2005605 : CollatzResearch.WordTrace tailWord_2005605 prefixEnd_2005605 25428132544709402343553 := by
  unfold tailWord_2005605
  simp only [CollatzResearch.WordTrace]
  refine ⟨73150423899043089908898269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48766949266028726605932179 73150423899043089908898269)
  ·
    refine ⟨27431408962141158715836851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73150423899043089908898269 27431408962141158715836851)
    ·
      refine ⟨41147113443211738073755277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27431408962141158715836851 41147113443211738073755277)
      ·
        refine ⟨15430167541204401777658229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41147113443211738073755277 15430167541204401777658229)
        ·
          refine ⟨1446578206987912666655459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15430167541204401777658229 1446578206987912666655459)
          ·
            refine ⟨2169867310481868999983189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446578206987912666655459 2169867310481868999983189)
            ·
              refine ⟨25428132544709402343553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2169867310481868999983189 25428132544709402343553)
              ·
                rfl

theorem cell22_2005605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 8].length) (baseStart_2005605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005605 prefixEnd_2005605 := by exact prefixLift 2005605
  have htrace : WordTrace (prefixWord ++ tailWord_2005605) baseStart_2005605 baseEnd_2005605 := by
    simpa [prefixWord, tailWord_2005605, baseEnd_2005605] using wordTrace_append hprefix tailTrace_2005605
  have hstable : (prefixWord ++ tailWord_2005605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005605).length < 2 ^ (prefixWord ++ tailWord_2005605).sum := by decide
  have hdescent : baseEnd_2005605 < baseStart_2005605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005671 : List Nat := [1, 1, 6, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2005671 : Nat := 118140960795 + 2005671 * 2 ^ 59
def prefixEnd_2005671 : Nat := 4983230072969 + 3 ^ 40 * 2005671 * 2
def baseEnd_2005671 : Nat := 686582171855951691125729

theorem tailTrace_2005671 : CollatzResearch.WordTrace tailWord_2005671 prefixEnd_2005671 686582171855951691125729 := by
  unfold tailWord_2005671
  simp only [CollatzResearch.WordTrace]
  refine ⟨73152831116803983180800867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48768554077869322120533911 73152831116803983180800867)
  ·
    refine ⟨109729246675205974771201301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73152831116803983180800867 109729246675205974771201301)
    ·
      refine ⟨5143558437900280067400061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109729246675205974771201301 5143558437900280067400061)
      ·
        refine ⟨1928834414212605025275023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5143558437900280067400061 1928834414212605025275023)
        ·
          refine ⟨2893251621318907537912535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928834414212605025275023 2893251621318907537912535)
          ·
            refine ⟨4339877431978361306868803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893251621318907537912535 4339877431978361306868803)
            ·
              refine ⟨6509816147967541960303205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339877431978361306868803 6509816147967541960303205)
              ·
                refine ⟨1220590527743914117556851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6509816147967541960303205 1220590527743914117556851)
                ·
                  refine ⟨1830885791615871176335277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220590527743914117556851 1830885791615871176335277)
                  ·
                    refine ⟨686582171855951691125729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1830885791615871176335277 686582171855951691125729)
                    ·
                      rfl

theorem cell22_2005671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2005671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005671 prefixEnd_2005671 := by exact prefixLift 2005671
  have htrace : WordTrace (prefixWord ++ tailWord_2005671) baseStart_2005671 baseEnd_2005671 := by
    simpa [prefixWord, tailWord_2005671, baseEnd_2005671] using wordTrace_append hprefix tailTrace_2005671
  have hstable : (prefixWord ++ tailWord_2005671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005671).length < 2 ^ (prefixWord ++ tailWord_2005671).sum := by decide
  have hdescent : baseEnd_2005671 < baseStart_2005671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005710 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_2005710 : Nat := 118140960795 + 2005710 * 2 ^ 59
def prefixEnd_2005710 : Nat := 4983230072969 + 3 ^ 40 * 2005710 * 2
def baseEnd_2005710 : Nat := 686595522352968589400609

theorem tailTrace_2005710 : CollatzResearch.WordTrace tailWord_2005710 prefixEnd_2005710 686595522352968589400609 := by
  unfold tailWord_2005710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9144281695457836605183823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48769502375775128560980389 9144281695457836605183823)
  ·
    refine ⟨13716422543186754907775735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9144281695457836605183823 13716422543186754907775735)
    ·
      refine ⟨20574633814780132361663603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13716422543186754907775735 20574633814780132361663603)
      ·
        refine ⟨30861950722170198542495405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20574633814780132361663603 30861950722170198542495405)
        ·
          refine ⟨11573231520813824453435777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30861950722170198542495405 11573231520813824453435777)
          ·
            refine ⟨8679923640610368340076833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11573231520813824453435777 8679923640610368340076833)
            ·
              refine ⟨6509942730457776255057625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8679923640610368340076833 6509942730457776255057625)
              ·
                refine ⟨4882457047843332191293219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6509942730457776255057625 4882457047843332191293219)
                ·
                  refine ⟨7323685571764998286939829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882457047843332191293219 7323685571764998286939829)
                  ·
                    refine ⟨686595522352968589400609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7323685571764998286939829 686595522352968589400609)
                    ·
                      rfl

theorem cell22_2005710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_2005710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005710 prefixEnd_2005710 := by exact prefixLift 2005710
  have htrace : WordTrace (prefixWord ++ tailWord_2005710) baseStart_2005710 baseEnd_2005710 := by
    simpa [prefixWord, tailWord_2005710, baseEnd_2005710] using wordTrace_append hprefix tailTrace_2005710
  have hstable : (prefixWord ++ tailWord_2005710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005710).length < 2 ^ (prefixWord ++ tailWord_2005710).sum := by decide
  have hdescent : baseEnd_2005710 < baseStart_2005710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005727 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 2, 3]
def baseStart_2005727 : Nat := 118140960795 + 2005727 * 2 ^ 59
def prefixEnd_2005727 : Nat := 4983230072969 + 3 ^ 40 * 2005727 * 2
def baseEnd_2005727 : Nat := 686601341800386211725557

theorem tailTrace_2005727 : CollatzResearch.WordTrace tailWord_2005727 prefixEnd_2005727 686601341800386211725557 := by
  unfold tailWord_2005727
  simp only [CollatzResearch.WordTrace]
  refine ⟨73154873604601104744839435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48769915736400736496559623 73154873604601104744839435)
  ·
    refine ⟨109732310406901657117259153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73154873604601104744839435 109732310406901657117259153)
    ·
      refine ⟨82299232805176242837944365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109732310406901657117259153 82299232805176242837944365)
      ·
        refine ⟨30862212301941091064229137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82299232805176242837944365 30862212301941091064229137)
        ·
          refine ⟨23146659226455818298171853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30862212301941091064229137 23146659226455818298171853)
          ·
            refine ⟨8679997209920931861814445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23146659226455818298171853 8679997209920931861814445)
            ·
              refine ⟨3254998953720349448180417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8679997209920931861814445 3254998953720349448180417)
              ·
                refine ⟨2441249215290262086135313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3254998953720349448180417 2441249215290262086135313)
                ·
                  refine ⟨1830936911467696564601485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2441249215290262086135313 1830936911467696564601485)
                  ·
                    refine ⟨686601341800386211725557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1830936911467696564601485 686601341800386211725557)
                    ·
                      rfl

theorem cell22_2005727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_2005727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005727 prefixEnd_2005727 := by exact prefixLift 2005727
  have htrace : WordTrace (prefixWord ++ tailWord_2005727) baseStart_2005727 baseEnd_2005727 := by
    simpa [prefixWord, tailWord_2005727, baseEnd_2005727] using wordTrace_append hprefix tailTrace_2005727
  have hstable : (prefixWord ++ tailWord_2005727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005727).length < 2 ^ (prefixWord ++ tailWord_2005727).sum := by decide
  have hdescent : baseEnd_2005727 < baseStart_2005727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005753 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_2005753 : Nat := 118140960795 + 2005753 * 2 ^ 59
def prefixEnd_2005753 : Nat := 4983230072969 + 3 ^ 40 * 2005753 * 2
def baseEnd_2005753 : Nat := 686610242131730810575477

theorem tailTrace_2005753 : CollatzResearch.WordTrace tailWord_2005753 prefixEnd_2005753 686610242131730810575477 := by
  unfold tailWord_2005753
  simp only [CollatzResearch.WordTrace]
  refine ⟨73155821902506911185285913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48770547935004607456857275 73155821902506911185285913)
  ·
    refine ⟨54866866426880183388964435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73155821902506911185285913 54866866426880183388964435)
    ·
      refine ⟨82300299640320275083446653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54866866426880183388964435 82300299640320275083446653)
      ·
        refine ⟨30862612365120103156292495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82300299640320275083446653 30862612365120103156292495)
        ·
          refine ⟨46293918547680154734438743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30862612365120103156292495 46293918547680154734438743)
          ·
            refine ⟨69440877821520232101658115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46293918547680154734438743 69440877821520232101658115)
            ·
              refine ⟨104161316732280348152487173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69440877821520232101658115 104161316732280348152487173)
              ·
                refine ⟨19530246887302565278591345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104161316732280348152487173 19530246887302565278591345)
                ·
                  refine ⟨14647685165476923958943509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19530246887302565278591345 14647685165476923958943509)
                  ·
                    refine ⟨686610242131730810575477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14647685165476923958943509 686610242131730810575477)
                    ·
                      rfl

theorem cell22_2005753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_2005753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005753 prefixEnd_2005753 := by exact prefixLift 2005753
  have htrace : WordTrace (prefixWord ++ tailWord_2005753) baseStart_2005753 baseEnd_2005753 := by
    simpa [prefixWord, tailWord_2005753, baseEnd_2005753] using wordTrace_append hprefix tailTrace_2005753
  have hstable : (prefixWord ++ tailWord_2005753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005753).length < 2 ^ (prefixWord ++ tailWord_2005753).sum := by decide
  have hdescent : baseEnd_2005753 < baseStart_2005753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005800 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2005800 : Nat := 118140960795 + 2005800 * 2 ^ 59
def prefixEnd_2005800 : Nat := 4983230072969 + 3 ^ 40 * 2005800 * 2
def baseEnd_2005800 : Nat := 686626331192238354650333

theorem tailTrace_2005800 : CollatzResearch.WordTrace tailWord_2005800 prefixEnd_2005800 686626331192238354650333 := by
  unfold tailWord_2005800
  simp only [CollatzResearch.WordTrace]
  refine ⟨36578768066668319106123427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48771690755557758808164569 36578768066668319106123427)
  ·
    refine ⟨54868152100002478659185141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36578768066668319106123427 54868152100002478659185141)
    ·
      refine ⟨5143889259375232374298607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54868152100002478659185141 5143889259375232374298607)
      ·
        refine ⟨7715833889062848561447911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5143889259375232374298607 7715833889062848561447911)
        ·
          refine ⟨11573750833594272842171867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7715833889062848561447911 11573750833594272842171867)
          ·
            refine ⟨17360626250391409263257801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11573750833594272842171867 17360626250391409263257801)
            ·
              refine ⟨13020469687793556947443351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17360626250391409263257801 13020469687793556947443351)
              ·
                refine ⟨19530704531690335421165027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13020469687793556947443351 19530704531690335421165027)
                ·
                  refine ⟨29296056797535503131747541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19530704531690335421165027 29296056797535503131747541)
                  ·
                    refine ⟨686626331192238354650333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29296056797535503131747541 686626331192238354650333)
                    ·
                      rfl

theorem cell22_2005800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2005800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005800 prefixEnd_2005800 := by exact prefixLift 2005800
  have htrace : WordTrace (prefixWord ++ tailWord_2005800) baseStart_2005800 baseEnd_2005800 := by
    simpa [prefixWord, tailWord_2005800, baseEnd_2005800] using wordTrace_append hprefix tailTrace_2005800
  have hstable : (prefixWord ++ tailWord_2005800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005800).length < 2 ^ (prefixWord ++ tailWord_2005800).sum := by decide
  have hdescent : baseEnd_2005800 < baseStart_2005800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005815 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 3, 4]
def baseStart_2005815 : Nat := 118140960795 + 2005815 * 2 ^ 59
def prefixEnd_2005815 : Nat := 4983230072969 + 3 ^ 40 * 2005815 * 2
def baseEnd_2005815 : Nat := 686631465998783315525287

theorem tailTrace_2005815 : CollatzResearch.WordTrace tailWord_2005815 prefixEnd_2005815 686631465998783315525287 := by
  unfold tailWord_2005815
  simp only [CollatzResearch.WordTrace]
  refine ⟨73158083228282295774042899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48772055485521530516028599 73158083228282295774042899)
  ·
    refine ⟨109737124842423443661064349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73158083228282295774042899 109737124842423443661064349)
    ·
      refine ⟨41151421815908791372899131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109737124842423443661064349 41151421815908791372899131)
      ·
        refine ⟨61727132723863187059348697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41151421815908791372899131 61727132723863187059348697)
        ·
          refine ⟨46295349542897390294511523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61727132723863187059348697 46295349542897390294511523)
          ·
            refine ⟨69443024314346085441767285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46295349542897390294511523 69443024314346085441767285)
            ·
              refine ⟨6510283529469945510165683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69443024314346085441767285 6510283529469945510165683)
              ·
                refine ⟨9765425294204918265248525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510283529469945510165683 9765425294204918265248525)
                ·
                  refine ⟨3662034485326844349468197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9765425294204918265248525 3662034485326844349468197)
                  ·
                    refine ⟨686631465998783315525287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3662034485326844349468197 686631465998783315525287)
                    ·
                      rfl

theorem cell22_2005815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_2005815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005815 prefixEnd_2005815 := by exact prefixLift 2005815
  have htrace : WordTrace (prefixWord ++ tailWord_2005815) baseStart_2005815 baseEnd_2005815 := by
    simpa [prefixWord, tailWord_2005815, baseEnd_2005815] using wordTrace_append hprefix tailTrace_2005815
  have hstable : (prefixWord ++ tailWord_2005815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005815).length < 2 ^ (prefixWord ++ tailWord_2005815).sum := by decide
  have hdescent : baseEnd_2005815 < baseStart_2005815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005845 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_2005845 : Nat := 118140960795 + 2005845 * 2 ^ 59
def prefixEnd_2005845 : Nat := 4983230072969 + 3 ^ 40 * 2005845 * 2
def baseEnd_2005845 : Nat := 686641735611873237275195

theorem tailTrace_2005845 : CollatzResearch.WordTrace tailWord_2005845 prefixEnd_2005845 686641735611873237275195 := by
  unfold tailWord_2005845
  simp only [CollatzResearch.WordTrace]
  refine ⟨73159177418173610897634989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48772784945449073931756659 73159177418173610897634989)
  ·
    refine ⟨27434691531815104086613121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73159177418173610897634989 27434691531815104086613121)
    ·
      refine ⟨20576018648861328064959841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27434691531815104086613121 20576018648861328064959841)
      ·
        refine ⟨15432013986645996048719881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20576018648861328064959841 15432013986645996048719881)
        ·
          refine ⟨11574010489984497036539911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15432013986645996048719881 11574010489984497036539911)
          ·
            refine ⟨17361015734976745554809867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11574010489984497036539911 17361015734976745554809867)
            ·
              refine ⟨26041523602465118332214801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17361015734976745554809867 26041523602465118332214801)
              ·
                refine ⟨19531142701848838749161101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26041523602465118332214801 19531142701848838749161101)
                ·
                  refine ⟨7324178513193314530935413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19531142701848838749161101 7324178513193314530935413)
                  ·
                    refine ⟨686641735611873237275195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7324178513193314530935413 686641735611873237275195)
                    ·
                      rfl

theorem cell22_2005845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_2005845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005845 prefixEnd_2005845 := by exact prefixLift 2005845
  have htrace : WordTrace (prefixWord ++ tailWord_2005845) baseStart_2005845 baseEnd_2005845 := by
    simpa [prefixWord, tailWord_2005845, baseEnd_2005845] using wordTrace_append hprefix tailTrace_2005845
  have hstable : (prefixWord ++ tailWord_2005845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005845).length < 2 ^ (prefixWord ++ tailWord_2005845).sum := by decide
  have hdescent : baseEnd_2005845 < baseStart_2005845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005877 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2005877 : Nat := 118140960795 + 2005877 * 2 ^ 59
def prefixEnd_2005877 : Nat := 4983230072969 + 3 ^ 40 * 2005877 * 2
def baseEnd_2005877 : Nat := 686652689865835820475097

theorem tailTrace_2005877 : CollatzResearch.WordTrace tailWord_2005877 prefixEnd_2005877 686652689865835820475097 := by
  unfold tailWord_2005877
  simp only [CollatzResearch.WordTrace]
  refine ⟨73160344554057680362799885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48773563036038453575199923 73160344554057680362799885)
  ·
    refine ⟨27435129207771630136049957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73160344554057680362799885 27435129207771630136049957)
    ·
      refine ⟨5144086726457180650509367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27435129207771630136049957 5144086726457180650509367)
      ·
        refine ⟨7716130089685770975764051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144086726457180650509367 7716130089685770975764051)
        ·
          refine ⟨11574195134528656463646077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716130089685770975764051 11574195134528656463646077)
          ·
            refine ⟨4340323175448246173867279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11574195134528656463646077 4340323175448246173867279)
            ·
              refine ⟨6510484763172369260800919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340323175448246173867279 6510484763172369260800919)
              ·
                refine ⟨9765727144758553891201379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510484763172369260800919 9765727144758553891201379)
                ·
                  refine ⟨14648590717137830836802069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765727144758553891201379 14648590717137830836802069)
                  ·
                    refine ⟨686652689865835820475097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14648590717137830836802069 686652689865835820475097)
                    ·
                      rfl

theorem cell22_2005877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2005877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005877 prefixEnd_2005877 := by exact prefixLift 2005877
  have htrace : WordTrace (prefixWord ++ tailWord_2005877) baseStart_2005877 baseEnd_2005877 := by
    simpa [prefixWord, tailWord_2005877, baseEnd_2005877] using wordTrace_append hprefix tailTrace_2005877
  have hstable : (prefixWord ++ tailWord_2005877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005877).length < 2 ^ (prefixWord ++ tailWord_2005877).sum := by decide
  have hdescent : baseEnd_2005877 < baseStart_2005877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005896 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 2, 3]
def baseStart_2005896 : Nat := 118140960795 + 2005896 * 2 ^ 59
def prefixEnd_2005896 : Nat := 4983230072969 + 3 ^ 40 * 2005896 * 2
def baseEnd_2005896 : Nat := 686659193954126104250039

theorem tailTrace_2005896 : CollatzResearch.WordTrace tailWord_2005896 prefixEnd_2005896 686659193954126104250039 := by
  unfold tailWord_2005896
  simp only [CollatzResearch.WordTrace]
  refine ⟨36580518770494423303870771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48774025027325897738494361 36580518770494423303870771)
  ·
    refine ⟨54870778155741634955806157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36580518770494423303870771 54870778155741634955806157)
    ·
      refine ⟨20576541808403113108427309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54870778155741634955806157 20576541808403113108427309)
      ·
        refine ⟨7716203178151167415660241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20576541808403113108427309 7716203178151167415660241)
        ·
          refine ⟨5787152383613375561745181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7716203178151167415660241 5787152383613375561745181)
          ·
            refine ⟨2170182143855015835654443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5787152383613375561745181 2170182143855015835654443)
            ·
              refine ⟨3255273215782523753481665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170182143855015835654443 3255273215782523753481665)
              ·
                refine ⟨2441454911836892815111249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255273215782523753481665 2441454911836892815111249)
                ·
                  refine ⟨1831091183877669611333437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2441454911836892815111249 1831091183877669611333437)
                  ·
                    refine ⟨686659193954126104250039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1831091183877669611333437 686659193954126104250039)
                    ·
                      rfl

theorem cell22_2005896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_2005896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005896 prefixEnd_2005896 := by exact prefixLift 2005896
  have htrace : WordTrace (prefixWord ++ tailWord_2005896) baseStart_2005896 baseEnd_2005896 := by
    simpa [prefixWord, tailWord_2005896, baseEnd_2005896] using wordTrace_append hprefix tailTrace_2005896
  have hstable : (prefixWord ++ tailWord_2005896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005896).length < 2 ^ (prefixWord ++ tailWord_2005896).sum := by decide
  have hdescent : baseEnd_2005896 < baseStart_2005896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005935 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 4, 5]
def baseStart_2005935 : Nat := 118140960795 + 2005935 * 2 ^ 59
def prefixEnd_2005935 : Nat := 4983230072969 + 3 ^ 40 * 2005935 * 2
def baseEnd_2005935 : Nat := 686672544451143002524919

theorem tailTrace_2005935 : CollatzResearch.WordTrace tailWord_2005935 prefixEnd_2005935 686672544451143002524919 := by
  unfold tailWord_2005935
  simp only [CollatzResearch.WordTrace]
  refine ⟨73162459987847556268411259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48774973325231704178940839 73162459987847556268411259)
  ·
    refine ⟨109743689981771334402616889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73162459987847556268411259 109743689981771334402616889)
    ·
      refine ⟨82307767486328500801962667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109743689981771334402616889 82307767486328500801962667)
      ·
        refine ⟨123461651229492751202944001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82307767486328500801962667 123461651229492751202944001)
        ·
          refine ⟨92596238422119563402208001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123461651229492751202944001 92596238422119563402208001)
          ·
            refine ⟨69447178816589672551656001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92596238422119563402208001 69447178816589672551656001)
            ·
              refine ⟨52085384112442254413742001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69447178816589672551656001 52085384112442254413742001)
              ·
                refine ⟨39064038084331690810306501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52085384112442254413742001 39064038084331690810306501)
                ·
                  refine ⟨7324507140812192026932469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39064038084331690810306501 7324507140812192026932469)
                  ·
                    refine ⟨686672544451143002524919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7324507140812192026932469 686672544451143002524919)
                    ·
                      rfl

theorem cell22_2005935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_2005935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2005935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2005935 prefixEnd_2005935 := by exact prefixLift 2005935
  have htrace : WordTrace (prefixWord ++ tailWord_2005935) baseStart_2005935 baseEnd_2005935 := by
    simpa [prefixWord, tailWord_2005935, baseEnd_2005935] using wordTrace_append hprefix tailTrace_2005935
  have hstable : (prefixWord ++ tailWord_2005935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005935).length < 2 ^ (prefixWord ++ tailWord_2005935).sum := by decide
  have hdescent : baseEnd_2005935 < baseStart_2005935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006001 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 1, 4]
def baseStart_2006001 : Nat := 118140960795 + 2006001 * 2 ^ 59
def prefixEnd_2006001 : Nat := 4983230072969 + 3 ^ 40 * 2006001 * 2
def baseEnd_2006001 : Nat := 686695137599940830374717

theorem tailTrace_2006001 : CollatzResearch.WordTrace tailWord_2006001 prefixEnd_2006001 686695137599940830374717 := by
  unfold tailWord_2006001
  simp only [CollatzResearch.WordTrace]
  refine ⟨73164867205608449540313857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48776578137072299693542571 73164867205608449540313857)
  ·
    refine ⟨54873650404206337155235393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73164867205608449540313857 54873650404206337155235393)
    ·
      refine ⟨41155237803154752866426545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54873650404206337155235393 41155237803154752866426545)
      ·
        refine ⟨30866428352366064649819909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41155237803154752866426545 30866428352366064649819909)
        ·
          refine ⟨5787455316068637121841233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30866428352366064649819909 5787455316068637121841233)
          ·
            refine ⟨4340591487051477841380925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5787455316068637121841233 4340591487051477841380925)
            ·
              refine ⟨1627721807644304190517847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4340591487051477841380925 1627721807644304190517847)
              ·
                refine ⟨2441582711466456285776771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627721807644304190517847 2441582711466456285776771)
                ·
                  refine ⟨3662374067199684428665157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441582711466456285776771 3662374067199684428665157)
                  ·
                    refine ⟨686695137599940830374717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3662374067199684428665157 686695137599940830374717)
                    ·
                      rfl

theorem cell22_2006001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_2006001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006001 prefixEnd_2006001 := by exact prefixLift 2006001
  have htrace : WordTrace (prefixWord ++ tailWord_2006001) baseStart_2006001 baseEnd_2006001 := by
    simpa [prefixWord, tailWord_2006001, baseEnd_2006001] using wordTrace_append hprefix tailTrace_2006001
  have hstable : (prefixWord ++ tailWord_2006001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006001).length < 2 ^ (prefixWord ++ tailWord_2006001).sum := by decide
  have hdescent : baseEnd_2006001 < baseStart_2006001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006027 : List Nat := [1, 1, 1, 1, 6, 2, 3, 7]
def baseStart_2006027 : Nat := 118140960795 + 2006027 * 2 ^ 59
def prefixEnd_2006027 : Nat := 4983230072969 + 3 ^ 40 * 2006027 * 2
def baseEnd_2006027 : Nat := 76300448659031714358293

theorem tailTrace_2006027 : CollatzResearch.WordTrace tailWord_2006027 prefixEnd_2006027 76300448659031714358293 := by
  unfold tailWord_2006027
  simp only [CollatzResearch.WordTrace]
  refine ⟨73165815503514255980760335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48777210335676170653840223 73165815503514255980760335)
  ·
    refine ⟨109748723255271383971140503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73165815503514255980760335 109748723255271383971140503)
    ·
      refine ⟨164623084882907075956710755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109748723255271383971140503 164623084882907075956710755)
      ·
        refine ⟨246934627324360613935066133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164623084882907075956710755 246934627324360613935066133)
        ·
          refine ⟨11575060655829403778206225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246934627324360613935066133 11575060655829403778206225)
          ·
            refine ⟨8681295491872052833654669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11575060655829403778206225 8681295491872052833654669)
            ·
              refine ⟨3255485809452019812620501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8681295491872052833654669 3255485809452019812620501)
              ·
                refine ⟨76300448659031714358293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3255485809452019812620501 76300448659031714358293)
                ·
                  rfl

theorem cell22_2006027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 7].length) (baseStart_2006027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006027 prefixEnd_2006027 := by exact prefixLift 2006027
  have htrace : WordTrace (prefixWord ++ tailWord_2006027) baseStart_2006027 baseEnd_2006027 := by
    simpa [prefixWord, tailWord_2006027, baseEnd_2006027] using wordTrace_append hprefix tailTrace_2006027
  have hstable : (prefixWord ++ tailWord_2006027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006027).length < 2 ^ (prefixWord ++ tailWord_2006027).sum := by decide
  have hdescent : baseEnd_2006027 < baseStart_2006027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006076 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_2006076 : Nat := 118140960795 + 2006076 * 2 ^ 59
def prefixEnd_2006076 : Nat := 4983230072969 + 3 ^ 40 * 2006076 * 2
def baseEnd_2006076 : Nat := 686720811632665634749487

theorem tailTrace_2006076 : CollatzResearch.WordTrace tailWord_2006076 prefixEnd_2006076 686720811632665634749487 := by
  unfold tailWord_2006076
  simp only [CollatzResearch.WordTrace]
  refine ⟨36583801340168368674647041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48778401786891158232862721 36583801340168368674647041)
  ·
    refine ⟨27437851005126276505985281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36583801340168368674647041 27437851005126276505985281)
    ·
      refine ⟨20578388253844707379488961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27437851005126276505985281 20578388253844707379488961)
      ·
        refine ⟨15433791190383530534616721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20578388253844707379488961 15433791190383530534616721)
        ·
          refine ⟨11575343392787647900962541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15433791190383530534616721 11575343392787647900962541)
          ·
            refine ⟨4340753772295367962860953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11575343392787647900962541 4340753772295367962860953)
            ·
              refine ⟨3255565329221525972145715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340753772295367962860953 3255565329221525972145715)
              ·
                refine ⟨4883347993832288958218573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255565329221525972145715 4883347993832288958218573)
                ·
                  refine ⟨1831255497687108359331965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4883347993832288958218573 1831255497687108359331965)
                  ·
                    refine ⟨686720811632665634749487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1831255497687108359331965 686720811632665634749487)
                    ·
                      rfl

theorem cell22_2006076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_2006076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006076 prefixEnd_2006076 := by exact prefixLift 2006076
  have htrace : WordTrace (prefixWord ++ tailWord_2006076) baseStart_2006076 baseEnd_2006076 := by
    simpa [prefixWord, tailWord_2006076, baseEnd_2006076] using wordTrace_append hprefix tailTrace_2006076
  have hstable : (prefixWord ++ tailWord_2006076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006076).length < 2 ^ (prefixWord ++ tailWord_2006076).sum := by decide
  have hdescent : baseEnd_2006076 < baseStart_2006076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006183 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2006183 : Nat := 118140960795 + 2006183 * 2 ^ 59
def prefixEnd_2006183 : Nat := 4983230072969 + 3 ^ 40 * 2006183 * 2
def baseEnd_2006183 : Nat := 686757439919353022324159

theorem tailTrace_2006183 : CollatzResearch.WordTrace tailWord_2006183 prefixEnd_2006183 686757439919353022324159 := by
  unfold tailWord_2006183
  simp only [CollatzResearch.WordTrace]
  refine ⟨73171505290949094623439203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48781003527299396415626135 73171505290949094623439203)
  ·
    refine ⟨109757257936423641935158805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73171505290949094623439203 109757257936423641935158805)
    ·
      refine ⟨5144871465769858215710569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109757257936423641935158805 5144871465769858215710569)
      ·
        refine ⟨3858653599327393661782927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5144871465769858215710569 3858653599327393661782927)
        ·
          refine ⟨5787980398991090492674391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858653599327393661782927 5787980398991090492674391)
          ·
            refine ⟨8681970598486635739011587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787980398991090492674391 8681970598486635739011587)
            ·
              refine ⟨13022955897729953608517381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681970598486635739011587 13022955897729953608517381)
              ·
                refine ⟨2441804230824366301597009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13022955897729953608517381 2441804230824366301597009)
                ·
                  refine ⟨1831353173118274726197757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2441804230824366301597009 1831353173118274726197757)
                  ·
                    refine ⟨686757439919353022324159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1831353173118274726197757 686757439919353022324159)
                    ·
                      rfl

theorem cell22_2006183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2006183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006183 prefixEnd_2006183 := by exact prefixLift 2006183
  have htrace : WordTrace (prefixWord ++ tailWord_2006183) baseStart_2006183 baseEnd_2006183 := by
    simpa [prefixWord, tailWord_2006183, baseEnd_2006183] using wordTrace_append hprefix tailTrace_2006183
  have hstable : (prefixWord ++ tailWord_2006183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006183).length < 2 ^ (prefixWord ++ tailWord_2006183).sum := by decide
  have hdescent : baseEnd_2006183 < baseStart_2006183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006239 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 2, 5]
def baseStart_2006239 : Nat := 118140960795 + 2006239 * 2 ^ 59
def prefixEnd_2006239 : Nat := 4983230072969 + 3 ^ 40 * 2006239 * 2
def baseEnd_2006239 : Nat := 686776609863787542923987

theorem tailTrace_2006239 : CollatzResearch.WordTrace tailWord_2006239 prefixEnd_2006239 686776609863787542923987 := by
  unfold tailWord_2006239
  simp only [CollatzResearch.WordTrace]
  refine ⟨73173547778746216187477771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48782365185830810791651847 73173547778746216187477771)
  ·
    refine ⟨109760321668119324281216657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73173547778746216187477771 109760321668119324281216657)
    ·
      refine ⟨82320241251089493210912493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109760321668119324281216657 82320241251089493210912493)
      ·
        refine ⟨30870090469158559954092185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82320241251089493210912493 30870090469158559954092185)
        ·
          refine ⟨23152567851868919965569139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30870090469158559954092185 23152567851868919965569139)
          ·
            refine ⟨34728851777803379948353709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23152567851868919965569139 34728851777803379948353709)
            ·
              refine ⟨13023319416676267480632641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34728851777803379948353709 13023319416676267480632641)
              ·
                refine ⟨9767489562507200610474481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13023319416676267480632641 9767489562507200610474481)
                ·
                  refine ⟨7325617171880400457855861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9767489562507200610474481 7325617171880400457855861)
                  ·
                    refine ⟨686776609863787542923987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7325617171880400457855861 686776609863787542923987)
                    ·
                      rfl

theorem cell22_2006239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_2006239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006239 prefixEnd_2006239 := by exact prefixLift 2006239
  have htrace : WordTrace (prefixWord ++ tailWord_2006239) baseStart_2006239 baseEnd_2006239 := by
    simpa [prefixWord, tailWord_2006239, baseEnd_2006239] using wordTrace_append hprefix tailTrace_2006239
  have hstable : (prefixWord ++ tailWord_2006239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006239).length < 2 ^ (prefixWord ++ tailWord_2006239).sum := by decide
  have hdescent : baseEnd_2006239 < baseStart_2006239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006241 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 5]
def baseStart_2006241 : Nat := 118140960795 + 2006241 * 2 ^ 59
def prefixEnd_2006241 : Nat := 4983230072969 + 3 ^ 40 * 2006241 * 2
def baseEnd_2006241 : Nat := 228925764834886734791327

theorem tailTrace_2006241 : CollatzResearch.WordTrace tailWord_2006241 prefixEnd_2006241 228925764834886734791327 := by
  unfold tailWord_2006241
  simp only [CollatzResearch.WordTrace]
  refine ⟨73173620724738970529050577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48782413816492647019367051 73173620724738970529050577)
  ·
    refine ⟨54880215543554227896787933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73173620724738970529050577 54880215543554227896787933)
    ·
      refine ⟨20580080828832835461295475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54880215543554227896787933 20580080828832835461295475)
      ·
        refine ⟨30870121243249253191943213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20580080828832835461295475 30870121243249253191943213)
        ·
          refine ⟨11576295466218469946978705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30870121243249253191943213 11576295466218469946978705)
          ·
            refine ⟨8682221599663852460234029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11576295466218469946978705 8682221599663852460234029)
            ·
              refine ⟨3255833099873944672587761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8682221599663852460234029 3255833099873944672587761)
              ·
                refine ⟨2441874824905458504440821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255833099873944672587761 2441874824905458504440821)
                ·
                  refine ⟨228925764834886734791327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2441874824905458504440821 228925764834886734791327)
                  ·
                    rfl

theorem cell22_2006241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_2006241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006241 prefixEnd_2006241 := by exact prefixLift 2006241
  have htrace : WordTrace (prefixWord ++ tailWord_2006241) baseStart_2006241 baseEnd_2006241 := by
    simpa [prefixWord, tailWord_2006241, baseEnd_2006241] using wordTrace_append hprefix tailTrace_2006241
  have hstable : (prefixWord ++ tailWord_2006241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006241).length < 2 ^ (prefixWord ++ tailWord_2006241).sum := by decide
  have hdescent : baseEnd_2006241 < baseStart_2006241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006271 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 1, 4]
def baseStart_2006271 : Nat := 118140960795 + 2006271 * 2 ^ 59
def prefixEnd_2006271 : Nat := 4983230072969 + 3 ^ 40 * 2006271 * 2
def baseEnd_2006271 : Nat := 686787564117750126123889

theorem tailTrace_2006271 : CollatzResearch.WordTrace tailWord_2006271 prefixEnd_2006271 686787564117750126123889 := by
  unfold tailWord_2006271
  simp only [CollatzResearch.WordTrace]
  refine ⟨73174714914630285652642667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48783143276420190435095111 73174714914630285652642667)
  ·
    refine ⟨109762072371945428478964001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73174714914630285652642667 109762072371945428478964001)
    ·
      refine ⟨82321554278959071359223001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109762072371945428478964001 82321554278959071359223001)
      ·
        refine ⟨61741165709219303519417251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82321554278959071359223001 61741165709219303519417251)
        ·
          refine ⟨92611748563828955279125877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61741165709219303519417251 92611748563828955279125877)
          ·
            refine ⟨8682351427858964557418051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92611748563828955279125877 8682351427858964557418051)
            ·
              refine ⟨13023527141788446836127077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682351427858964557418051 13023527141788446836127077)
              ·
                refine ⟨2441911339085333781773827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13023527141788446836127077 2441911339085333781773827)
                ·
                  refine ⟨3662867008628000672660741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441911339085333781773827 3662867008628000672660741)
                  ·
                    refine ⟨686787564117750126123889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3662867008628000672660741 686787564117750126123889)
                    ·
                      rfl

theorem cell22_2006271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_2006271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2006271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2006271 prefixEnd_2006271 := by exact prefixLift 2006271
  have htrace : WordTrace (prefixWord ++ tailWord_2006271) baseStart_2006271 baseEnd_2006271 := by
    simpa [prefixWord, tailWord_2006271, baseEnd_2006271] using wordTrace_append hprefix tailTrace_2006271
  have hstable : (prefixWord ++ tailWord_2006271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006271).length < 2 ^ (prefixWord ++ tailWord_2006271).sum := by decide
  have hdescent : baseEnd_2006271 < baseStart_2006271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
