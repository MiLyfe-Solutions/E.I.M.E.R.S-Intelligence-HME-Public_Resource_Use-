import V185TrunkScan23Chunk0142

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_845255 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_845255 : Nat := 118140960795 + 845255 * 2 ^ 59
def prefixEnd_845255 : Nat := 4983230072969 + 3 ^ 40 * 845255 * 2
def baseEnd_845255 : Nat := 434022090616195669625249

theorem tailTrace_845255 : CollatzResearch.WordTrace tailWord_845255 prefixEnd_845255 434022090616195669625249 := by
  unfold tailWord_845255
  simp only [CollatzResearch.WordTrace]
  refine ⟨30828982552792967906177219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20552655035195311937451479 30828982552792967906177219)
  ·
    refine ⟨46243473829189451859265829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30828982552792967906177219 46243473829189451859265829)
    ·
      refine ⟨8670651342973022223612343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46243473829189451859265829 8670651342973022223612343)
      ·
        refine ⟨13005977014459533335418515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670651342973022223612343 13005977014459533335418515)
        ·
          refine ⟨19508965521689300003127773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005977014459533335418515 19508965521689300003127773)
          ·
            refine ⟨7315862070633487501172915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19508965521689300003127773 7315862070633487501172915)
            ·
              refine ⟨10973793105950231251759373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315862070633487501172915 10973793105950231251759373)
              ·
                refine ⟨4115172414731336719409765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10973793105950231251759373 4115172414731336719409765)
                ·
                  refine ⟨771594827762125634889331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4115172414731336719409765 771594827762125634889331)
                  ·
                    refine ⟨1157392241643188452333997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 771594827762125634889331 1157392241643188452333997)
                    ·
                      refine ⟨434022090616195669625249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157392241643188452333997 434022090616195669625249)
                      ·
                        rfl

theorem cell23_845255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_845255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845255 prefixEnd_845255 := by exact prefixLift 845255
  have htrace : WordTrace (prefixWord ++ tailWord_845255) baseStart_845255 baseEnd_845255 := by
    simpa [prefixWord, tailWord_845255, baseEnd_845255] using wordTrace_append hprefix tailTrace_845255
  have hstable : (prefixWord ++ tailWord_845255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845255).length < 2 ^ (prefixWord ++ tailWord_845255).sum := by decide
  have hdescent : baseEnd_845255 < baseStart_845255 := by decide
  rcases family_descends (prefixWord ++ tailWord_845255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845256 : List Nat := [2, 1, 3, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_845256 : Nat := 118140960795 + 845256 * 2 ^ 59
def prefixEnd_845256 : Nat := 4983230072969 + 3 ^ 40 * 845256 * 2
def baseEnd_845256 : Nat := 434022604096850165712745

theorem tailTrace_845256 : CollatzResearch.WordTrace tailWord_845256 prefixEnd_845256 434022604096850165712745 := by
  unfold tailWord_845256
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414509512894672538481811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20552679350526230051309081 15414509512894672538481811)
  ·
    refine ⟨23121764269342008807722717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15414509512894672538481811 23121764269342008807722717)
    ·
      refine ⟨8670661601003253302896019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23121764269342008807722717 8670661601003253302896019)
      ·
        refine ⟨13005992401504879954344029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670661601003253302896019 13005992401504879954344029)
        ·
          refine ⟨4877247150564329982879011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13005992401504879954344029 4877247150564329982879011)
          ·
            refine ⟨7315870725846494974318517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877247150564329982879011 7315870725846494974318517)
            ·
              refine ⟨685862880548108903842361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7315870725846494974318517 685862880548108903842361)
              ·
                refine ⟨514397160411081677881771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685862880548108903842361 514397160411081677881771)
                ·
                  refine ⟨771595740616622516822657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514397160411081677881771 771595740616622516822657)
                  ·
                    refine ⟨578696805462466887616993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 771595740616622516822657 578696805462466887616993)
                    ·
                      refine ⟨434022604096850165712745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578696805462466887616993 434022604096850165712745)
                      ·
                        rfl

theorem cell23_845256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_845256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845256 prefixEnd_845256 := by exact prefixLift 845256
  have htrace : WordTrace (prefixWord ++ tailWord_845256) baseStart_845256 baseEnd_845256 := by
    simpa [prefixWord, tailWord_845256, baseEnd_845256] using wordTrace_append hprefix tailTrace_845256
  have hstable : (prefixWord ++ tailWord_845256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845256).length < 2 ^ (prefixWord ++ tailWord_845256).sum := by decide
  have hdescent : baseEnd_845256 < baseStart_845256 := by decide
  rcases family_descends (prefixWord ++ tailWord_845256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845295 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 3, 4, 2]
def baseStart_845295 : Nat := 118140960795 + 845295 * 2 ^ 59
def prefixEnd_845295 : Nat := 4983230072969 + 3 ^ 40 * 845295 * 2
def baseEnd_845295 : Nat := 434042629842375513125065

theorem tailTrace_845295 : CollatzResearch.WordTrace tailWord_845295 prefixEnd_845295 434042629842375513125065 := by
  unfold tailWord_845295
  simp only [CollatzResearch.WordTrace]
  refine ⟨30830441472648054737633339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20553627648432036491755559 30830441472648054737633339)
  ·
    refine ⟨46245662208972082106450009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30830441472648054737633339 46245662208972082106450009)
    ·
      refine ⟨34684246656729061579837507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46245662208972082106450009 34684246656729061579837507)
      ·
        refine ⟨52026369985093592369756261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34684246656729061579837507 52026369985093592369756261)
        ·
          refine ⟨9754944372205048569329299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52026369985093592369756261 9754944372205048569329299)
          ·
            refine ⟨14632416558307572853993949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754944372205048569329299 14632416558307572853993949)
            ·
              refine ⟨5487156209365339820247731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14632416558307572853993949 5487156209365339820247731)
              ·
                refine ⟨8230734314048009730371597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487156209365339820247731 8230734314048009730371597)
                ·
                  refine ⟨3086525367768003648889349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8230734314048009730371597 3086525367768003648889349)
                  ·
                    refine ⟨578723506456500684166753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3086525367768003648889349 578723506456500684166753)
                    ·
                      refine ⟨434042629842375513125065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578723506456500684166753 434042629842375513125065)
                      ·
                        rfl

theorem cell23_845295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 4, 2].length) (baseStart_845295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845295 prefixEnd_845295 := by exact prefixLift 845295
  have htrace : WordTrace (prefixWord ++ tailWord_845295) baseStart_845295 baseEnd_845295 := by
    simpa [prefixWord, tailWord_845295, baseEnd_845295] using wordTrace_append hprefix tailTrace_845295
  have hstable : (prefixWord ++ tailWord_845295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845295).length < 2 ^ (prefixWord ++ tailWord_845295).sum := by decide
  have hdescent : baseEnd_845295 < baseStart_845295 := by decide
  rcases family_descends (prefixWord ++ tailWord_845295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845429 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_845429 : Nat := 118140960795 + 845429 * 2 ^ 59
def prefixEnd_845429 : Nat := 4983230072969 + 3 ^ 40 * 845429 * 2
def baseEnd_845429 : Nat := 144703812083359329616483

theorem tailTrace_845429 : CollatzResearch.WordTrace tailWord_845429 prefixEnd_845429 144703812083359329616483 := by
  unfold tailWord_845429
  simp only [CollatzResearch.WordTrace]
  refine ⟨30835328854162595623011341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20556885902775063748674227 30835328854162595623011341)
  ·
    refine ⟨11563248320310973358629253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30835328854162595623011341 11563248320310973358629253)
    ·
      refine ⟨2168109060058307504742985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11563248320310973358629253 2168109060058307504742985)
      ·
        refine ⟨1626081795043730628557239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2168109060058307504742985 1626081795043730628557239)
        ·
          refine ⟨2439122692565595942835859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626081795043730628557239 2439122692565595942835859)
          ·
            refine ⟨3658684038848393914253789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439122692565595942835859 3658684038848393914253789)
            ·
              refine ⟨1372006514568147717845171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3658684038848393914253789 1372006514568147717845171)
              ·
                refine ⟨2058009771852221576767757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372006514568147717845171 2058009771852221576767757)
                ·
                  refine ⟨771753664444583091287909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2058009771852221576767757 771753664444583091287909)
                  ·
                    refine ⟨144703812083359329616483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771753664444583091287909 144703812083359329616483)
                    ·
                      rfl

theorem cell23_845429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_845429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845429 prefixEnd_845429 := by exact prefixLift 845429
  have htrace : WordTrace (prefixWord ++ tailWord_845429) baseStart_845429 baseEnd_845429 := by
    simpa [prefixWord, tailWord_845429, baseEnd_845429] using wordTrace_append hprefix tailTrace_845429
  have hstable : (prefixWord ++ tailWord_845429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845429).length < 2 ^ (prefixWord ++ tailWord_845429).sum := by decide
  have hdescent : baseEnd_845429 < baseStart_845429 := by decide
  rcases family_descends (prefixWord ++ tailWord_845429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845452 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_845452 : Nat := 118140960795 + 845452 * 2 ^ 59
def prefixEnd_845452 : Nat := 4983230072969 + 3 ^ 40 * 845452 * 2
def baseEnd_845452 : Nat := 434123246305131398861843

theorem tailTrace_845452 : CollatzResearch.WordTrace tailWord_845452 prefixEnd_845452 434123246305131398861843 := by
  unfold tailWord_845452
  simp only [CollatzResearch.WordTrace]
  refine ⟨15418083866539635275549305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20557445155386180367399073 15418083866539635275549305)
  ·
    refine ⟨11563562899904726456661979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15418083866539635275549305 11563562899904726456661979)
    ·
      refine ⟨17345344349857089684992969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11563562899904726456661979 17345344349857089684992969)
      ·
        refine ⟨13009008262392817263744727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17345344349857089684992969 13009008262392817263744727)
        ·
          refine ⟨19513512393589225895617091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13009008262392817263744727 19513512393589225895617091)
          ·
            refine ⟨29270268590383838843425637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19513512393589225895617091 29270268590383838843425637)
            ·
              refine ⟨5488175360696969783142307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29270268590383838843425637 5488175360696969783142307)
              ·
                refine ⟨8232263041045454674713461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488175360696969783142307 8232263041045454674713461)
                ·
                  refine ⟨771774660098011375754387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8232263041045454674713461 771774660098011375754387)
                  ·
                    refine ⟨1157661990147017063631581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 771774660098011375754387 1157661990147017063631581)
                    ·
                      refine ⟨434123246305131398861843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157661990147017063631581 434123246305131398861843)
                      ·
                        rfl

theorem cell23_845452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_845452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845452 prefixEnd_845452 := by exact prefixLift 845452
  have htrace : WordTrace (prefixWord ++ tailWord_845452) baseStart_845452 baseEnd_845452 := by
    simpa [prefixWord, tailWord_845452, baseEnd_845452] using wordTrace_append hprefix tailTrace_845452
  have hstable : (prefixWord ++ tailWord_845452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845452).length < 2 ^ (prefixWord ++ tailWord_845452).sum := by decide
  have hdescent : baseEnd_845452 < baseStart_845452 := by decide
  rcases family_descends (prefixWord ++ tailWord_845452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845480 : List Nat := [2, 1, 7, 1, 1, 1, 1, 4, 1, 4]
def baseStart_845480 : Nat := 118140960795 + 845480 * 2 ^ 59
def prefixEnd_845480 : Nat := 4983230072969 + 3 ^ 40 * 845480 * 2
def baseEnd_845480 : Nat := 144712541254485763103905

theorem tailTrace_845480 : CollatzResearch.WordTrace tailWord_845480 prefixEnd_845480 144712541254485763103905 := by
  unfold tailWord_845480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15418594488488915666558947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20558125984651887555411929 15418594488488915666558947)
  ·
    refine ⟨23127891732733373499838421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15418594488488915666558947 23127891732733373499838421)
    ·
      refine ⟨542059962485938441402463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23127891732733373499838421 542059962485938441402463)
      ·
        refine ⟨813089943728907662103695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542059962485938441402463 813089943728907662103695)
        ·
          refine ⟨1219634915593361493155543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813089943728907662103695 1219634915593361493155543)
          ·
            refine ⟨1829452373390042239733315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219634915593361493155543 1829452373390042239733315)
            ·
              refine ⟨2744178560085063359599973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829452373390042239733315 2744178560085063359599973)
              ·
                refine ⟨514533480015949379924995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2744178560085063359599973 514533480015949379924995)
                ·
                  refine ⟨771800220023924069887493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514533480015949379924995 771800220023924069887493)
                  ·
                    refine ⟨144712541254485763103905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771800220023924069887493 144712541254485763103905)
                    ·
                      rfl

theorem cell23_845480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_845480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845480 prefixEnd_845480 := by exact prefixLift 845480
  have htrace : WordTrace (prefixWord ++ tailWord_845480) baseStart_845480 baseEnd_845480 := by
    simpa [prefixWord, tailWord_845480, baseEnd_845480] using wordTrace_append hprefix tailTrace_845480
  have hstable : (prefixWord ++ tailWord_845480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845480).length < 2 ^ (prefixWord ++ tailWord_845480).sum := by decide
  have hdescent : baseEnd_845480 < baseStart_845480 := by decide
  rcases family_descends (prefixWord ++ tailWord_845480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845502 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_845502 : Nat := 118140960795 + 845502 * 2 ^ 59
def prefixEnd_845502 : Nat := 4983230072969 + 3 ^ 40 * 845502 * 2
def baseEnd_845502 : Nat := 144716306779285401078871

theorem tailTrace_845502 : CollatzResearch.WordTrace tailWord_845502 prefixEnd_845502 144716306779285401078871 := by
  unfold tailWord_845502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854748922862266136302345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20558660921932086060279173 3854748922862266136302345)
  ·
    refine ⟨2891061692146699602226759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3854748922862266136302345 2891061692146699602226759)
    ·
      refine ⟨4336592538220049403340139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2891061692146699602226759 4336592538220049403340139)
      ·
        refine ⟨6504888807330074105010209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4336592538220049403340139 6504888807330074105010209)
        ·
          refine ⟨4878666605497555578757657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6504888807330074105010209 4878666605497555578757657)
          ·
            refine ⟨3658999954123166684068243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4878666605497555578757657 3658999954123166684068243)
            ·
              refine ⟨5488499931184750026102365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658999954123166684068243 5488499931184750026102365)
              ·
                refine ⟨2058187474194281259788387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488499931184750026102365 2058187474194281259788387)
                ·
                  refine ⟨3087281211291421889682581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058187474194281259788387 3087281211291421889682581)
                  ·
                    refine ⟨144716306779285401078871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3087281211291421889682581 144716306779285401078871)
                    ·
                      rfl

theorem cell23_845502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_845502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845502 prefixEnd_845502 := by exact prefixLift 845502
  have htrace : WordTrace (prefixWord ++ tailWord_845502) baseStart_845502 baseEnd_845502 := by
    simpa [prefixWord, tailWord_845502, baseEnd_845502] using wordTrace_append hprefix tailTrace_845502
  have hstable : (prefixWord ++ tailWord_845502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845502).length < 2 ^ (prefixWord ++ tailWord_845502).sum := by decide
  have hdescent : baseEnd_845502 < baseStart_845502 := by decide
  rcases family_descends (prefixWord ++ tailWord_845502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845509 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 3, 2, 2]
def baseStart_845509 : Nat := 118140960795 + 845509 * 2 ^ 59
def prefixEnd_845509 : Nat := 4983230072969 + 3 ^ 40 * 845509 * 2
def baseEnd_845509 : Nat := 434152514702437675849081

theorem tailTrace_845509 : CollatzResearch.WordTrace tailWord_845509 prefixEnd_845509 434152514702437675849081 := by
  unfold tailWord_845509
  simp only [CollatzResearch.WordTrace]
  refine ⟨30838246693872769285923581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20558831129248512857282387 30838246693872769285923581)
  ·
    refine ⟨11564342510202288482221343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30838246693872769285923581 11564342510202288482221343)
    ·
      refine ⟨17346513765303432723332015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11564342510202288482221343 17346513765303432723332015)
      ·
        refine ⟨26019770647955149084998023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17346513765303432723332015 26019770647955149084998023)
        ·
          refine ⟨39029655971932723627497035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26019770647955149084998023 39029655971932723627497035)
          ·
            refine ⟨58544483957899085441245553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39029655971932723627497035 58544483957899085441245553)
            ·
              refine ⟨43908362968424314080934165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58544483957899085441245553 43908362968424314080934165)
              ·
                refine ⟨2058204514144889722543789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43908362968424314080934165 2058204514144889722543789)
                ·
                  refine ⟨771826692804333645953921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2058204514144889722543789 771826692804333645953921)
                  ·
                    refine ⟨578870019603250234465441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 771826692804333645953921 578870019603250234465441)
                    ·
                      refine ⟨434152514702437675849081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578870019603250234465441 434152514702437675849081)
                      ·
                        rfl

theorem cell23_845509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_845509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845509 prefixEnd_845509 := by exact prefixLift 845509
  have htrace : WordTrace (prefixWord ++ tailWord_845509) baseStart_845509 baseEnd_845509 := by
    simpa [prefixWord, tailWord_845509, baseEnd_845509] using wordTrace_append hprefix tailTrace_845509
  have hstable : (prefixWord ++ tailWord_845509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845509).length < 2 ^ (prefixWord ++ tailWord_845509).sum := by decide
  have hdescent : baseEnd_845509 < baseStart_845509 := by decide
  rcases family_descends (prefixWord ++ tailWord_845509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845512 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_845512 : Nat := 118140960795 + 845512 * 2 ^ 59
def prefixEnd_845512 : Nat := 4983230072969 + 3 ^ 40 * 845512 * 2
def baseEnd_845512 : Nat := 434154055144401164111567

theorem tailTrace_845512 : CollatzResearch.WordTrace tailWord_845512 prefixEnd_845512 434154055144401164111567 := by
  unfold tailWord_845512
  simp only [CollatzResearch.WordTrace]
  refine ⟨15419178056430950399141395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20558904075241267198855193 15419178056430950399141395)
  ·
    refine ⟨23128767084646425598712093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15419178056430950399141395 23128767084646425598712093)
    ·
      refine ⟨8673287656742409599517035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23128767084646425598712093 8673287656742409599517035)
      ·
        refine ⟨13009931485113614399275553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673287656742409599517035 13009931485113614399275553)
        ·
          refine ⟨9757448613835210799456665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13009931485113614399275553 9757448613835210799456665)
          ·
            refine ⟨7318086460376408099592499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9757448613835210799456665 7318086460376408099592499)
            ·
              refine ⟨10977129690564612149388749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7318086460376408099592499 10977129690564612149388749)
              ·
                refine ⟨4116423633961729556020781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10977129690564612149388749 4116423633961729556020781)
                ·
                  refine ⟨1543658862735648583507793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4116423633961729556020781 1543658862735648583507793)
                  ·
                    refine ⟨1157744147051736437630845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1543658862735648583507793 1157744147051736437630845)
                    ·
                      refine ⟨434154055144401164111567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157744147051736437630845 434154055144401164111567)
                      ·
                        rfl

theorem cell23_845512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_845512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845512 prefixEnd_845512 := by exact prefixLift 845512
  have htrace : WordTrace (prefixWord ++ tailWord_845512) baseStart_845512 baseEnd_845512 := by
    simpa [prefixWord, tailWord_845512, baseEnd_845512] using wordTrace_append hprefix tailTrace_845512
  have hstable : (prefixWord ++ tailWord_845512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845512).length < 2 ^ (prefixWord ++ tailWord_845512).sum := by decide
  have hdescent : baseEnd_845512 < baseStart_845512 := by decide
  rcases family_descends (prefixWord ++ tailWord_845512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845529 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 3]
def baseStart_845529 : Nat := 118140960795 + 845529 * 2 ^ 59
def prefixEnd_845529 : Nat := 4983230072969 + 3 ^ 40 * 845529 * 2
def baseEnd_845529 : Nat := 434162784315527597598989

theorem tailTrace_845529 : CollatzResearch.WordTrace tailWord_845529 prefixEnd_845529 434162784315527597598989 := by
  unfold tailWord_845529
  simp only [CollatzResearch.WordTrace]
  refine ⟨30838976153800312701651641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20559317435866875134434427 30838976153800312701651641)
  ·
    refine ⟨23129232115350234526238731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30838976153800312701651641 23129232115350234526238731)
    ·
      refine ⟨34693848173025351789358097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23129232115350234526238731 34693848173025351789358097)
      ·
        refine ⟨26020386129769013842018573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34693848173025351789358097 26020386129769013842018573)
        ·
          refine ⟨9757644798663380190756965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26020386129769013842018573 9757644798663380190756965)
          ·
            refine ⟨1829558399749383785766931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9757644798663380190756965 1829558399749383785766931)
            ·
              refine ⟨2744337599624075678650397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829558399749383785766931 2744337599624075678650397)
              ·
                refine ⟨1029126599859028379493899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2744337599624075678650397 1029126599859028379493899)
                ·
                  refine ⟨1543689899788542569240849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029126599859028379493899 1543689899788542569240849)
                  ·
                    refine ⟨1157767424841406926930637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1543689899788542569240849 1157767424841406926930637)
                    ·
                      refine ⟨434162784315527597598989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157767424841406926930637 434162784315527597598989)
                      ·
                        rfl

theorem cell23_845529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_845529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845529 prefixEnd_845529 := by exact prefixLift 845529
  have htrace : WordTrace (prefixWord ++ tailWord_845529) baseStart_845529 baseEnd_845529 := by
    simpa [prefixWord, tailWord_845529, baseEnd_845529] using wordTrace_append hprefix tailTrace_845529
  have hstable : (prefixWord ++ tailWord_845529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845529).length < 2 ^ (prefixWord ++ tailWord_845529).sum := by decide
  have hdescent : baseEnd_845529 < baseStart_845529 := by decide
  rcases family_descends (prefixWord ++ tailWord_845529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845552 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 2, 7, 2]
def baseStart_845552 : Nat := 118140960795 + 845552 * 2 ^ 59
def prefixEnd_845552 : Nat := 4983230072969 + 3 ^ 40 * 845552 * 2
def baseEnd_845552 : Nat := 434174594370581007611383

theorem tailTrace_845552 : CollatzResearch.WordTrace tailWord_845552 prefixEnd_845552 434174594370581007611383 := by
  unfold tailWord_845552
  simp only [CollatzResearch.WordTrace]
  refine ⟨15419907516358493814869455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20559876688477991753159273 15419907516358493814869455)
  ·
    refine ⟨23129861274537740722304183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15419907516358493814869455 23129861274537740722304183)
    ·
      refine ⟨34694791911806611083456275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23129861274537740722304183 34694791911806611083456275)
      ·
        refine ⟨52042187867709916625184413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34694791911806611083456275 52042187867709916625184413)
        ·
          refine ⟨19515820450391218734444155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52042187867709916625184413 19515820450391218734444155)
          ·
            refine ⟨29273730675586828101666233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19515820450391218734444155 29273730675586828101666233)
            ·
              refine ⟨21955298006690121076249675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29273730675586828101666233 21955298006690121076249675)
              ·
                refine ⟨32932947010035181614374513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21955298006690121076249675 32932947010035181614374513)
                ·
                  refine ⟨24699710257526386210780885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32932947010035181614374513 24699710257526386210780885)
                  ·
                    refine ⟨578899459160774676815177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24699710257526386210780885 578899459160774676815177)
                    ·
                      refine ⟨434174594370581007611383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578899459160774676815177 434174594370581007611383)
                      ·
                        rfl

theorem cell23_845552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 7, 2].length) (baseStart_845552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845552 prefixEnd_845552 := by exact prefixLift 845552
  have htrace : WordTrace (prefixWord ++ tailWord_845552) baseStart_845552 baseEnd_845552 := by
    simpa [prefixWord, tailWord_845552, baseEnd_845552] using wordTrace_append hprefix tailTrace_845552
  have hstable : (prefixWord ++ tailWord_845552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845552).length < 2 ^ (prefixWord ++ tailWord_845552).sum := by decide
  have hdescent : baseEnd_845552 < baseStart_845552 := by decide
  rcases family_descends (prefixWord ++ tailWord_845552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845556 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_845556 : Nat := 118140960795 + 845556 * 2 ^ 59
def prefixEnd_845556 : Nat := 4983230072969 + 3 ^ 40 * 845556 * 2
def baseEnd_845556 : Nat := 434176648293198991961365

theorem tailTrace_845556 : CollatzResearch.WordTrace tailWord_845556 prefixEnd_845556 434176648293198991961365 := by
  unfold tailWord_845556
  simp only [CollatzResearch.WordTrace]
  refine ⟨15419980462351248156442261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20559973949801664208589681 15419980462351248156442261)
  ·
    refine ⟨722811584172714757333231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15419980462351248156442261 722811584172714757333231)
    ·
      refine ⟨1084217376259072135999847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722811584172714757333231 1084217376259072135999847)
      ·
        refine ⟨1626326064388608203999771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084217376259072135999847 1626326064388608203999771)
        ·
          refine ⟨2439489096582912305999657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626326064388608203999771 2439489096582912305999657)
          ·
            refine ⟨1829616822437184229499743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439489096582912305999657 1829616822437184229499743)
            ·
              refine ⟨2744425233655776344249615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829616822437184229499743 2744425233655776344249615)
              ·
                refine ⟨4116637850483664516374423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744425233655776344249615 4116637850483664516374423)
                ·
                  refine ⟨6174956775725496774561635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116637850483664516374423 6174956775725496774561635)
                  ·
                    refine ⟨9262435163588245161842453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174956775725496774561635 9262435163588245161842453)
                    ·
                      refine ⟨434176648293198991961365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9262435163588245161842453 434176648293198991961365)
                      ·
                        rfl

theorem cell23_845556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_845556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845556 prefixEnd_845556 := by exact prefixLift 845556
  have htrace : WordTrace (prefixWord ++ tailWord_845556) baseStart_845556 baseEnd_845556 := by
    simpa [prefixWord, tailWord_845556, baseEnd_845556] using wordTrace_append hprefix tailTrace_845556
  have hstable : (prefixWord ++ tailWord_845556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845556).length < 2 ^ (prefixWord ++ tailWord_845556).sum := by decide
  have hdescent : baseEnd_845556 < baseStart_845556 := by decide
  rcases family_descends (prefixWord ++ tailWord_845556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845559 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_845559 : Nat := 118140960795 + 845559 * 2 ^ 59
def prefixEnd_845559 : Nat := 4983230072969 + 3 ^ 40 * 845559 * 2
def baseEnd_845559 : Nat := 434178188735162480223851

theorem tailTrace_845559 : CollatzResearch.WordTrace tailWord_845559 prefixEnd_845559 434178188735162480223851 := by
  unfold tailWord_845559
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840070343691627825243731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20560046895794418550162487 30840070343691627825243731)
  ·
    refine ⟨46260105515537441737865597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30840070343691627825243731 46260105515537441737865597)
    ·
      refine ⟨17347539568326540651699599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46260105515537441737865597 17347539568326540651699599)
      ·
        refine ⟨26021309352489810977549399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17347539568326540651699599 26021309352489810977549399)
        ·
          refine ⟨39031964028734716466324099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26021309352489810977549399 39031964028734716466324099)
          ·
            refine ⟨58547946043102074699486149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39031964028734716466324099 58547946043102074699486149)
            ·
              refine ⟨10977739883081639006153653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58547946043102074699486149 10977739883081639006153653)
              ·
                refine ⟨1029163114038903656826905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10977739883081639006153653 1029163114038903656826905)
                ·
                  refine ⟨771872335529177742620179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029163114038903656826905 771872335529177742620179)
                  ·
                    refine ⟨1157808503293766613930269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 771872335529177742620179 1157808503293766613930269)
                    ·
                      refine ⟨434178188735162480223851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157808503293766613930269 434178188735162480223851)
                      ·
                        rfl

theorem cell23_845559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_845559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845559 prefixEnd_845559 := by exact prefixLift 845559
  have htrace : WordTrace (prefixWord ++ tailWord_845559) baseStart_845559 baseEnd_845559 := by
    simpa [prefixWord, tailWord_845559, baseEnd_845559] using wordTrace_append hprefix tailTrace_845559
  have hstable : (prefixWord ++ tailWord_845559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845559).length < 2 ^ (prefixWord ++ tailWord_845559).sum := by decide
  have hdescent : baseEnd_845559 < baseStart_845559 := by decide
  rcases family_descends (prefixWord ++ tailWord_845559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845565 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_845565 : Nat := 118140960795 + 845565 * 2 ^ 59
def prefixEnd_845565 : Nat := 4983230072969 + 3 ^ 40 * 845565 * 2
def baseEnd_845565 : Nat := 434181269619089456748823

theorem tailTrace_845565 : CollatzResearch.WordTrace tailWord_845565 prefixEnd_845565 434181269619089456748823 := by
  unfold tailWord_845565
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840289181669890849962149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20560192787779927233308099 30840289181669890849962149)
  ·
    refine ⟨5782554221563104534367903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30840289181669890849962149 5782554221563104534367903)
    ·
      refine ⟨8673831332344656801551855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782554221563104534367903 8673831332344656801551855)
      ·
        refine ⟨13010746998516985202327783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673831332344656801551855 13010746998516985202327783)
        ·
          refine ⟨19516120497775477803491675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13010746998516985202327783 19516120497775477803491675)
          ·
            refine ⟨29274180746663216705237513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19516120497775477803491675 29274180746663216705237513)
            ·
              refine ⟨21955635559997412528928135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29274180746663216705237513 21955635559997412528928135)
              ·
                refine ⟨32933453339996118793392203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21955635559997412528928135 32933453339996118793392203)
                ·
                  refine ⟨49400180009994178190088305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32933453339996118793392203 49400180009994178190088305)
                  ·
                    refine ⟨37050135007495633642566229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49400180009994178190088305 37050135007495633642566229)
                    ·
                      refine ⟨434181269619089456748823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 37050135007495633642566229 434181269619089456748823)
                      ·
                        rfl

theorem cell23_845565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_845565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845565 prefixEnd_845565 := by exact prefixLift 845565
  have htrace : WordTrace (prefixWord ++ tailWord_845565) baseStart_845565 baseEnd_845565 := by
    simpa [prefixWord, tailWord_845565, baseEnd_845565] using wordTrace_append hprefix tailTrace_845565
  have hstable : (prefixWord ++ tailWord_845565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845565).length < 2 ^ (prefixWord ++ tailWord_845565).sum := by decide
  have hdescent : baseEnd_845565 < baseStart_845565 := by decide
  rcases family_descends (prefixWord ++ tailWord_845565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845566 : List Nat := [4, 2, 2, 1, 3, 2, 2, 7]
def baseStart_845566 : Nat := 118140960795 + 845566 * 2 ^ 59
def prefixEnd_845566 : Nat := 4983230072969 + 3 ^ 40 * 845566 * 2
def baseEnd_845566 : Nat := 16080806781471998253197

theorem tailTrace_845566 : CollatzResearch.WordTrace tailWord_845566 prefixEnd_845566 16080806781471998253197 := by
  unfold tailWord_845566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855040706833283502593569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20560217103110845347165701 3855040706833283502593569)
  ·
    refine ⟨2891280530124962626945177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3855040706833283502593569 2891280530124962626945177)
    ·
      refine ⟨2168460397593721970208883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2891280530124962626945177 2168460397593721970208883)
      ·
        refine ⟨3252690596390582955313325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168460397593721970208883 3252690596390582955313325)
        ·
          refine ⟨1219758973646468608242497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3252690596390582955313325 1219758973646468608242497)
          ·
            refine ⟨914819230234851456181873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219758973646468608242497 914819230234851456181873)
            ·
              refine ⟨686114422676138592136405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914819230234851456181873 686114422676138592136405)
              ·
                refine ⟨16080806781471998253197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 686114422676138592136405 16080806781471998253197)
                ·
                  rfl

theorem cell23_845566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_845566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845566 prefixEnd_845566 := by exact prefixLift 845566
  have htrace : WordTrace (prefixWord ++ tailWord_845566) baseStart_845566 baseEnd_845566 := by
    simpa [prefixWord, tailWord_845566, baseEnd_845566] using wordTrace_append hprefix tailTrace_845566
  have hstable : (prefixWord ++ tailWord_845566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845566).length < 2 ^ (prefixWord ++ tailWord_845566).sum := by decide
  have hdescent : baseEnd_845566 < baseStart_845566 := by decide
  rcases family_descends (prefixWord ++ tailWord_845566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845569 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_845569 : Nat := 118140960795 + 845569 * 2 ^ 59
def prefixEnd_845569 : Nat := 4983230072969 + 3 ^ 40 * 845569 * 2
def baseEnd_845569 : Nat := 434183323541707441098805

theorem tailTrace_845569 : CollatzResearch.WordTrace tailWord_845569 prefixEnd_845569 434183323541707441098805 := by
  unfold tailWord_845569
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840435073655399533107761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20560290049103599688738507 30840435073655399533107761)
  ·
    refine ⟨23130326305241549649830821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30840435073655399533107761 23130326305241549649830821)
    ·
      refine ⟨4336936182232790559343279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23130326305241549649830821 4336936182232790559343279)
      ·
        refine ⟨6505404273349185839014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4336936182232790559343279 6505404273349185839014919)
        ·
          refine ⟨9758106410023778758522379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505404273349185839014919 9758106410023778758522379)
          ·
            refine ⟨14637159615035668137783569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9758106410023778758522379 14637159615035668137783569)
            ·
              refine ⟨10977869711276751103337677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14637159615035668137783569 10977869711276751103337677)
              ·
                refine ⟨4116701141728781663751629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10977869711276751103337677 4116701141728781663751629)
                ·
                  refine ⟨1543762928148293123906861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4116701141728781663751629 1543762928148293123906861)
                  ·
                    refine ⟨578911098055609921465073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543762928148293123906861 578911098055609921465073)
                    ·
                      refine ⟨434183323541707441098805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578911098055609921465073 434183323541707441098805)
                      ·
                        rfl

theorem cell23_845569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_845569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845569 prefixEnd_845569 := by exact prefixLift 845569
  have htrace : WordTrace (prefixWord ++ tailWord_845569) baseStart_845569 baseEnd_845569 := by
    simpa [prefixWord, tailWord_845569, baseEnd_845569] using wordTrace_append hprefix tailTrace_845569
  have hstable : (prefixWord ++ tailWord_845569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845569).length < 2 ^ (prefixWord ++ tailWord_845569).sum := by decide
  have hdescent : baseEnd_845569 < baseStart_845569 := by decide
  rcases family_descends (prefixWord ++ tailWord_845569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845572 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_845572 : Nat := 118140960795 + 845572 * 2 ^ 59
def prefixEnd_845572 : Nat := 4983230072969 + 3 ^ 40 * 845572 * 2
def baseEnd_845572 : Nat := 434184863983670929361291

theorem tailTrace_845572 : CollatzResearch.WordTrace tailWord_845572 prefixEnd_845572 434184863983670929361291 := by
  unfold tailWord_845572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15420272246322265522733485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20560362995096354030311313 15420272246322265522733485)
  ·
    refine ⟨5782602092370849571025057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15420272246322265522733485 5782602092370849571025057)
    ·
      refine ⟨4336951569278137178268793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5782602092370849571025057 4336951569278137178268793)
      ·
        refine ⟨3252713676958602883701595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4336951569278137178268793 3252713676958602883701595)
        ·
          refine ⟨4879070515437904325552393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3252713676958602883701595 4879070515437904325552393)
          ·
            refine ⟨3659302886578428244164295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4879070515437904325552393 3659302886578428244164295)
            ·
              refine ⟨5488954329867642366246443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659302886578428244164295 5488954329867642366246443)
              ·
                refine ⟨8233431494801463549369665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488954329867642366246443 8233431494801463549369665)
                ·
                  refine ⟨6175073621101097662027249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8233431494801463549369665 6175073621101097662027249)
                  ·
                    refine ⟨4631305215825823246520437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6175073621101097662027249 4631305215825823246520437)
                    ·
                      refine ⟨434184863983670929361291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4631305215825823246520437 434184863983670929361291)
                      ·
                        rfl

theorem cell23_845572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_845572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845572 prefixEnd_845572 := by exact prefixLift 845572
  have htrace : WordTrace (prefixWord ++ tailWord_845572) baseStart_845572 baseEnd_845572 := by
    simpa [prefixWord, tailWord_845572, baseEnd_845572] using wordTrace_append hprefix tailTrace_845572
  have hstable : (prefixWord ++ tailWord_845572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845572).length < 2 ^ (prefixWord ++ tailWord_845572).sum := by decide
  have hdescent : baseEnd_845572 < baseStart_845572 := by decide
  rcases family_descends (prefixWord ++ tailWord_845572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845602 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_845602 : Nat := 118140960795 + 845602 * 2 ^ 59
def prefixEnd_845602 : Nat := 4983230072969 + 3 ^ 40 * 845602 * 2
def baseEnd_845602 : Nat := 434200268403305811986153

theorem tailTrace_845602 : CollatzResearch.WordTrace tailWord_845602 prefixEnd_845602 434200268403305811986153 := by
  unfold tailWord_845602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710409670633961542264765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20561092455023897446039373 7710409670633961542264765)
  ·
    refine ⟨2891403626487735578349287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7710409670633961542264765 2891403626487735578349287)
    ·
      refine ⟨4337105439731603367523931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2891403626487735578349287 4337105439731603367523931)
      ·
        refine ⟨6505658159597405051285897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337105439731603367523931 6505658159597405051285897)
        ·
          refine ⟨4879243619698053788464423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6505658159597405051285897 4879243619698053788464423)
          ·
            refine ⟨7318865429547080682696635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879243619698053788464423 7318865429547080682696635)
            ·
              refine ⟨10978298144320621024044953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7318865429547080682696635 10978298144320621024044953)
              ·
                refine ⟨8233723608240465768033715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10978298144320621024044953 8233723608240465768033715)
                ·
                  refine ⟨12350585412360698652050573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8233723608240465768033715 12350585412360698652050573)
                  ·
                    refine ⟨4631469529635261994518965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12350585412360698652050573 4631469529635261994518965)
                    ·
                      refine ⟨434200268403305811986153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4631469529635261994518965 434200268403305811986153)
                      ·
                        rfl

theorem cell23_845602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_845602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845602 prefixEnd_845602 := by exact prefixLift 845602
  have htrace : WordTrace (prefixWord ++ tailWord_845602) baseStart_845602 baseEnd_845602 := by
    simpa [prefixWord, tailWord_845602, baseEnd_845602] using wordTrace_append hprefix tailTrace_845602
  have hstable : (prefixWord ++ tailWord_845602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845602).length < 2 ^ (prefixWord ++ tailWord_845602).sum := by decide
  have hdescent : baseEnd_845602 < baseStart_845602 := by decide
  rcases family_descends (prefixWord ++ tailWord_845602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845615 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_845615 : Nat := 118140960795 + 845615 * 2 ^ 59
def prefixEnd_845615 : Nat := 4983230072969 + 3 ^ 40 * 845615 * 2
def baseEnd_845615 : Nat := 434206943651814261123593

theorem tailTrace_845615 : CollatzResearch.WordTrace tailWord_845615 prefixEnd_845615 434206943651814261123593 := by
  unfold tailWord_845615
  simp only [CollatzResearch.WordTrace]
  refine ⟨30842112831488749389282299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20561408554325832926188199 30842112831488749389282299)
  ·
    refine ⟨46263169247233124083923449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30842112831488749389282299 46263169247233124083923449)
    ·
      refine ⟨34697376935424843062942587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46263169247233124083923449 34697376935424843062942587)
      ·
        refine ⟨52046065403137264594413881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34697376935424843062942587 52046065403137264594413881)
        ·
          refine ⟨39034549052352948445810411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52046065403137264594413881 39034549052352948445810411)
          ·
            refine ⟨58551823578529422668715617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39034549052352948445810411 58551823578529422668715617)
            ·
              refine ⟨43913867683897067001536713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58551823578529422668715617 43913867683897067001536713)
              ·
                refine ⟨32935400762922800251152535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43913867683897067001536713 32935400762922800251152535)
                ·
                  refine ⟨49403101144384200376728803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32935400762922800251152535 49403101144384200376728803)
                  ·
                    refine ⟨74104651716576300565093205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49403101144384200376728803 74104651716576300565093205)
                    ·
                      refine ⟨434206943651814261123593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 74104651716576300565093205 434206943651814261123593)
                      ·
                        rfl

theorem cell23_845615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_845615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845615 prefixEnd_845615 := by exact prefixLift 845615
  have htrace : WordTrace (prefixWord ++ tailWord_845615) baseStart_845615 baseEnd_845615 := by
    simpa [prefixWord, tailWord_845615, baseEnd_845615] using wordTrace_append hprefix tailTrace_845615
  have hstable : (prefixWord ++ tailWord_845615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845615).length < 2 ^ (prefixWord ++ tailWord_845615).sum := by decide
  have hdescent : baseEnd_845615 < baseStart_845615 := by decide
  rcases family_descends (prefixWord ++ tailWord_845615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845620 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_845620 : Nat := 118140960795 + 845620 * 2 ^ 59
def prefixEnd_845620 : Nat := 4983230072969 + 3 ^ 40 * 845620 * 2
def baseEnd_845620 : Nat := 434209511055086741561071

theorem tailTrace_845620 : CollatzResearch.WordTrace tailWord_845620 prefixEnd_845620 434209511055086741561071 := by
  unfold tailWord_845620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15421147598235317621607157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20561530130980423495476209 15421147598235317621607157)
  ·
    refine ⟨1445732587334561027025671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15421147598235317621607157 1445732587334561027025671)
    ·
      refine ⟨2168598881001841540538507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445732587334561027025671 2168598881001841540538507)
      ·
        refine ⟨3252898321502762310807761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168598881001841540538507 3252898321502762310807761)
        ·
          refine ⟨2439673741127071733105821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3252898321502762310807761 2439673741127071733105821)
          ·
            refine ⟨914877652922651899914683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2439673741127071733105821 914877652922651899914683)
            ·
              refine ⟨1372316479383977849872025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914877652922651899914683 1372316479383977849872025)
              ·
                refine ⟨1029237359537983387404019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372316479383977849872025 1029237359537983387404019)
                ·
                  refine ⟨1543856039306975081106029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029237359537983387404019 1543856039306975081106029)
                  ·
                    refine ⟨578946014740115655414761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543856039306975081106029 578946014740115655414761)
                    ·
                      refine ⟨434209511055086741561071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578946014740115655414761 434209511055086741561071)
                      ·
                        rfl

theorem cell23_845620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_845620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845620 prefixEnd_845620 := by exact prefixLift 845620
  have htrace : WordTrace (prefixWord ++ tailWord_845620) baseStart_845620 baseEnd_845620 := by
    simpa [prefixWord, tailWord_845620, baseEnd_845620] using wordTrace_append hprefix tailTrace_845620
  have hstable : (prefixWord ++ tailWord_845620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845620).length < 2 ^ (prefixWord ++ tailWord_845620).sum := by decide
  have hdescent : baseEnd_845620 < baseStart_845620 := by decide
  rcases family_descends (prefixWord ++ tailWord_845620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845632 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3]
def baseStart_845632 : Nat := 118140960795 + 845632 * 2 ^ 59
def prefixEnd_845632 : Nat := 4983230072969 + 3 ^ 40 * 845632 * 2
def baseEnd_845632 : Nat := 434215672822940694611015

theorem tailTrace_845632 : CollatzResearch.WordTrace tailWord_845632 prefixEnd_845632 434215672822940694611015 := by
  unfold tailWord_845632
  simp only [CollatzResearch.WordTrace]
  refine ⟨15421366436213580646325575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20561821914951440861767433 15421366436213580646325575)
  ·
    refine ⟨23132049654320370969488363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15421366436213580646325575 23132049654320370969488363)
    ·
      refine ⟨34698074481480556454232545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23132049654320370969488363 34698074481480556454232545)
      ·
        refine ⟨26023555861110417340674409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34698074481480556454232545 26023555861110417340674409)
        ·
          refine ⟨19517666895832813005505807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26023555861110417340674409 19517666895832813005505807)
          ·
            refine ⟨29276500343749219508258711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19517666895832813005505807 29276500343749219508258711)
            ·
              refine ⟨43914750515623829262388067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29276500343749219508258711 43914750515623829262388067)
              ·
                refine ⟨65872125773435743893582101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43914750515623829262388067 65872125773435743893582101)
                ·
                  refine ⟨3087755895629800495011661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65872125773435743893582101 3087755895629800495011661)
                  ·
                    refine ⟨1157908460861175185629373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087755895629800495011661 1157908460861175185629373)
                    ·
                      refine ⟨434215672822940694611015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157908460861175185629373 434215672822940694611015)
                      ·
                        rfl

theorem cell23_845632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_845632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845632 prefixEnd_845632 := by exact prefixLift 845632
  have htrace : WordTrace (prefixWord ++ tailWord_845632) baseStart_845632 baseEnd_845632 := by
    simpa [prefixWord, tailWord_845632, baseEnd_845632] using wordTrace_append hprefix tailTrace_845632
  have hstable : (prefixWord ++ tailWord_845632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845632).length < 2 ^ (prefixWord ++ tailWord_845632).sum := by decide
  have hdescent : baseEnd_845632 < baseStart_845632 := by decide
  rcases family_descends (prefixWord ++ tailWord_845632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845666 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_845666 : Nat := 118140960795 + 845666 * 2 ^ 59
def prefixEnd_845666 : Nat := 4983230072969 + 3 ^ 40 * 845666 * 2
def baseEnd_845666 : Nat := 434233131165193561585859

theorem tailTrace_845666 : CollatzResearch.WordTrace tailWord_845666 prefixEnd_845666 434233131165193561585859 := by
  unfold tailWord_845666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710993238575996274847213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20562648636202656732925901 7710993238575996274847213)
  ·
    refine ⟨2891622464465998603067705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7710993238575996274847213 2891622464465998603067705)
    ·
      refine ⟨2168716848349498952300779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2891622464465998603067705 2168716848349498952300779)
      ·
        refine ⟨3253075272524248428451169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168716848349498952300779 3253075272524248428451169)
        ·
          refine ⟨2439806454393186321338377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253075272524248428451169 2439806454393186321338377)
          ·
            refine ⟨1829854840794889741003783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439806454393186321338377 1829854840794889741003783)
            ·
              refine ⟨2744782261192334611505675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829854840794889741003783 2744782261192334611505675)
              ·
                refine ⟨4117173391788501917258513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744782261192334611505675 4117173391788501917258513)
                ·
                  refine ⟨3087880043841376437943885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4117173391788501917258513 3087880043841376437943885)
                  ·
                    refine ⟨1157955016440516164228957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087880043841376437943885 1157955016440516164228957)
                    ·
                      refine ⟨434233131165193561585859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157955016440516164228957 434233131165193561585859)
                      ·
                        rfl

theorem cell23_845666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_845666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845666 prefixEnd_845666 := by exact prefixLift 845666
  have htrace : WordTrace (prefixWord ++ tailWord_845666) baseStart_845666 baseEnd_845666 := by
    simpa [prefixWord, tailWord_845666, baseEnd_845666] using wordTrace_append hprefix tailTrace_845666
  have hstable : (prefixWord ++ tailWord_845666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845666).length < 2 ^ (prefixWord ++ tailWord_845666).sum := by decide
  have hdescent : baseEnd_845666 < baseStart_845666 := by decide
  rcases family_descends (prefixWord ++ tailWord_845666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845686 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_845686 : Nat := 118140960795 + 845686 * 2 ^ 59
def prefixEnd_845686 : Nat := 4983230072969 + 3 ^ 40 * 845686 * 2
def baseEnd_845686 : Nat := 144747800259427827778589

theorem tailTrace_845686 : CollatzResearch.WordTrace tailWord_845686 prefixEnd_845686 144747800259427827778589 := by
  unfold tailWord_845686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927793900889470532194807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20563134942821019010077941 1927793900889470532194807)
  ·
    refine ⟨2891690851334205798292211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1927793900889470532194807 2891690851334205798292211)
    ·
      refine ⟨4337536277001308697438317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2891690851334205798292211 4337536277001308697438317)
      ·
        refine ⟨1626576103875490761539369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4337536277001308697438317 1626576103875490761539369)
        ·
          refine ⟨1219932077906618071154527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1626576103875490761539369 1219932077906618071154527)
          ·
            refine ⟨1829898116859927106731791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219932077906618071154527 1829898116859927106731791)
            ·
              refine ⟨2744847175289890660097687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829898116859927106731791 2744847175289890660097687)
              ·
                refine ⟨4117270762934835990146531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744847175289890660097687 4117270762934835990146531)
                ·
                  refine ⟨6175906144402253985219797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117270762934835990146531 6175906144402253985219797)
                  ·
                    refine ⟨144747800259427827778589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6175906144402253985219797 144747800259427827778589)
                    ·
                      rfl

theorem cell23_845686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_845686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845686 prefixEnd_845686 := by exact prefixLift 845686
  have htrace : WordTrace (prefixWord ++ tailWord_845686) baseStart_845686 baseEnd_845686 := by
    simpa [prefixWord, tailWord_845686, baseEnd_845686] using wordTrace_append hprefix tailTrace_845686
  have hstable : (prefixWord ++ tailWord_845686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845686).length < 2 ^ (prefixWord ++ tailWord_845686).sum := by decide
  have hdescent : baseEnd_845686 < baseStart_845686 := by decide
  rcases family_descends (prefixWord ++ tailWord_845686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845689 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 1, 6, 2]
def baseStart_845689 : Nat := 118140960795 + 845689 * 2 ^ 59
def prefixEnd_845689 : Nat := 4983230072969 + 3 ^ 40 * 845689 * 2
def baseEnd_845689 : Nat := 434244941220246971598253

theorem tailTrace_845689 : CollatzResearch.WordTrace tailWord_845689 prefixEnd_845689 434244941220246971598253 := by
  unfold tailWord_845689
  simp only [CollatzResearch.WordTrace]
  refine ⟨30844811833220660027476121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20563207888813773351650747 30844811833220660027476121)
  ·
    refine ⟨23133608874915495020607091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30844811833220660027476121 23133608874915495020607091)
    ·
      refine ⟨34700413312373242530910637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23133608874915495020607091 34700413312373242530910637)
      ·
        refine ⟨13012654992139965949091489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34700413312373242530910637 13012654992139965949091489)
        ·
          refine ⟨9759491244104974461818617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13012654992139965949091489 9759491244104974461818617)
          ·
            refine ⟨7319618433078730846363963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9759491244104974461818617 7319618433078730846363963)
            ·
              refine ⟨10979427649618096269545945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7319618433078730846363963 10979427649618096269545945)
              ·
                refine ⟨8234570737213572202159459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10979427649618096269545945 8234570737213572202159459)
                ·
                  refine ⟨12351856105820358303239189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234570737213572202159459 12351856105820358303239189)
                  ·
                    refine ⟨578993254960329295464337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12351856105820358303239189 578993254960329295464337)
                    ·
                      refine ⟨434244941220246971598253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578993254960329295464337 434244941220246971598253)
                      ·
                        rfl

theorem cell23_845689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_845689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845689 prefixEnd_845689 := by exact prefixLift 845689
  have htrace : WordTrace (prefixWord ++ tailWord_845689) baseStart_845689 baseEnd_845689 := by
    simpa [prefixWord, tailWord_845689, baseEnd_845689] using wordTrace_append hprefix tailTrace_845689
  have hstable : (prefixWord ++ tailWord_845689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845689).length < 2 ^ (prefixWord ++ tailWord_845689).sum := by decide
  have hdescent : baseEnd_845689 < baseStart_845689 := by decide
  rcases family_descends (prefixWord ++ tailWord_845689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845716 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_845716 : Nat := 118140960795 + 845716 * 2 ^ 59
def prefixEnd_845716 : Nat := 4983230072969 + 3 ^ 40 * 845716 * 2
def baseEnd_845716 : Nat := 144752935065972788653543

theorem tailTrace_845716 : CollatzResearch.WordTrace tailWord_845716 prefixEnd_845716 144752935065972788653543 := by
  unfold tailWord_845716
  simp only [CollatzResearch.WordTrace]
  refine ⟨15422898302061421819354501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20563864402748562425806001 15422898302061421819354501)
  ·
    refine ⟨2891793431636516591128969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15422898302061421819354501 2891793431636516591128969)
    ·
      refine ⟨2168845073727387443346727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2891793431636516591128969 2168845073727387443346727)
      ·
        refine ⟨3253267610591081165020091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168845073727387443346727 3253267610591081165020091)
        ·
          refine ⟨4879901415886621747530137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253267610591081165020091 4879901415886621747530137)
          ·
            refine ⟨3659926061914966310647603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4879901415886621747530137 3659926061914966310647603)
            ·
              refine ⟨5489889092872449465971405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659926061914966310647603 5489889092872449465971405)
              ·
                refine ⟨2058708409827168549739277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5489889092872449465971405 2058708409827168549739277)
                ·
                  refine ⟨772015653685188206152229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2058708409827168549739277 772015653685188206152229)
                  ·
                    refine ⟨144752935065972788653543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 772015653685188206152229 144752935065972788653543)
                    ·
                      rfl

theorem cell23_845716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_845716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845716 prefixEnd_845716 := by exact prefixLift 845716
  have htrace : WordTrace (prefixWord ++ tailWord_845716) baseStart_845716 baseEnd_845716 := by
    simpa [prefixWord, tailWord_845716, baseEnd_845716] using wordTrace_append hprefix tailTrace_845716
  have hstable : (prefixWord ++ tailWord_845716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845716).length < 2 ^ (prefixWord ++ tailWord_845716).sum := by decide
  have hdescent : baseEnd_845716 < baseStart_845716 := by decide
  rcases family_descends (prefixWord ++ tailWord_845716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845759 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 1, 5]
def baseStart_845759 : Nat := 118140960795 + 845759 * 2 ^ 59
def prefixEnd_845759 : Nat := 4983230072969 + 3 ^ 40 * 845759 * 2
def baseEnd_845759 : Nat := 144760294955353899240977

theorem tailTrace_845759 : CollatzResearch.WordTrace tailWord_845759 prefixEnd_845759 144760294955353899240977 := by
  unfold tailWord_845759
  simp only [CollatzResearch.WordTrace]
  refine ⟨30847364942967061982524331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20564909961978041321682887 30847364942967061982524331)
  ·
    refine ⟨46271047414450592973786497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30847364942967061982524331 46271047414450592973786497)
    ·
      refine ⟨34703285560837944730339873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46271047414450592973786497 34703285560837944730339873)
      ·
        refine ⟨26027464170628458547754905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34703285560837944730339873 26027464170628458547754905)
        ·
          refine ⟨19520598127971343910816179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26027464170628458547754905 19520598127971343910816179)
          ·
            refine ⟨29280897191957015866224269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19520598127971343910816179 29280897191957015866224269)
            ·
              refine ⟨10980336446983880949834101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29280897191957015866224269 10980336446983880949834101)
              ·
                refine ⟨1029406541904738839046947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10980336446983880949834101 1029406541904738839046947)
                ·
                  refine ⟨1544109812857108258570421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029406541904738839046947 1544109812857108258570421)
                  ·
                    refine ⟨144760294955353899240977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1544109812857108258570421 144760294955353899240977)
                    ·
                      rfl

theorem cell23_845759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_845759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845759 prefixEnd_845759 := by exact prefixLift 845759
  have htrace : WordTrace (prefixWord ++ tailWord_845759) baseStart_845759 baseEnd_845759 := by
    simpa [prefixWord, tailWord_845759, baseEnd_845759] using wordTrace_append hprefix tailTrace_845759
  have hstable : (prefixWord ++ tailWord_845759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845759).length < 2 ^ (prefixWord ++ tailWord_845759).sum := by decide
  have hdescent : baseEnd_845759 < baseStart_845759 := by decide
  rcases family_descends (prefixWord ++ tailWord_845759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845806 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_845806 : Nat := 118140960795 + 845806 * 2 ^ 59
def prefixEnd_845806 : Nat := 4983230072969 + 3 ^ 40 * 845806 * 2
def baseEnd_845806 : Nat := 144768339485607671278405

theorem tailTrace_845806 : CollatzResearch.WordTrace tailWord_845806 prefixEnd_845806 144768339485607671278405 := by
  unfold tailWord_845806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856134896724598626185659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20566052782531192672990181 3856134896724598626185659)
  ·
    refine ⟨5784202345086897939278489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3856134896724598626185659 5784202345086897939278489)
    ·
      refine ⟨4338151758815173454458867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5784202345086897939278489 4338151758815173454458867)
      ·
        refine ⟨6507227638222760181688301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338151758815173454458867 6507227638222760181688301)
        ·
          refine ⟨2440210364333535068133113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6507227638222760181688301 2440210364333535068133113)
          ·
            refine ⟨1830157773250151301099835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440210364333535068133113 1830157773250151301099835)
            ·
              refine ⟨2745236659875226951649753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830157773250151301099835 2745236659875226951649753)
              ·
                refine ⟨2058927494906420213737315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745236659875226951649753 2058927494906420213737315)
                ·
                  refine ⟨3088391242359630320605973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058927494906420213737315 3088391242359630320605973)
                  ·
                    refine ⟨144768339485607671278405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3088391242359630320605973 144768339485607671278405)
                    ·
                      rfl

theorem cell23_845806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_845806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845806 prefixEnd_845806 := by exact prefixLift 845806
  have htrace : WordTrace (prefixWord ++ tailWord_845806) baseStart_845806 baseEnd_845806 := by
    simpa [prefixWord, tailWord_845806, baseEnd_845806] using wordTrace_append hprefix tailTrace_845806
  have hstable : (prefixWord ++ tailWord_845806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845806).length < 2 ^ (prefixWord ++ tailWord_845806).sum := by decide
  have hdescent : baseEnd_845806 < baseStart_845806 := by decide
  rcases family_descends (prefixWord ++ tailWord_845806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845816 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_845816 : Nat := 118140960795 + 845816 * 2 ^ 59
def prefixEnd_845816 : Nat := 4983230072969 + 3 ^ 40 * 845816 * 2
def baseEnd_845816 : Nat := 434310153263367974710169

theorem tailTrace_845816 : CollatzResearch.WordTrace tailWord_845816 prefixEnd_845816 434310153263367974710169 := by
  unfold tailWord_845816
  simp only [CollatzResearch.WordTrace]
  refine ⟨15424721951880280358674651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20566295935840373811566201 15424721951880280358674651)
  ·
    refine ⟨23137082927820420538011977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15424721951880280358674651 23137082927820420538011977)
    ·
      refine ⟨17352812195865315403508983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23137082927820420538011977 17352812195865315403508983)
      ·
        refine ⟨26029218293797973105263475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17352812195865315403508983 26029218293797973105263475)
        ·
          refine ⟨39043827440696959657895213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26029218293797973105263475 39043827440696959657895213)
          ·
            refine ⟨14641435290261359871710705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39043827440696959657895213 14641435290261359871710705)
            ·
              refine ⟨10981076467696019903783029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14641435290261359871710705 10981076467696019903783029)
              ·
                refine ⟨1029475918846501865979659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10981076467696019903783029 1029475918846501865979659)
                ·
                  refine ⟨1544213878269752798969489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029475918846501865979659 1544213878269752798969489)
                  ·
                    refine ⟨1158160408702314599227117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1544213878269752798969489 1158160408702314599227117)
                    ·
                      refine ⟨434310153263367974710169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158160408702314599227117 434310153263367974710169)
                      ·
                        rfl

theorem cell23_845816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_845816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845816 prefixEnd_845816 := by exact prefixLift 845816
  have htrace : WordTrace (prefixWord ++ tailWord_845816) baseStart_845816 baseEnd_845816 := by
    simpa [prefixWord, tailWord_845816, baseEnd_845816] using wordTrace_append hprefix tailTrace_845816
  have hstable : (prefixWord ++ tailWord_845816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845816).length < 2 ^ (prefixWord ++ tailWord_845816).sum := by decide
  have hdescent : baseEnd_845816 < baseStart_845816 := by decide
  rcases family_descends (prefixWord ++ tailWord_845816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845859 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 5]
def baseStart_845859 : Nat := 118140960795 + 845859 * 2 ^ 59
def prefixEnd_845859 : Nat := 4983230072969 + 3 ^ 40 * 845859 * 2
def baseEnd_845859 : Nat := 434332232931511306472471

theorem tailTrace_845859 : CollatzResearch.WordTrace tailWord_845859 prefixEnd_845859 434332232931511306472471 := by
  unfold tailWord_845859
  simp only [CollatzResearch.WordTrace]
  refine ⟨30851012242604779061164631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20567341495069852707443087 30851012242604779061164631)
  ·
    refine ⟨46276518363907168591746947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30851012242604779061164631 46276518363907168591746947)
    ·
      refine ⟨69414777545860752887620421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46276518363907168591746947 69414777545860752887620421)
      ·
        refine ⟨13015270789848891166428829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69414777545860752887620421 13015270789848891166428829)
        ·
          refine ⟨4880726546193334187410811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13015270789848891166428829 4880726546193334187410811)
          ·
            refine ⟨7321089819290001281116217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880726546193334187410811 7321089819290001281116217)
            ·
              refine ⟨5490817364467500960837163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7321089819290001281116217 5490817364467500960837163)
              ·
                refine ⟨8236226046701251441255745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490817364467500960837163 8236226046701251441255745)
                ·
                  refine ⟨6177169535025938580941809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8236226046701251441255745 6177169535025938580941809)
                  ·
                    refine ⟨4632877151269453935706357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6177169535025938580941809 4632877151269453935706357)
                    ·
                      refine ⟨434332232931511306472471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4632877151269453935706357 434332232931511306472471)
                      ·
                        rfl

theorem cell23_845859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_845859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845859 prefixEnd_845859 := by exact prefixLift 845859
  have htrace : WordTrace (prefixWord ++ tailWord_845859) baseStart_845859 baseEnd_845859 := by
    simpa [prefixWord, tailWord_845859, baseEnd_845859] using wordTrace_append hprefix tailTrace_845859
  have hstable : (prefixWord ++ tailWord_845859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845859).length < 2 ^ (prefixWord ++ tailWord_845859).sum := by decide
  have hdescent : baseEnd_845859 < baseStart_845859 := by decide
  rcases family_descends (prefixWord ++ tailWord_845859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845864 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_845864 : Nat := 118140960795 + 845864 * 2 ^ 59
def prefixEnd_845864 : Nat := 4983230072969 + 3 ^ 40 * 845864 * 2
def baseEnd_845864 : Nat := 434334800334783786909949

theorem tailTrace_845864 : CollatzResearch.WordTrace tailWord_845864 prefixEnd_845864 434334800334783786909949 := by
  unfold tailWord_845864
  simp only [CollatzResearch.WordTrace]
  refine ⟨15425597303793332457548323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20567463071724443276731097 15425597303793332457548323)
  ·
    refine ⟨23138395955689998686322485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15425597303793332457548323 23138395955689998686322485)
    ·
      refine ⟨2169224620845937376842733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23138395955689998686322485 2169224620845937376842733)
      ·
        refine ⟨813459232817226516316025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2169224620845937376842733 813459232817226516316025)
        ·
          refine ⟨610094424612919887237019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813459232817226516316025 610094424612919887237019)
          ·
            refine ⟨915141636919379830855529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610094424612919887237019 915141636919379830855529)
            ·
              refine ⟨686356227689534873141647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915141636919379830855529 686356227689534873141647)
              ·
                refine ⟨1029534341534302309712471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686356227689534873141647 1029534341534302309712471)
                ·
                  refine ⟨1544301512301453464568707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029534341534302309712471 1544301512301453464568707)
                  ·
                    refine ⟨2316452268452180196853061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1544301512301453464568707 2316452268452180196853061)
                    ·
                      refine ⟨434334800334783786909949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2316452268452180196853061 434334800334783786909949)
                      ·
                        rfl

theorem cell23_845864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_845864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845864 prefixEnd_845864 := by exact prefixLift 845864
  have htrace : WordTrace (prefixWord ++ tailWord_845864) baseStart_845864 baseEnd_845864 := by
    simpa [prefixWord, tailWord_845864, baseEnd_845864] using wordTrace_append hprefix tailTrace_845864
  have hstable : (prefixWord ++ tailWord_845864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845864).length < 2 ^ (prefixWord ++ tailWord_845864).sum := by decide
  have hdescent : baseEnd_845864 < baseStart_845864 := by decide
  rcases family_descends (prefixWord ++ tailWord_845864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845879 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 2, 6]
def baseStart_845879 : Nat := 118140960795 + 845879 * 2 ^ 59
def prefixEnd_845879 : Nat := 4983230072969 + 3 ^ 40 * 845879 * 2
def baseEnd_845879 : Nat := 144780834181533742740793

theorem tailTrace_845879 : CollatzResearch.WordTrace tailWord_845879 prefixEnd_845879 144780834181533742740793 := by
  unfold tailWord_845879
  simp only [CollatzResearch.WordTrace]
  refine ⟨30851741702532322476892691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20567827801688214984595127 30851741702532322476892691)
  ·
    refine ⟨46277612553798483715339037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30851741702532322476892691 46277612553798483715339037)
    ·
      refine ⟨17354104707674431393252139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46277612553798483715339037 17354104707674431393252139)
      ·
        refine ⟨26031157061511647089878209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17354104707674431393252139 26031157061511647089878209)
        ·
          refine ⟨19523367796133735317408657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26031157061511647089878209 19523367796133735317408657)
          ·
            refine ⟨14642525847100301488056493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19523367796133735317408657 14642525847100301488056493)
            ·
              refine ⟨5490947192662613058021185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14642525847100301488056493 5490947192662613058021185)
              ·
                refine ⟨4118210394496959793515889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5490947192662613058021185 4118210394496959793515889)
                ·
                  refine ⟨3088657795872719845136917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4118210394496959793515889 3088657795872719845136917)
                  ·
                    refine ⟨144780834181533742740793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3088657795872719845136917 144780834181533742740793)
                    ·
                      rfl

theorem cell23_845879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_845879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845879 prefixEnd_845879 := by exact prefixLift 845879
  have htrace : WordTrace (prefixWord ++ tailWord_845879) baseStart_845879 baseEnd_845879 := by
    simpa [prefixWord, tailWord_845879, baseEnd_845879] using wordTrace_append hprefix tailTrace_845879
  have hstable : (prefixWord ++ tailWord_845879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845879).length < 2 ^ (prefixWord ++ tailWord_845879).sum := by decide
  have hdescent : baseEnd_845879 < baseStart_845879 := by decide
  rcases family_descends (prefixWord ++ tailWord_845879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845956 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_845956 : Nat := 118140960795 + 845956 * 2 ^ 59
def prefixEnd_845956 : Nat := 4983230072969 + 3 ^ 40 * 845956 * 2
def baseEnd_845956 : Nat := 144794013518332475653175

theorem tailTrace_845956 : CollatzResearch.WordTrace tailWord_845956 prefixEnd_845956 144794013518332475653175 := by
  unfold tailWord_845956
  simp only [CollatzResearch.WordTrace]
  refine ⟨15427275061626682313722861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20569700082168909751630481 15427275061626682313722861)
  ·
    refine ⟨5785228148110005867646073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15427275061626682313722861 5785228148110005867646073)
    ·
      refine ⟨4338921111082504400734555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5785228148110005867646073 4338921111082504400734555)
      ·
        refine ⟨6508381666623756601101833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338921111082504400734555 6508381666623756601101833)
        ·
          refine ⟨4881286249967817450826375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6508381666623756601101833 4881286249967817450826375)
          ·
            refine ⟨7321929374951726176239563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881286249967817450826375 7321929374951726176239563)
            ·
              refine ⟨10982894062427589264359345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7321929374951726176239563 10982894062427589264359345)
              ·
                refine ⟨8237170546820691948269509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10982894062427589264359345 8237170546820691948269509)
                ·
                  refine ⟨1544469477528879740300533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8237170546820691948269509 1544469477528879740300533)
                  ·
                    refine ⟨144794013518332475653175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1544469477528879740300533 144794013518332475653175)
                    ·
                      rfl

theorem cell23_845956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_845956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845956 prefixEnd_845956 := by exact prefixLift 845956
  have htrace : WordTrace (prefixWord ++ tailWord_845956) baseStart_845956 baseEnd_845956 := by
    simpa [prefixWord, tailWord_845956, baseEnd_845956] using wordTrace_append hprefix tailTrace_845956
  have hstable : (prefixWord ++ tailWord_845956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845956).length < 2 ^ (prefixWord ++ tailWord_845956).sum := by decide
  have hdescent : baseEnd_845956 < baseStart_845956 := by decide
  rcases family_descends (prefixWord ++ tailWord_845956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845994 : List Nat := [3, 1, 5, 1, 2, 2, 2, 2, 5]
def baseStart_845994 : Nat := 118140960795 + 845994 * 2 ^ 59
def prefixEnd_845994 : Nat := 4983230072969 + 3 ^ 40 * 845994 * 2
def baseEnd_845994 : Nat := 48266839202207586476039

theorem tailTrace_845994 : CollatzResearch.WordTrace tailWord_845994 prefixEnd_845994 48266839202207586476039 := by
  unfold tailWord_845994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7713984024278924279332259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20570624064743798078219357 7713984024278924279332259)
  ·
    refine ⟨11570976036418386418998389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7713984024278924279332259 11570976036418386418998389)
    ·
      refine ⟨1084779003414223726781099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11570976036418386418998389 1084779003414223726781099)
      ·
        refine ⟨1627168505121335590171649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084779003414223726781099 1627168505121335590171649)
        ·
          refine ⟨1220376378841001692628737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1627168505121335590171649 1220376378841001692628737)
          ·
            refine ⟨915282284130751269471553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220376378841001692628737 915282284130751269471553)
            ·
              refine ⟨686461713098063452103665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915282284130751269471553 686461713098063452103665)
              ·
                refine ⟨514846284823547589077749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686461713098063452103665 514846284823547589077749)
                ·
                  refine ⟨48266839202207586476039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 514846284823547589077749 48266839202207586476039)
                  ·
                    rfl

theorem cell23_845994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_845994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845994 prefixEnd_845994 := by exact prefixLift 845994
  have htrace : WordTrace (prefixWord ++ tailWord_845994) baseStart_845994 baseEnd_845994 := by
    simpa [prefixWord, tailWord_845994, baseEnd_845994] using wordTrace_append hprefix tailTrace_845994
  have hstable : (prefixWord ++ tailWord_845994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845994).length < 2 ^ (prefixWord ++ tailWord_845994).sum := by decide
  have hdescent : baseEnd_845994 < baseStart_845994 := by decide
  rcases family_descends (prefixWord ++ tailWord_845994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846004 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_846004 : Nat := 118140960795 + 846004 * 2 ^ 59
def prefixEnd_846004 : Nat := 4983230072969 + 3 ^ 40 * 846004 * 2
def baseEnd_846004 : Nat := 434406687626413239159305

theorem tailTrace_846004 : CollatzResearch.WordTrace tailWord_846004 prefixEnd_846004 434406687626413239159305 := by
  unfold tailWord_846004
  simp only [CollatzResearch.WordTrace]
  refine ⟨15428150413539734412596533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20570867218052979216795377 15428150413539734412596533)
  ·
    refine ⟨1446389101269350101180925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15428150413539734412596533 1446389101269350101180925)
    ·
      refine ⟨542395912976006287942847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1446389101269350101180925 542395912976006287942847)
      ·
        refine ⟨813593869464009431914271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542395912976006287942847 813593869464009431914271)
        ·
          refine ⟨1220390804196014147871407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813593869464009431914271 1220390804196014147871407)
          ·
            refine ⟨1830586206294021221807111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220390804196014147871407 1830586206294021221807111)
            ·
              refine ⟨2745879309441031832710667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830586206294021221807111 2745879309441031832710667)
              ·
                refine ⟨4118818964161547749066001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745879309441031832710667 4118818964161547749066001)
                ·
                  refine ⟨3089114223121160811799501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4118818964161547749066001 3089114223121160811799501)
                  ·
                    refine ⟨1158417833670435304424813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089114223121160811799501 1158417833670435304424813)
                    ·
                      refine ⟨434406687626413239159305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158417833670435304424813 434406687626413239159305)
                      ·
                        rfl

theorem cell23_846004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_846004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846004 prefixEnd_846004 := by exact prefixLift 846004
  have htrace : WordTrace (prefixWord ++ tailWord_846004) baseStart_846004 baseEnd_846004 := by
    simpa [prefixWord, tailWord_846004, baseEnd_846004] using wordTrace_append hprefix tailTrace_846004
  have hstable : (prefixWord ++ tailWord_846004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846004).length < 2 ^ (prefixWord ++ tailWord_846004).sum := by decide
  have hdescent : baseEnd_846004 < baseStart_846004 := by decide
  rcases family_descends (prefixWord ++ tailWord_846004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846020 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_846020 : Nat := 118140960795 + 846020 * 2 ^ 59
def prefixEnd_846020 : Nat := 4983230072969 + 3 ^ 40 * 846020 * 2
def baseEnd_846020 : Nat := 144804967772295058853077

theorem tailTrace_846020 : CollatzResearch.WordTrace tailWord_846020 prefixEnd_846020 144804967772295058853077 := by
  unfold tailWord_846020
  simp only [CollatzResearch.WordTrace]
  refine ⟨15428442197510751778887757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20571256263347669038517009 15428442197510751778887757)
  ·
    refine ⟨5785665824066531917082909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15428442197510751778887757 5785665824066531917082909)
    ·
      refine ⟨2169624684024949468906091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5785665824066531917082909 2169624684024949468906091)
      ·
        refine ⟨3254437026037424203359137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169624684024949468906091 3254437026037424203359137)
        ·
          refine ⟨2440827769528068152519353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3254437026037424203359137 2440827769528068152519353)
          ·
            refine ⟨1830620827146051114389515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440827769528068152519353 1830620827146051114389515)
            ·
              refine ⟨2745931240719076671584273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830620827146051114389515 2745931240719076671584273)
              ·
                refine ⟨2059448430539307503688205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745931240719076671584273 2059448430539307503688205)
                ·
                  refine ⟨772293161452240313883077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2059448430539307503688205 772293161452240313883077)
                  ·
                    refine ⟨144804967772295058853077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 772293161452240313883077 144804967772295058853077)
                    ·
                      rfl

theorem cell23_846020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_846020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846020 prefixEnd_846020 := by exact prefixLift 846020
  have htrace : WordTrace (prefixWord ++ tailWord_846020) baseStart_846020 baseEnd_846020 := by
    simpa [prefixWord, tailWord_846020, baseEnd_846020] using wordTrace_append hprefix tailTrace_846020
  have hstable : (prefixWord ++ tailWord_846020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846020).length < 2 ^ (prefixWord ++ tailWord_846020).sum := by decide
  have hdescent : baseEnd_846020 < baseStart_846020 := by decide
  rcases family_descends (prefixWord ++ tailWord_846020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846030 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_846030 : Nat := 118140960795 + 846030 * 2 ^ 59
def prefixEnd_846030 : Nat := 4983230072969 + 3 ^ 40 * 846030 * 2
def baseEnd_846030 : Nat := 434420038123430137434185

theorem tailTrace_846030 : CollatzResearch.WordTrace tailWord_846030 prefixEnd_846030 434420038123430137434185 := by
  unfold tailWord_846030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857156140623159408204943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20571499416656850177093029 3857156140623159408204943)
  ·
    refine ⟨5785734210934739112307415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3857156140623159408204943 5785734210934739112307415)
    ·
      refine ⟨8678601316402108668461123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785734210934739112307415 8678601316402108668461123)
      ·
        refine ⟨13017901974603163002691685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8678601316402108668461123 13017901974603163002691685)
        ·
          refine ⟨2440856620238093063004691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13017901974603163002691685 2440856620238093063004691)
          ·
            refine ⟨3661284930357139594507037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440856620238093063004691 3661284930357139594507037)
            ·
              refine ⟨1372981848883927347940139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3661284930357139594507037 1372981848883927347940139)
              ·
                refine ⟨2059472773325891021910209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372981848883927347940139 2059472773325891021910209)
                ·
                  refine ⟨1544604579994418266432657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2059472773325891021910209 1544604579994418266432657)
                  ·
                    refine ⟨1158453434995813699824493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1544604579994418266432657 1158453434995813699824493)
                    ·
                      refine ⟨434420038123430137434185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158453434995813699824493 434420038123430137434185)
                      ·
                        rfl

theorem cell23_846030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_846030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846030 prefixEnd_846030 := by exact prefixLift 846030
  have htrace : WordTrace (prefixWord ++ tailWord_846030) baseStart_846030 baseEnd_846030 := by
    simpa [prefixWord, tailWord_846030, baseEnd_846030] using wordTrace_append hprefix tailTrace_846030
  have hstable : (prefixWord ++ tailWord_846030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846030).length < 2 ^ (prefixWord ++ tailWord_846030).sum := by decide
  have hdescent : baseEnd_846030 < baseStart_846030 := by decide
  rcases family_descends (prefixWord ++ tailWord_846030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846060 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_846060 : Nat := 118140960795 + 846060 * 2 ^ 59
def prefixEnd_846060 : Nat := 4983230072969 + 3 ^ 40 * 846060 * 2
def baseEnd_846060 : Nat := 434435442543065020059047

theorem tailTrace_846060 : CollatzResearch.WordTrace tailWord_846060 prefixEnd_846060 434435442543065020059047 := by
  unfold tailWord_846060
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429171657438295194615817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20572228876584393592821089 15429171657438295194615817)
  ·
    refine ⟨11571878743078721395961863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15429171657438295194615817 11571878743078721395961863)
    ·
      refine ⟨17357818114618082093942795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11571878743078721395961863 17357818114618082093942795)
      ·
        refine ⟨26036727171927123140914193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17357818114618082093942795 26036727171927123140914193)
        ·
          refine ⟨19527545378945342355685645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26036727171927123140914193 19527545378945342355685645)
          ·
            refine ⟨7322829517104503383382117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19527545378945342355685645 7322829517104503383382117)
            ·
              refine ⟨1373030534457094384384147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7322829517104503383382117 1373030534457094384384147)
              ·
                refine ⟨2059545801685641576576221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373030534457094384384147 2059545801685641576576221)
                ·
                  refine ⟨772329675632115591216083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2059545801685641576576221 772329675632115591216083)
                  ·
                    refine ⟨1158494513448173386824125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 772329675632115591216083 1158494513448173386824125)
                    ·
                      refine ⟨434435442543065020059047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158494513448173386824125 434435442543065020059047)
                      ·
                        rfl

theorem cell23_846060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_846060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846060 prefixEnd_846060 := by exact prefixLift 846060
  have htrace : WordTrace (prefixWord ++ tailWord_846060) baseStart_846060 baseEnd_846060 := by
    simpa [prefixWord, tailWord_846060, baseEnd_846060] using wordTrace_append hprefix tailTrace_846060
  have hstable : (prefixWord ++ tailWord_846060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846060).length < 2 ^ (prefixWord ++ tailWord_846060).sum := by decide
  have hdescent : baseEnd_846060 < baseStart_846060 := by decide
  rcases family_descends (prefixWord ++ tailWord_846060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846070 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_846070 : Nat := 118140960795 + 846070 * 2 ^ 59
def prefixEnd_846070 : Nat := 4983230072969 + 3 ^ 40 * 846070 * 2
def baseEnd_846070 : Nat := 434440577349609980934001

theorem tailTrace_846070 : CollatzResearch.WordTrace tailWord_846070 prefixEnd_846070 434440577349609980934001 := by
  unfold tailWord_846070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928669252802522631068479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20572472029893574731397109 1928669252802522631068479)
  ·
    refine ⟨2893003879203783946602719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1928669252802522631068479 2893003879203783946602719)
    ·
      refine ⟨4339505818805675919904079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2893003879203783946602719 4339505818805675919904079)
      ·
        refine ⟨6509258728208513879856119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339505818805675919904079 6509258728208513879856119)
        ·
          refine ⟨9763888092312770819784179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509258728208513879856119 9763888092312770819784179)
          ·
            refine ⟨14645832138469156229676269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9763888092312770819784179 14645832138469156229676269)
            ·
              refine ⟨5492187051925933586128601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14645832138469156229676269 5492187051925933586128601)
              ·
                refine ⟨4119140288944450189596451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492187051925933586128601 4119140288944450189596451)
                ·
                  refine ⟨6178710433416675284394677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119140288944450189596451 6178710433416675284394677)
                  ·
                    refine ⟨579254103132813307912001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6178710433416675284394677 579254103132813307912001)
                    ·
                      refine ⟨434440577349609980934001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579254103132813307912001 434440577349609980934001)
                      ·
                        rfl

theorem cell23_846070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_846070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846070 prefixEnd_846070 := by exact prefixLift 846070
  have htrace : WordTrace (prefixWord ++ tailWord_846070) baseStart_846070 baseEnd_846070 := by
    simpa [prefixWord, tailWord_846070, baseEnd_846070] using wordTrace_append hprefix tailTrace_846070
  have hstable : (prefixWord ++ tailWord_846070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846070).length < 2 ^ (prefixWord ++ tailWord_846070).sum := by decide
  have hdescent : baseEnd_846070 < baseStart_846070 := by decide
  rcases family_descends (prefixWord ++ tailWord_846070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846083 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 2, 6, 2]
def baseStart_846083 : Nat := 118140960795 + 846083 * 2 ^ 59
def prefixEnd_846083 : Nat := 4983230072969 + 3 ^ 40 * 846083 * 2
def baseEnd_846083 : Nat := 434447252598118430071441

theorem tailTrace_846083 : CollatzResearch.WordTrace tailWord_846083 prefixEnd_846083 434447252598118430071441 := by
  unfold tailWord_846083
  simp only [CollatzResearch.WordTrace]
  refine ⟨30859182193793265317318903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20572788129195510211545935 30859182193793265317318903)
  ·
    refine ⟨46288773290689897975978355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30859182193793265317318903 46288773290689897975978355)
    ·
      refine ⟨69433159936034846963967533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46288773290689897975978355 69433159936034846963967533)
      ·
        refine ⟨26037434976013067611487825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69433159936034846963967533 26037434976013067611487825)
        ·
          refine ⟨19528076232009800708615869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26037434976013067611487825 19528076232009800708615869)
          ·
            refine ⟨7323028587003675265730951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19528076232009800708615869 7323028587003675265730951)
            ·
              refine ⟨10984542880505512898596427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323028587003675265730951 10984542880505512898596427)
              ·
                refine ⟨16476814320758269347894641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10984542880505512898596427 16476814320758269347894641)
                ·
                  refine ⟨12357610740568702010920981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16476814320758269347894641 12357610740568702010920981)
                  ·
                    refine ⟨579263003464157906761921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12357610740568702010920981 579263003464157906761921)
                    ·
                      refine ⟨434447252598118430071441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579263003464157906761921 434447252598118430071441)
                      ·
                        rfl

theorem cell23_846083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_846083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846083 prefixEnd_846083 := by exact prefixLift 846083
  have htrace : WordTrace (prefixWord ++ tailWord_846083) baseStart_846083 baseEnd_846083 := by
    simpa [prefixWord, tailWord_846083, baseEnd_846083] using wordTrace_append hprefix tailTrace_846083
  have hstable : (prefixWord ++ tailWord_846083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846083).length < 2 ^ (prefixWord ++ tailWord_846083).sum := by decide
  have hdescent : baseEnd_846083 < baseStart_846083 := by decide
  rcases family_descends (prefixWord ++ tailWord_846083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846103 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_846103 : Nat := 118140960795 + 846103 * 2 ^ 59
def prefixEnd_846103 : Nat := 4983230072969 + 3 ^ 40 * 846103 * 2
def baseEnd_846103 : Nat := 434457522211208351821349

theorem tailTrace_846103 : CollatzResearch.WordTrace tailWord_846103 prefixEnd_846103 434457522211208351821349 := by
  unfold tailWord_846103
  simp only [CollatzResearch.WordTrace]
  refine ⟨30859911653720808733046963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20573274435813872488697975 30859911653720808733046963)
  ·
    refine ⟨46289867480581213099570445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30859911653720808733046963 46289867480581213099570445)
    ·
      refine ⟨17358700305217954912338917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46289867480581213099570445 17358700305217954912338917)
      ·
        refine ⟨3254756307228366546063547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17358700305217954912338917 3254756307228366546063547)
        ·
          refine ⟨4882134460842549819095321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254756307228366546063547 4882134460842549819095321)
          ·
            refine ⟨3661600845631912364321491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4882134460842549819095321 3661600845631912364321491)
            ·
              refine ⟨5492401268447868546482237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661600845631912364321491 5492401268447868546482237)
              ·
                refine ⟨2059650475667950704930839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5492401268447868546482237 2059650475667950704930839)
                ·
                  refine ⟨3089475713501926057396259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059650475667950704930839 3089475713501926057396259)
                  ·
                    refine ⟨4634213570252889086094389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3089475713501926057396259 4634213570252889086094389)
                    ·
                      refine ⟨434457522211208351821349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4634213570252889086094389 434457522211208351821349)
                      ·
                        rfl

theorem cell23_846103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_846103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846103 prefixEnd_846103 := by exact prefixLift 846103
  have htrace : WordTrace (prefixWord ++ tailWord_846103) baseStart_846103 baseEnd_846103 := by
    simpa [prefixWord, tailWord_846103, baseEnd_846103] using wordTrace_append hprefix tailTrace_846103
  have hstable : (prefixWord ++ tailWord_846103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846103).length < 2 ^ (prefixWord ++ tailWord_846103).sum := by decide
  have hdescent : baseEnd_846103 < baseStart_846103 := by decide
  rcases family_descends (prefixWord ++ tailWord_846103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846137 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 3]
def baseStart_846137 : Nat := 118140960795 + 846137 * 2 ^ 59
def prefixEnd_846137 : Nat := 4983230072969 + 3 ^ 40 * 846137 * 2
def baseEnd_846137 : Nat := 434474980553461218796193

theorem tailTrace_846137 : CollatzResearch.WordTrace tailWord_846137 prefixEnd_846137 434474980553461218796193 := by
  unfold tailWord_846137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30861151735597632539784665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20574101157065088359856443 30861151735597632539784665)
  ·
    refine ⟨23145863801698224404838499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30861151735597632539784665 23145863801698224404838499)
    ·
      refine ⟨34718795702547336607257749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23145863801698224404838499 34718795702547336607257749)
      ·
        refine ⟨1627443548556906403465207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34718795702547336607257749 1627443548556906403465207)
        ·
          refine ⟨2441165322835359605197811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627443548556906403465207 2441165322835359605197811)
          ·
            refine ⟨3661747984253039407796717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441165322835359605197811 3661747984253039407796717)
            ·
              refine ⟨1373155494094889777923769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3661747984253039407796717 1373155494094889777923769)
              ·
                refine ⟨1029866620571167333442827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373155494094889777923769 1029866620571167333442827)
                ·
                  refine ⟨1544799930856751000164241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029866620571167333442827 1544799930856751000164241)
                  ·
                    refine ⟨1158599948142563250123181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1544799930856751000164241 1158599948142563250123181)
                    ·
                      refine ⟨434474980553461218796193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158599948142563250123181 434474980553461218796193)
                      ·
                        rfl

theorem cell23_846137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_846137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846137 prefixEnd_846137 := by exact prefixLift 846137
  have htrace : WordTrace (prefixWord ++ tailWord_846137) baseStart_846137 baseEnd_846137 := by
    simpa [prefixWord, tailWord_846137, baseEnd_846137] using wordTrace_append hprefix tailTrace_846137
  have hstable : (prefixWord ++ tailWord_846137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846137).length < 2 ^ (prefixWord ++ tailWord_846137).sum := by decide
  have hdescent : baseEnd_846137 < baseStart_846137 := by decide
  rcases family_descends (prefixWord ++ tailWord_846137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846167 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_846167 : Nat := 118140960795 + 846167 * 2 ^ 59
def prefixEnd_846167 : Nat := 4983230072969 + 3 ^ 40 * 846167 * 2
def baseEnd_846167 : Nat := 434490384973096101421055

theorem tailTrace_846167 : CollatzResearch.WordTrace tailWord_846167 prefixEnd_846167 434490384973096101421055 := by
  unfold tailWord_846167
  simp only [CollatzResearch.WordTrace]
  refine ⟨30862245925488947663376755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20574830616992631775584503 30862245925488947663376755)
  ·
    refine ⟨46293368888233421495065133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30862245925488947663376755 46293368888233421495065133)
    ·
      refine ⟨17360013333087533060649425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46293368888233421495065133 17360013333087533060649425)
      ·
        refine ⟨13020009999815649795487069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17360013333087533060649425 13020009999815649795487069)
        ·
          refine ⟨4882503749930868673307651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13020009999815649795487069 4882503749930868673307651)
          ·
            refine ⟨7323755624896303009961477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882503749930868673307651 7323755624896303009961477)
            ·
              refine ⟨1373204179668056814367777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7323755624896303009961477 1373204179668056814367777)
              ·
                refine ⟨1029903134751042610775833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373204179668056814367777 1029903134751042610775833)
                ·
                  refine ⟨772427351063281958081875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029903134751042610775833 772427351063281958081875)
                  ·
                    refine ⟨1158641026594922937122813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 772427351063281958081875 1158641026594922937122813)
                    ·
                      refine ⟨434490384973096101421055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158641026594922937122813 434490384973096101421055)
                      ·
                        rfl

theorem cell23_846167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_846167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846167 prefixEnd_846167 := by exact prefixLift 846167
  have htrace : WordTrace (prefixWord ++ tailWord_846167) baseStart_846167 baseEnd_846167 := by
    simpa [prefixWord, tailWord_846167, baseEnd_846167] using wordTrace_append hprefix tailTrace_846167
  have hstable : (prefixWord ++ tailWord_846167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846167).length < 2 ^ (prefixWord ++ tailWord_846167).sum := by decide
  have hdescent : baseEnd_846167 < baseStart_846167 := by decide
  rcases family_descends (prefixWord ++ tailWord_846167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846183 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 1, 8]
def baseStart_846183 : Nat := 118140960795 + 846183 * 2 ^ 59
def prefixEnd_846183 : Nat := 4983230072969 + 3 ^ 40 * 846183 * 2
def baseEnd_846183 : Nat := 144832866887856012940327

theorem tailTrace_846183 : CollatzResearch.WordTrace tailWord_846183 prefixEnd_846183 144832866887856012940327 := by
  unfold tailWord_846183
  simp only [CollatzResearch.WordTrace]
  refine ⟨30862829493430982395959203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20575219662287321597306135 30862829493430982395959203)
  ·
    refine ⟨46294244240146473593938805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30862829493430982395959203 46294244240146473593938805)
    ·
      refine ⟨4340085397513731899431763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46294244240146473593938805 4340085397513731899431763)
      ·
        refine ⟨6510128096270597849147645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4340085397513731899431763 6510128096270597849147645)
        ·
          refine ⟨2441298036101474193430367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6510128096270597849147645 2441298036101474193430367)
          ·
            refine ⟨3661947054152211290145551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441298036101474193430367 3661947054152211290145551)
            ·
              refine ⟨5492920581228316935218327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661947054152211290145551 5492920581228316935218327)
              ·
                refine ⟨8239380871842475402827491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492920581228316935218327 8239380871842475402827491)
                ·
                  refine ⟨12359071307763713104241237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8239380871842475402827491 12359071307763713104241237)
                  ·
                    refine ⟨144832866887856012940327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12359071307763713104241237 144832866887856012940327)
                    ·
                      rfl

theorem cell23_846183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_846183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846183 prefixEnd_846183 := by exact prefixLift 846183
  have htrace : WordTrace (prefixWord ++ tailWord_846183) baseStart_846183 baseEnd_846183 := by
    simpa [prefixWord, tailWord_846183, baseEnd_846183] using wordTrace_append hprefix tailTrace_846183
  have hstable : (prefixWord ++ tailWord_846183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846183).length < 2 ^ (prefixWord ++ tailWord_846183).sum := by decide
  have hdescent : baseEnd_846183 < baseStart_846183 := by decide
  rcases family_descends (prefixWord ++ tailWord_846183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846193 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_846193 : Nat := 118140960795 + 846193 * 2 ^ 59
def prefixEnd_846193 : Nat := 4983230072969 + 3 ^ 40 * 846193 * 2
def baseEnd_846193 : Nat := 434503735470112999695935

theorem tailTrace_846193 : CollatzResearch.WordTrace tailWord_846193 prefixEnd_846193 434503735470112999695935 := by
  unfold tailWord_846193
  simp only [CollatzResearch.WordTrace]
  refine ⟨30863194223394754103823233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20575462815596502735882155 30863194223394754103823233)
  ·
    refine ⟨23147395667546065577867425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30863194223394754103823233 23147395667546065577867425)
    ·
      refine ⟨17360546750659549183400569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23147395667546065577867425 17360546750659549183400569)
      ·
        refine ⟨13020410062994661887550427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17360546750659549183400569 13020410062994661887550427)
        ·
          refine ⟨19530615094491992831325641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13020410062994661887550427 19530615094491992831325641)
          ·
            refine ⟨14647961320868994623494231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19530615094491992831325641 14647961320868994623494231)
            ·
              refine ⟨21971941981303491935241347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14647961320868994623494231 21971941981303491935241347)
              ·
                refine ⟨32957912971955237902862021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21971941981303491935241347 32957912971955237902862021)
                ·
                  refine ⟨6179608682241607106786629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32957912971955237902862021 6179608682241607106786629)
                  ·
                    refine ⟨1158676627920301332522493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179608682241607106786629 1158676627920301332522493)
                    ·
                      refine ⟨434503735470112999695935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158676627920301332522493 434503735470112999695935)
                      ·
                        rfl

theorem cell23_846193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_846193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846193 prefixEnd_846193 := by exact prefixLift 846193
  have htrace : WordTrace (prefixWord ++ tailWord_846193) baseStart_846193 baseEnd_846193 := by
    simpa [prefixWord, tailWord_846193, baseEnd_846193] using wordTrace_append hprefix tailTrace_846193
  have hstable : (prefixWord ++ tailWord_846193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846193).length < 2 ^ (prefixWord ++ tailWord_846193).sum := by decide
  have hdescent : baseEnd_846193 < baseStart_846193 := by decide
  rcases family_descends (prefixWord ++ tailWord_846193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846211 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 1, 3, 2]
def baseStart_846211 : Nat := 118140960795 + 846211 * 2 ^ 59
def prefixEnd_846211 : Nat := 4983230072969 + 3 ^ 40 * 846211 * 2
def baseEnd_846211 : Nat := 434512978121893929270853

theorem tailTrace_846211 : CollatzResearch.WordTrace tailWord_846211 prefixEnd_846211 434512978121893929270853 := by
  unfold tailWord_846211
  simp only [CollatzResearch.WordTrace]
  refine ⟨30863850737329543177978487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20575900491553028785318991 30863850737329543177978487)
  ·
    refine ⟨46295776105994314766967731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30863850737329543177978487 46295776105994314766967731)
    ·
      refine ⟨69443664158991472150451597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46295776105994314766967731 69443664158991472150451597)
      ·
        refine ⟨26041374059621802056419349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69443664158991472150451597 26041374059621802056419349)
        ·
          refine ⟨1220689409044771971394657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26041374059621802056419349 1220689409044771971394657)
          ·
            refine ⟨915517056783578978545993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220689409044771971394657 915517056783578978545993)
            ·
              refine ⟨686637792587684233909495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915517056783578978545993 686637792587684233909495)
              ·
                refine ⟨1029956688881526350864243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686637792587684233909495 1029956688881526350864243)
                ·
                  refine ⟨1544935033322289526296365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029956688881526350864243 1544935033322289526296365)
                  ·
                    refine ⟨579350637495858572361137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1544935033322289526296365 579350637495858572361137)
                    ·
                      refine ⟨434512978121893929270853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579350637495858572361137 434512978121893929270853)
                      ·
                        rfl

theorem cell23_846211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_846211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846211 prefixEnd_846211 := by exact prefixLift 846211
  have htrace : WordTrace (prefixWord ++ tailWord_846211) baseStart_846211 baseEnd_846211 := by
    simpa [prefixWord, tailWord_846211, baseEnd_846211] using wordTrace_append hprefix tailTrace_846211
  have hstable : (prefixWord ++ tailWord_846211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846211).length < 2 ^ (prefixWord ++ tailWord_846211).sum := by decide
  have hdescent : baseEnd_846211 < baseStart_846211 := by decide
  rcases family_descends (prefixWord ++ tailWord_846211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846218 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_846218 : Nat := 118140960795 + 846218 * 2 ^ 59
def prefixEnd_846218 : Nat := 4983230072969 + 3 ^ 40 * 846218 * 2
def baseEnd_846218 : Nat := 434516572486475401883321

theorem tailTrace_846218 : CollatzResearch.WordTrace tailWord_846218 prefixEnd_846218 434516572486475401883321 := by
  unfold tailWord_846218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7716026512076045843370827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20576070698869455582322205 7716026512076045843370827)
  ·
    refine ⟨11574039768114068765056241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7716026512076045843370827 11574039768114068765056241)
    ·
      refine ⟨8680529826085551573792181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11574039768114068765056241 8680529826085551573792181)
      ·
        refine ⟨813799671195520460043017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8680529826085551573792181 813799671195520460043017)
        ·
          refine ⟨610349753396640345032263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813799671195520460043017 610349753396640345032263)
          ·
            refine ⟨915524630094960517548395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610349753396640345032263 915524630094960517548395)
            ·
              refine ⟨1373286945142440776322593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915524630094960517548395 1373286945142440776322593)
              ·
                refine ⟨1029965208856830582241945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373286945142440776322593 1029965208856830582241945)
                ·
                  refine ⟨772473906642622936681459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029965208856830582241945 772473906642622936681459)
                  ·
                    refine ⟨1158710859963934405022189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 772473906642622936681459 1158710859963934405022189)
                    ·
                      refine ⟨434516572486475401883321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158710859963934405022189 434516572486475401883321)
                      ·
                        rfl

theorem cell23_846218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_846218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846218 prefixEnd_846218 := by exact prefixLift 846218
  have htrace : WordTrace (prefixWord ++ tailWord_846218) baseStart_846218 baseEnd_846218 := by
    simpa [prefixWord, tailWord_846218, baseEnd_846218] using wordTrace_append hprefix tailTrace_846218
  have hstable : (prefixWord ++ tailWord_846218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846218).length < 2 ^ (prefixWord ++ tailWord_846218).sum := by decide
  have hdescent : baseEnd_846218 < baseStart_846218 := by decide
  rcases family_descends (prefixWord ++ tailWord_846218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846240 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 3]
def baseStart_846240 : Nat := 118140960795 + 846240 * 2 ^ 59
def prefixEnd_846240 : Nat := 4983230072969 + 3 ^ 40 * 846240 * 2
def baseEnd_846240 : Nat := 434527869060874315808219

theorem tailTrace_846240 : CollatzResearch.WordTrace tailWord_846240 prefixEnd_846240 434527869060874315808219 := by
  unfold tailWord_846240
  simp only [CollatzResearch.WordTrace]
  refine ⟨15432454227112240565392087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20576605636149654087189449 15432454227112240565392087)
  ·
    refine ⟨23148681340668360848088131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15432454227112240565392087 23148681340668360848088131)
    ·
      refine ⟨34723022011002541272132197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23148681340668360848088131 34723022011002541272132197)
      ·
        refine ⟨6510566627062976488524787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34723022011002541272132197 6510566627062976488524787)
        ·
          refine ⟨9765849940594464732787181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510566627062976488524787 9765849940594464732787181)
          ·
            refine ⟨3662193727722924274795193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9765849940594464732787181 3662193727722924274795193)
            ·
              refine ⟨2746645295792193206096395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662193727722924274795193 2746645295792193206096395)
              ·
                refine ⟨4119967943688289809144593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746645295792193206096395 4119967943688289809144593)
                ·
                  refine ⟨3089975957766217356858445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4119967943688289809144593 3089975957766217356858445)
                  ·
                    refine ⟨1158740984162331508821917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089975957766217356858445 1158740984162331508821917)
                    ·
                      refine ⟨434527869060874315808219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158740984162331508821917 434527869060874315808219)
                      ·
                        rfl

theorem cell23_846240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_846240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846240 prefixEnd_846240 := by exact prefixLift 846240
  have htrace : WordTrace (prefixWord ++ tailWord_846240) baseStart_846240 baseEnd_846240 := by
    simpa [prefixWord, tailWord_846240, baseEnd_846240] using wordTrace_append hprefix tailTrace_846240
  have hstable : (prefixWord ++ tailWord_846240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846240).length < 2 ^ (prefixWord ++ tailWord_846240).sum := by decide
  have hdescent : baseEnd_846240 < baseStart_846240 := by decide
  rcases family_descends (prefixWord ++ tailWord_846240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846241 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_846241 : Nat := 118140960795 + 846241 * 2 ^ 59
def prefixEnd_846241 : Nat := 4983230072969 + 3 ^ 40 * 846241 * 2
def baseEnd_846241 : Nat := 434528382541528811895715

theorem tailTrace_846241 : CollatzResearch.WordTrace tailWord_846241 prefixEnd_846241 434528382541528811895715 := by
  unfold tailWord_846241
  simp only [CollatzResearch.WordTrace]
  refine ⟨30864944927220858301570577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20576629951480572201047051 30864944927220858301570577)
  ·
    refine ⟨23148708695415643726177933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30864944927220858301570577 23148708695415643726177933)
    ·
      refine ⟨8680765760780866397316725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23148708695415643726177933 8680765760780866397316725)
      ·
        refine ⟨813821790073206224748443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8680765760780866397316725 813821790073206224748443)
        ·
          refine ⟨1220732685109809337122665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813821790073206224748443 1220732685109809337122665)
          ·
            refine ⟨915549513832357002841999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220732685109809337122665 915549513832357002841999)
            ·
              refine ⟨1373324270748535504262999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915549513832357002841999 1373324270748535504262999)
              ·
                refine ⟨2059986406122803256394499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373324270748535504262999 2059986406122803256394499)
                ·
                  refine ⟨3089979609184204884591749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059986406122803256394499 3089979609184204884591749)
                  ·
                    refine ⟨579371176722038415860953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089979609184204884591749 579371176722038415860953)
                    ·
                      refine ⟨434528382541528811895715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579371176722038415860953 434528382541528811895715)
                      ·
                        rfl

theorem cell23_846241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_846241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846241 prefixEnd_846241 := by exact prefixLift 846241
  have htrace : WordTrace (prefixWord ++ tailWord_846241) baseStart_846241 baseEnd_846241 := by
    simpa [prefixWord, tailWord_846241, baseEnd_846241] using wordTrace_append hprefix tailTrace_846241
  have hstable : (prefixWord ++ tailWord_846241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846241).length < 2 ^ (prefixWord ++ tailWord_846241).sum := by decide
  have hdescent : baseEnd_846241 < baseStart_846241 := by decide
  rcases family_descends (prefixWord ++ tailWord_846241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846243 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 1, 7]
def baseStart_846243 : Nat := 118140960795 + 846243 * 2 ^ 59
def prefixEnd_846243 : Nat := 4983230072969 + 3 ^ 40 * 846243 * 2
def baseEnd_846243 : Nat := 144843136500945934690235

theorem tailTrace_846243 : CollatzResearch.WordTrace tailWord_846243 prefixEnd_846243 144843136500945934690235 := by
  unfold tailWord_846243
  simp only [CollatzResearch.WordTrace]
  refine ⟨30865017873213612643143383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20576678582142408428762255 30865017873213612643143383)
  ·
    refine ⟨46297526809820418964715075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30865017873213612643143383 46297526809820418964715075)
    ·
      refine ⟨69446290214730628447072613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46297526809820418964715075 69446290214730628447072613)
      ·
        refine ⟨13021179415261992833826115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69446290214730628447072613 13021179415261992833826115)
        ·
          refine ⟨19531769122892989250739173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13021179415261992833826115 19531769122892989250739173)
          ·
            refine ⟨3662206710542435484513595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19531769122892989250739173 3662206710542435484513595)
            ·
              refine ⟨5493310065813653226770393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662206710542435484513595 5493310065813653226770393)
              ·
                refine ⟨4119982549360239920077795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5493310065813653226770393 4119982549360239920077795)
                ·
                  refine ⟨6179973824040359880116693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119982549360239920077795 6179973824040359880116693)
                  ·
                    refine ⟨144843136500945934690235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6179973824040359880116693 144843136500945934690235)
                    ·
                      rfl

theorem cell23_846243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 7].length) (baseStart_846243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846243 prefixEnd_846243 := by exact prefixLift 846243
  have htrace : WordTrace (prefixWord ++ tailWord_846243) baseStart_846243 baseEnd_846243 := by
    simpa [prefixWord, tailWord_846243, baseEnd_846243] using wordTrace_append hprefix tailTrace_846243
  have hstable : (prefixWord ++ tailWord_846243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846243).length < 2 ^ (prefixWord ++ tailWord_846243).sum := by decide
  have hdescent : baseEnd_846243 < baseStart_846243 := by decide
  rcases family_descends (prefixWord ++ tailWord_846243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846280 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_846280 : Nat := 118140960795 + 846280 * 2 ^ 59
def prefixEnd_846280 : Nat := 4983230072969 + 3 ^ 40 * 846280 * 2
def baseEnd_846280 : Nat := 434548408287054159308035

theorem tailTrace_846280 : CollatzResearch.WordTrace tailWord_846280 prefixEnd_846280 434548408287054159308035 := by
  unfold tailWord_846280
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433183687039783981120147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20577578249386378641493529 15433183687039783981120147)
  ·
    refine ⟨23149775530559675971680221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15433183687039783981120147 23149775530559675971680221)
    ·
      refine ⟨8681165823959878489380083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23149775530559675971680221 8681165823959878489380083)
      ·
        refine ⟨13021748735939817734070125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8681165823959878489380083 13021748735939817734070125)
        ·
          refine ⟨4883155775977431650276297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13021748735939817734070125 4883155775977431650276297)
          ·
            refine ⟨3662366831983073737707223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4883155775977431650276297 3662366831983073737707223)
            ·
              refine ⟨5493550247974610606560835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662366831983073737707223 5493550247974610606560835)
              ·
                refine ⟨8240325371961915909841253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5493550247974610606560835 8240325371961915909841253)
                ·
                  refine ⟨1545061007242859233095235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8240325371961915909841253 1545061007242859233095235)
                  ·
                    refine ⟨2317591510864288849642853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1545061007242859233095235 2317591510864288849642853)
                    ·
                      refine ⟨434548408287054159308035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2317591510864288849642853 434548408287054159308035)
                      ·
                        rfl

theorem cell23_846280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_846280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846280 prefixEnd_846280 := by exact prefixLift 846280
  have htrace : WordTrace (prefixWord ++ tailWord_846280) baseStart_846280 baseEnd_846280 := by
    simpa [prefixWord, tailWord_846280, baseEnd_846280] using wordTrace_append hprefix tailTrace_846280
  have hstable : (prefixWord ++ tailWord_846280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846280).length < 2 ^ (prefixWord ++ tailWord_846280).sum := by decide
  have hdescent : baseEnd_846280 < baseStart_846280 := by decide
  rcases family_descends (prefixWord ++ tailWord_846280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846337 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 6]
def baseStart_846337 : Nat := 118140960795 + 846337 * 2 ^ 59
def prefixEnd_846337 : Nat := 4983230072969 + 3 ^ 40 * 846337 * 2
def baseEnd_846337 : Nat := 48286408520484492921697

theorem tailTrace_846337 : CollatzResearch.WordTrace tailWord_846337 prefixEnd_846337 48286408520484492921697 := by
  unfold tailWord_846337
  simp only [CollatzResearch.WordTrace]
  refine ⟨30868446334873066697065265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20578964223248711131376843 30868446334873066697065265)
  ·
    refine ⟨23151334751154800022798949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30868446334873066697065265 23151334751154800022798949)
    ·
      refine ⟨4340875265841525004274803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23151334751154800022798949 4340875265841525004274803)
      ·
        refine ⟨6511312898762287506412205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4340875265841525004274803 6511312898762287506412205)
        ·
          refine ⟨2441742337035857814904577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6511312898762287506412205 2441742337035857814904577)
          ·
            refine ⟨1831306752776893361178433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2441742337035857814904577 1831306752776893361178433)
            ·
              refine ⟨1373480064582670020883825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831306752776893361178433 1373480064582670020883825)
              ·
                refine ⟨1030110048437002515662869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373480064582670020883825 1030110048437002515662869)
                ·
                  refine ⟨48286408520484492921697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1030110048437002515662869 48286408520484492921697)
                  ·
                    rfl

theorem cell23_846337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 6].length) (baseStart_846337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846337 prefixEnd_846337 := by exact prefixLift 846337
  have htrace : WordTrace (prefixWord ++ tailWord_846337) baseStart_846337 baseEnd_846337 := by
    simpa [prefixWord, tailWord_846337, baseEnd_846337] using wordTrace_append hprefix tailTrace_846337
  have hstable : (prefixWord ++ tailWord_846337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846337).length < 2 ^ (prefixWord ++ tailWord_846337).sum := by decide
  have hdescent : baseEnd_846337 < baseStart_846337 := by decide
  rcases family_descends (prefixWord ++ tailWord_846337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846357 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_846357 : Nat := 118140960795 + 846357 * 2 ^ 59
def prefixEnd_846357 : Nat := 4983230072969 + 3 ^ 40 * 846357 * 2
def baseEnd_846357 : Nat := 434587946297450358045181

theorem tailTrace_846357 : CollatzResearch.WordTrace tailWord_846357 prefixEnd_846357 434587946297450358045181 := by
  unfold tailWord_846357
  simp only [CollatzResearch.WordTrace]
  refine ⟨30869175794800610112793325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20579450529867073408528883 30869175794800610112793325)
  ·
    refine ⟨11575940923050228792297497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30869175794800610112793325 11575940923050228792297497)
    ·
      refine ⟨8681955692287671594223123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11575940923050228792297497 8681955692287671594223123)
      ·
        refine ⟨13022933538431507391334685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8681955692287671594223123 13022933538431507391334685)
        ·
          refine ⟨4883600076911815271750507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13022933538431507391334685 4883600076911815271750507)
          ·
            refine ⟨7325400115367722907625761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883600076911815271750507 7325400115367722907625761)
            ·
              refine ⟨5494050086525792180719321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7325400115367722907625761 5494050086525792180719321)
              ·
                refine ⟨4120537564894344135539491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5494050086525792180719321 4120537564894344135539491)
                ·
                  refine ⟨6180806347341516203309237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120537564894344135539491 6180806347341516203309237)
                  ·
                    refine ⟨579450595063267144060241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6180806347341516203309237 579450595063267144060241)
                    ·
                      refine ⟨434587946297450358045181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579450595063267144060241 434587946297450358045181)
                      ·
                        rfl

theorem cell23_846357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_846357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846357 prefixEnd_846357 := by exact prefixLift 846357
  have htrace : WordTrace (prefixWord ++ tailWord_846357) baseStart_846357 baseEnd_846357 := by
    simpa [prefixWord, tailWord_846357, baseEnd_846357] using wordTrace_append hprefix tailTrace_846357
  have hstable : (prefixWord ++ tailWord_846357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846357).length < 2 ^ (prefixWord ++ tailWord_846357).sum := by decide
  have hdescent : baseEnd_846357 < baseStart_846357 := by decide
  rcases family_descends (prefixWord ++ tailWord_846357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846364 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_846364 : Nat := 118140960795 + 846364 * 2 ^ 59
def prefixEnd_846364 : Nat := 4983230072969 + 3 ^ 40 * 846364 * 2
def baseEnd_846364 : Nat := 434591540662031830657649

theorem tailTrace_846364 : CollatzResearch.WordTrace tailWord_846364 prefixEnd_846364 434591540662031830657649 := by
  unfold tailWord_846364
  simp only [CollatzResearch.WordTrace]
  refine ⟨15434715552887625154149073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20579620737183500205532097 15434715552887625154149073)
  ·
    refine ⟨11576036664665718865611805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15434715552887625154149073 11576036664665718865611805)
    ·
      refine ⟨4341013749249644574604427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11576036664665718865611805 4341013749249644574604427)
      ·
        refine ⟨6511520623874466861906641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341013749249644574604427 6511520623874466861906641)
        ·
          refine ⟨4883640467905850146429981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6511520623874466861906641 4883640467905850146429981)
          ·
            refine ⟨1831365175464693804911243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4883640467905850146429981 1831365175464693804911243)
            ·
              refine ⟨2747047763197040707366865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831365175464693804911243 2747047763197040707366865)
              ·
                refine ⟨2060285822397780530525149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747047763197040707366865 2060285822397780530525149)
                ·
                  refine ⟨772607183399167698946931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2060285822397780530525149 772607183399167698946931)
                  ·
                    refine ⟨1158910775098751548420397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 772607183399167698946931 1158910775098751548420397)
                    ·
                      refine ⟨434591540662031830657649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158910775098751548420397 434591540662031830657649)
                      ·
                        rfl

theorem cell23_846364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_846364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846364 prefixEnd_846364 := by exact prefixLift 846364
  have htrace : WordTrace (prefixWord ++ tailWord_846364) baseStart_846364 baseEnd_846364 := by
    simpa [prefixWord, tailWord_846364, baseEnd_846364] using wordTrace_append hprefix tailTrace_846364
  have hstable : (prefixWord ++ tailWord_846364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846364).length < 2 ^ (prefixWord ++ tailWord_846364).sum := by decide
  have hdescent : baseEnd_846364 < baseStart_846364 := by decide
  rcases family_descends (prefixWord ++ tailWord_846364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846387 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 4]
def baseStart_846387 : Nat := 118140960795 + 846387 * 2 ^ 59
def prefixEnd_846387 : Nat := 4983230072969 + 3 ^ 40 * 846387 * 2
def baseEnd_846387 : Nat := 434603350717085240670043

theorem tailTrace_846387 : CollatzResearch.WordTrace tailWord_846387 prefixEnd_846387 434603350717085240670043 := by
  unfold tailWord_846387
  simp only [CollatzResearch.WordTrace]
  refine ⟨30870269984691925236385415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20580179989794616824256943 30870269984691925236385415)
  ·
    refine ⟨46305404977037887854578123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30870269984691925236385415 46305404977037887854578123)
    ·
      refine ⟨69458107465556831781867185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46305404977037887854578123 69458107465556831781867185)
      ·
        refine ⟨52093580599167623836400389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69458107465556831781867185 52093580599167623836400389)
        ·
          refine ⟨9767546362343929469325073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52093580599167623836400389 9767546362343929469325073)
          ·
            refine ⟨7325659771757947101993805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9767546362343929469325073 7325659771757947101993805)
            ·
              refine ⟨2747122414409230163247677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7325659771757947101993805 2747122414409230163247677)
              ·
                refine ⟨1030170905403461311217879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2747122414409230163247677 1030170905403461311217879)
                ·
                  refine ⟨1545256358105191966826819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030170905403461311217879 1545256358105191966826819)
                  ·
                    refine ⟨2317884537157787950240229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1545256358105191966826819 2317884537157787950240229)
                    ·
                      refine ⟨434603350717085240670043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2317884537157787950240229 434603350717085240670043)
                      ·
                        rfl

theorem cell23_846387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 4].length) (baseStart_846387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846387 prefixEnd_846387 := by exact prefixLift 846387
  have htrace : WordTrace (prefixWord ++ tailWord_846387) baseStart_846387 baseEnd_846387 := by
    simpa [prefixWord, tailWord_846387, baseEnd_846387] using wordTrace_append hprefix tailTrace_846387
  have hstable : (prefixWord ++ tailWord_846387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846387).length < 2 ^ (prefixWord ++ tailWord_846387).sum := by decide
  have hdescent : baseEnd_846387 < baseStart_846387 := by decide
  rcases family_descends (prefixWord ++ tailWord_846387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846388 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 6]
def baseStart_846388 : Nat := 118140960795 + 846388 * 2 ^ 59
def prefixEnd_846388 : Nat := 4983230072969 + 3 ^ 40 * 846388 * 2
def baseEnd_846388 : Nat := 48289318244193304084171

theorem tailTrace_846388 : CollatzResearch.WordTrace tailWord_846388 prefixEnd_846388 48289318244193304084171 := by
  unfold tailWord_846388
  simp only [CollatzResearch.WordTrace]
  refine ⟨15435153228844151203585909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20580204305125534938114545 15435153228844151203585909)
  ·
    refine ⟨1447045615204139175336179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15435153228844151203585909 1447045615204139175336179)
    ·
      refine ⟨2170568422806208763004269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1447045615204139175336179 2170568422806208763004269)
      ·
        refine ⟨813963158552328286126601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2170568422806208763004269 813963158552328286126601)
        ·
          refine ⟨610472368914246214594951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813963158552328286126601 610472368914246214594951)
          ·
            refine ⟨915708553371369321892427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610472368914246214594951 915708553371369321892427)
            ·
              refine ⟨1373562830057053982838641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915708553371369321892427 1373562830057053982838641)
              ·
                refine ⟨1030172122542790487128981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373562830057053982838641 1030172122542790487128981)
                ·
                  refine ⟨48289318244193304084171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1030172122542790487128981 48289318244193304084171)
                  ·
                    rfl

theorem cell23_846388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_846388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846388 prefixEnd_846388 := by exact prefixLift 846388
  have htrace : WordTrace (prefixWord ++ tailWord_846388) baseStart_846388 baseEnd_846388 := by
    simpa [prefixWord, tailWord_846388, baseEnd_846388] using wordTrace_append hprefix tailTrace_846388
  have hstable : (prefixWord ++ tailWord_846388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846388).length < 2 ^ (prefixWord ++ tailWord_846388).sum := by decide
  have hdescent : baseEnd_846388 < baseStart_846388 := by decide
  rcases family_descends (prefixWord ++ tailWord_846388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846398 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_846398 : Nat := 118140960795 + 846398 * 2 ^ 59
def prefixEnd_846398 : Nat := 4983230072969 + 3 ^ 40 * 846398 * 2
def baseEnd_846398 : Nat := 434608999004284697632493

theorem tailTrace_846398 : CollatzResearch.WordTrace tailWord_846398 prefixEnd_846398 434608999004284697632493 := by
  unfold tailWord_846398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858833898456509264379481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20580447458434716076690565 3858833898456509264379481)
  ·
    refine ⟨2894125423842381948284611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3858833898456509264379481 2894125423842381948284611)
    ·
      refine ⟨4341188135763572922426917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2894125423842381948284611 4341188135763572922426917)
      ·
        refine ⟨813972775455669922955047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4341188135763572922426917 813972775455669922955047)
        ·
          refine ⟨1220959163183504884432571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813972775455669922955047 1220959163183504884432571)
          ·
            refine ⟨1831438744775257326648857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220959163183504884432571 1831438744775257326648857)
            ·
              refine ⟨1373579058581442994986643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831438744775257326648857 1373579058581442994986643)
              ·
                refine ⟨2060368587872164492479965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373579058581442994986643 2060368587872164492479965)
                ·
                  refine ⟨772638220452061684679987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2060368587872164492479965 772638220452061684679987)
                  ·
                    refine ⟨1158957330678092527019981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 772638220452061684679987 1158957330678092527019981)
                    ·
                      refine ⟨434608999004284697632493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1158957330678092527019981 434608999004284697632493)
                      ·
                        rfl

theorem cell23_846398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_846398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846398 prefixEnd_846398 := by exact prefixLift 846398
  have htrace : WordTrace (prefixWord ++ tailWord_846398) baseStart_846398 baseEnd_846398 := by
    simpa [prefixWord, tailWord_846398, baseEnd_846398] using wordTrace_append hprefix tailTrace_846398
  have hstable : (prefixWord ++ tailWord_846398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846398).length < 2 ^ (prefixWord ++ tailWord_846398).sum := by decide
  have hdescent : baseEnd_846398 < baseStart_846398 := by decide
  rcases family_descends (prefixWord ++ tailWord_846398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846400 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_846400 : Nat := 118140960795 + 846400 * 2 ^ 59
def prefixEnd_846400 : Nat := 4983230072969 + 3 ^ 40 * 846400 * 2
def baseEnd_846400 : Nat := 434610025965593689807483

theorem tailTrace_846400 : CollatzResearch.WordTrace tailWord_846400 prefixEnd_846400 434610025965593689807483 := by
  unfold tailWord_846400
  simp only [CollatzResearch.WordTrace]
  refine ⟨15435372066822414228304327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20580496089096552304405769 15435372066822414228304327)
  ·
    refine ⟨23153058100233621342456491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15435372066822414228304327 23153058100233621342456491)
    ·
      refine ⟨34729587150350432013684737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23153058100233621342456491 34729587150350432013684737)
      ·
        refine ⟨26047190362762824010263553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34729587150350432013684737 26047190362762824010263553)
        ·
          refine ⟨19535392772072118007697665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26047190362762824010263553 19535392772072118007697665)
          ·
            refine ⟨14651544579054088505773249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19535392772072118007697665 14651544579054088505773249)
            ·
              refine ⟨10988658434290566379329937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14651544579054088505773249 10988658434290566379329937)
              ·
                refine ⟨8241493825717924784497453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10988658434290566379329937 8241493825717924784497453)
                ·
                  refine ⟨3090560184644221794186545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8241493825717924784497453 3090560184644221794186545)
                  ·
                    refine ⟨2317920138483166345639909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090560184644221794186545 2317920138483166345639909)
                    ·
                      refine ⟨434610025965593689807483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2317920138483166345639909 434610025965593689807483)
                      ·
                        rfl

theorem cell23_846400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_846400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846400 prefixEnd_846400 := by exact prefixLift 846400
  have htrace : WordTrace (prefixWord ++ tailWord_846400) baseStart_846400 baseEnd_846400 := by
    simpa [prefixWord, tailWord_846400, baseEnd_846400] using wordTrace_append hprefix tailTrace_846400
  have hstable : (prefixWord ++ tailWord_846400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846400).length < 2 ^ (prefixWord ++ tailWord_846400).sum := by decide
  have hdescent : baseEnd_846400 < baseStart_846400 := by decide
  rcases family_descends (prefixWord ++ tailWord_846400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846407 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_846407 : Nat := 118140960795 + 846407 * 2 ^ 59
def prefixEnd_846407 : Nat := 4983230072969 + 3 ^ 40 * 846407 * 2
def baseEnd_846407 : Nat := 434613620330175162419951

theorem tailTrace_846407 : CollatzResearch.WordTrace tailWord_846407 prefixEnd_846407 434613620330175162419951 := by
  unfold tailWord_846407
  simp only [CollatzResearch.WordTrace]
  refine ⟨30870999444619468652113475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20580666296412979101408983 30870999444619468652113475)
  ·
    refine ⟨46306499166929202978170213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30870999444619468652113475 46306499166929202978170213)
    ·
      refine ⟨8682468593799225558406915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46306499166929202978170213 8682468593799225558406915)
      ·
        refine ⟨13023702890698838337610373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8682468593799225558406915 13023702890698838337610373)
        ·
          refine ⟨2441944292006032188301945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13023702890698838337610373 2441944292006032188301945)
          ·
            refine ⟨1831458219004524141226459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2441944292006032188301945 1831458219004524141226459)
            ·
              refine ⟨2747187328506786211839689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831458219004524141226459 2747187328506786211839689)
              ·
                refine ⟨2060390496380089658879767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747187328506786211839689 2060390496380089658879767)
                ·
                  refine ⟨3090585744570134488319651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060390496380089658879767 3090585744570134488319651)
                  ·
                    refine ⟨4635878616855201732479477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3090585744570134488319651 4635878616855201732479477)
                    ·
                      refine ⟨434613620330175162419951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4635878616855201732479477 434613620330175162419951)
                      ·
                        rfl

theorem cell23_846407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_846407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846407 prefixEnd_846407 := by exact prefixLift 846407
  have htrace : WordTrace (prefixWord ++ tailWord_846407) baseStart_846407 baseEnd_846407 := by
    simpa [prefixWord, tailWord_846407, baseEnd_846407] using wordTrace_append hprefix tailTrace_846407
  have hstable : (prefixWord ++ tailWord_846407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846407).length < 2 ^ (prefixWord ++ tailWord_846407).sum := by decide
  have hdescent : baseEnd_846407 < baseStart_846407 := by decide
  rcases family_descends (prefixWord ++ tailWord_846407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846417 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_846417 : Nat := 118140960795 + 846417 * 2 ^ 59
def prefixEnd_846417 : Nat := 4983230072969 + 3 ^ 40 * 846417 * 2
def baseEnd_846417 : Nat := 434618755136720123294905

theorem tailTrace_846417 : CollatzResearch.WordTrace tailWord_846417 prefixEnd_846417 434618755136720123294905 := by
  unfold tailWord_846417
  simp only [CollatzResearch.WordTrace]
  refine ⟨30871364174583240359977505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20580909449722160239985003 30871364174583240359977505)
  ·
    refine ⟨23153523130937430269983129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30871364174583240359977505 23153523130937430269983129)
    ·
      refine ⟨17365142348203072702487347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23153523130937430269983129 17365142348203072702487347)
      ·
        refine ⟨26047713522304609053731021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17365142348203072702487347 26047713522304609053731021)
        ·
          refine ⟨9767892570864228395149133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26047713522304609053731021 9767892570864228395149133)
          ·
            refine ⟨3662959714074085648180925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9767892570864228395149133 3662959714074085648180925)
            ·
              refine ⟨1373609892777782118067847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3662959714074085648180925 1373609892777782118067847)
              ·
                refine ⟨2060414839166673177101771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373609892777782118067847 2060414839166673177101771)
                ·
                  refine ⟨3090622258750009765652657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060414839166673177101771 3090622258750009765652657)
                  ·
                    refine ⟨2317966694062507324239493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3090622258750009765652657 2317966694062507324239493)
                    ·
                      refine ⟨434618755136720123294905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2317966694062507324239493 434618755136720123294905)
                      ·
                        rfl

theorem cell23_846417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_846417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846417 prefixEnd_846417 := by exact prefixLift 846417
  have htrace : WordTrace (prefixWord ++ tailWord_846417) baseStart_846417 baseEnd_846417 := by
    simpa [prefixWord, tailWord_846417, baseEnd_846417] using wordTrace_append hprefix tailTrace_846417
  have hstable : (prefixWord ++ tailWord_846417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846417).length < 2 ^ (prefixWord ++ tailWord_846417).sum := by decide
  have hdescent : baseEnd_846417 < baseStart_846417 := by decide
  rcases family_descends (prefixWord ++ tailWord_846417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846506 : List Nat := [3, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_846506 : Nat := 118140960795 + 846506 * 2 ^ 59
def prefixEnd_846506 : Nat := 4983230072969 + 3 ^ 40 * 846506 * 2
def baseEnd_846506 : Nat := 434664454914970275081997

theorem tailTrace_846506 : CollatzResearch.WordTrace tailWord_846506 prefixEnd_846506 434664454914970275081997 := by
  unfold tailWord_846506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7718652567815202139991843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20583073514173872373311581 7718652567815202139991843)
  ·
    refine ⟨11577978851722803209987765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7718652567815202139991843 11577978851722803209987765)
    ·
      refine ⟨1085435517349012800936353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11577978851722803209987765 1085435517349012800936353)
      ·
        refine ⟨814076638011759600702265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1085435517349012800936353 814076638011759600702265)
        ·
          refine ⟨610557478508819700526699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814076638011759600702265 610557478508819700526699)
          ·
            refine ⟨915836217763229550790049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610557478508819700526699 915836217763229550790049)
            ·
              refine ⟨686877163322422163092537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915836217763229550790049 686877163322422163092537)
              ·
                refine ⟨515157872491816622319403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686877163322422163092537 515157872491816622319403)
                ·
                  refine ⟨772736808737724933479105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515157872491816622319403 772736808737724933479105)
                  ·
                    refine ⟨579552606553293700109329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 772736808737724933479105 579552606553293700109329)
                    ·
                      refine ⟨434664454914970275081997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579552606553293700109329 434664454914970275081997)
                      ·
                        rfl

theorem cell23_846506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_846506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846506 prefixEnd_846506 := by exact prefixLift 846506
  have htrace : WordTrace (prefixWord ++ tailWord_846506) baseStart_846506 baseEnd_846506 := by
    simpa [prefixWord, tailWord_846506, baseEnd_846506] using wordTrace_append hprefix tailTrace_846506
  have hstable : (prefixWord ++ tailWord_846506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846506).length < 2 ^ (prefixWord ++ tailWord_846506).sum := by decide
  have hdescent : baseEnd_846506 < baseStart_846506 := by decide
  rcases family_descends (prefixWord ++ tailWord_846506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846511 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 2, 2, 2]
def baseStart_846511 : Nat := 118140960795 + 846511 * 2 ^ 59
def prefixEnd_846511 : Nat := 4983230072969 + 3 ^ 40 * 846511 * 2
def baseEnd_846511 : Nat := 434667022318242755519473

theorem tailTrace_846511 : CollatzResearch.WordTrace tailWord_846511 prefixEnd_846511 434667022318242755519473 := by
  unfold tailWord_846511
  simp only [CollatzResearch.WordTrace]
  refine ⟨30874792636242694413899387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20583195090828462942599591 30874792636242694413899387)
  ·
    refine ⟨46312188954364041620849081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30874792636242694413899387 46312188954364041620849081)
    ·
      refine ⟨34734141715773031215636811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46312188954364041620849081 34734141715773031215636811)
      ·
        refine ⟨52101212573659546823455217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34734141715773031215636811 52101212573659546823455217)
        ·
          refine ⟨39075909430244660117591413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52101212573659546823455217 39075909430244660117591413)
          ·
            refine ⟨3663366509085436886024195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39075909430244660117591413 3663366509085436886024195)
            ·
              refine ⟨5495049763628155329036293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663366509085436886024195 5495049763628155329036293)
              ·
                refine ⟨1030321830680279124194305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5495049763628155329036293 1030321830680279124194305)
                ·
                  refine ⟨772741373010209343145729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1030321830680279124194305 772741373010209343145729)
                  ·
                    refine ⟨579556029757657007359297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 772741373010209343145729 579556029757657007359297)
                    ·
                      refine ⟨434667022318242755519473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579556029757657007359297 434667022318242755519473)
                      ·
                        rfl

theorem cell23_846511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 2, 2].length) (baseStart_846511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846511 prefixEnd_846511 := by exact prefixLift 846511
  have htrace : WordTrace (prefixWord ++ tailWord_846511) baseStart_846511 baseEnd_846511 := by
    simpa [prefixWord, tailWord_846511, baseEnd_846511] using wordTrace_append hprefix tailTrace_846511
  have hstable : (prefixWord ++ tailWord_846511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846511).length < 2 ^ (prefixWord ++ tailWord_846511).sum := by decide
  have hdescent : baseEnd_846511 < baseStart_846511 := by decide
  rcases family_descends (prefixWord ++ tailWord_846511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846520 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_846520 : Nat := 118140960795 + 846520 * 2 ^ 59
def prefixEnd_846520 : Nat := 4983230072969 + 3 ^ 40 * 846520 * 2
def baseEnd_846520 : Nat := 434671643644133220306931

theorem tailTrace_846520 : CollatzResearch.WordTrace tailWord_846520 prefixEnd_846520 434671643644133220306931 := by
  unfold tailWord_846520
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437560446605044475488507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20583413928806725967318009 15437560446605044475488507)
  ·
    refine ⟨23156340669907566713232761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15437560446605044475488507 23156340669907566713232761)
    ·
      refine ⟨17367255502430675034924571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23156340669907566713232761 17367255502430675034924571)
      ·
        refine ⟨26050883253646012552386857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17367255502430675034924571 26050883253646012552386857)
        ·
          refine ⟨19538162440234509414290143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26050883253646012552386857 19538162440234509414290143)
          ·
            refine ⟨29307243660351764121435215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19538162440234509414290143 29307243660351764121435215)
            ·
              refine ⟨43960865490527646182152823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29307243660351764121435215 43960865490527646182152823)
              ·
                refine ⟨65941298235791469273229235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43960865490527646182152823 65941298235791469273229235)
                ·
                  refine ⟨98911947353687203909843853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65941298235791469273229235 98911947353687203909843853)
                  ·
                    refine ⟨37091980257632701466191445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98911947353687203909843853 37091980257632701466191445)
                    ·
                      refine ⟨434671643644133220306931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 37091980257632701466191445 434671643644133220306931)
                      ·
                        rfl

theorem cell23_846520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_846520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846520 prefixEnd_846520 := by exact prefixLift 846520
  have htrace : WordTrace (prefixWord ++ tailWord_846520) baseStart_846520 baseEnd_846520 := by
    simpa [prefixWord, tailWord_846520, baseEnd_846520] using wordTrace_append hprefix tailTrace_846520
  have hstable : (prefixWord ++ tailWord_846520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846520).length < 2 ^ (prefixWord ++ tailWord_846520).sum := by decide
  have hdescent : baseEnd_846520 < baseStart_846520 := by decide
  rcases family_descends (prefixWord ++ tailWord_846520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846527 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 3]
def baseStart_846527 : Nat := 118140960795 + 846527 * 2 ^ 59
def prefixEnd_846527 : Nat := 4983230072969 + 3 ^ 40 * 846527 * 2
def baseEnd_846527 : Nat := 434675238008714692919399

theorem tailTrace_846527 : CollatzResearch.WordTrace tailWord_846527 prefixEnd_846527 434675238008714692919399 := by
  unfold tailWord_846527
  simp only [CollatzResearch.WordTrace]
  refine ⟨30875376204184729146481835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20583584136123152764321223 30875376204184729146481835)
  ·
    refine ⟨46313064306277093719722753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30875376204184729146481835 46313064306277093719722753)
    ·
      refine ⟨34734798229707820289792065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46313064306277093719722753 34734798229707820289792065)
      ·
        refine ⟨26051098672280865217344049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34734798229707820289792065 26051098672280865217344049)
        ·
          refine ⟨19538324004210648913008037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26051098672280865217344049 19538324004210648913008037)
          ·
            refine ⟨3663435750789496671189007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19538324004210648913008037 3663435750789496671189007)
            ·
              refine ⟨5495153626184245006783511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663435750789496671189007 5495153626184245006783511)
              ·
                refine ⟨8242730439276367510175267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495153626184245006783511 8242730439276367510175267)
                ·
                  refine ⟨12364095658914551265262901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8242730439276367510175267 12364095658914551265262901)
                  ·
                    refine ⟨1159133968023239181118397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12364095658914551265262901 1159133968023239181118397)
                    ·
                      refine ⟨434675238008714692919399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1159133968023239181118397 434675238008714692919399)
                      ·
                        rfl

theorem cell23_846527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_846527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846527 prefixEnd_846527 := by exact prefixLift 846527
  have htrace : WordTrace (prefixWord ++ tailWord_846527) baseStart_846527 baseEnd_846527 := by
    simpa [prefixWord, tailWord_846527, baseEnd_846527] using wordTrace_append hprefix tailTrace_846527
  have hstable : (prefixWord ++ tailWord_846527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846527).length < 2 ^ (prefixWord ++ tailWord_846527).sum := by decide
  have hdescent : baseEnd_846527 < baseStart_846527 := by decide
  rcases family_descends (prefixWord ++ tailWord_846527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846584 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 2, 4, 2]
def baseStart_846584 : Nat := 118140960795 + 846584 * 2 ^ 59
def prefixEnd_846584 : Nat := 4983230072969 + 3 ^ 40 * 846584 * 2
def baseEnd_846584 : Nat := 434704506406020969906637

theorem tailTrace_846584 : CollatzResearch.WordTrace tailWord_846584 prefixEnd_846584 434704506406020969906637 := by
  unfold tailWord_846584
  simp only [CollatzResearch.WordTrace]
  refine ⟨15438727582489113940653403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20584970109985485254204537 15438727582489113940653403)
  ·
    refine ⟨23158091373733670910980105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15438727582489113940653403 23158091373733670910980105)
    ·
      refine ⟨17368568530300253183235079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23158091373733670910980105 17368568530300253183235079)
      ·
        refine ⟨26052852795450379774852619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17368568530300253183235079 26052852795450379774852619)
        ·
          refine ⟨39079279193175569662278929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26052852795450379774852619 39079279193175569662278929)
          ·
            refine ⟨29309459394881677246709197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39079279193175569662278929 29309459394881677246709197)
            ·
              refine ⟨10991047273080628967515949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29309459394881677246709197 10991047273080628967515949)
              ·
                refine ⟨4121642727405235862818481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10991047273080628967515949 4121642727405235862818481)
                ·
                  refine ⟨3091232045553926897113861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4121642727405235862818481 3091232045553926897113861)
                  ·
                    refine ⟨579606008541361293208849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3091232045553926897113861 579606008541361293208849)
                    ·
                      refine ⟨434704506406020969906637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579606008541361293208849 434704506406020969906637)
                      ·
                        rfl

theorem cell23_846584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_846584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846584 prefixEnd_846584 := by exact prefixLift 846584
  have htrace : WordTrace (prefixWord ++ tailWord_846584) baseStart_846584 baseEnd_846584 := by
    simpa [prefixWord, tailWord_846584, baseEnd_846584] using wordTrace_append hprefix tailTrace_846584
  have hstable : (prefixWord ++ tailWord_846584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846584).length < 2 ^ (prefixWord ++ tailWord_846584).sum := by decide
  have hdescent : baseEnd_846584 < baseStart_846584 := by decide
  rcases family_descends (prefixWord ++ tailWord_846584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846604 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_846604 : Nat := 118140960795 + 846604 * 2 ^ 59
def prefixEnd_846604 : Nat := 4983230072969 + 3 ^ 40 * 846604 * 2
def baseEnd_846604 : Nat := 434714776019110891656545

theorem tailTrace_846604 : CollatzResearch.WordTrace tailWord_846604 prefixEnd_846604 434714776019110891656545 := by
  unfold tailWord_846604
  simp only [CollatzResearch.WordTrace]
  refine ⟨15439092312452885648517433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20585456416603847531356577 15439092312452885648517433)
  ·
    refine ⟨11579319234339664236388075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15439092312452885648517433 11579319234339664236388075)
    ·
      refine ⟨17368978851509496354582113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11579319234339664236388075 17368978851509496354582113)
      ·
        refine ⟨13026734138632122265936585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17368978851509496354582113 13026734138632122265936585)
        ·
          refine ⟨9770050603974091699452439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13026734138632122265936585 9770050603974091699452439)
          ·
            refine ⟨14655075905961137549178659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9770050603974091699452439 14655075905961137549178659)
            ·
              refine ⟨21982613858941706323767989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14655075905961137549178659 21982613858941706323767989)
              ·
                refine ⟨2060870049275784967853249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21982613858941706323767989 2060870049275784967853249)
                ·
                  refine ⟨1545652536956838725889937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2060870049275784967853249 1545652536956838725889937)
                  ·
                    refine ⟨1159239402717629044417453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1545652536956838725889937 1159239402717629044417453)
                    ·
                      refine ⟨434714776019110891656545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1159239402717629044417453 434714776019110891656545)
                      ·
                        rfl

theorem cell23_846604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_846604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846604 prefixEnd_846604 := by exact prefixLift 846604
  have htrace : WordTrace (prefixWord ++ tailWord_846604) baseStart_846604 baseEnd_846604 := by
    simpa [prefixWord, tailWord_846604, baseEnd_846604] using wordTrace_append hprefix tailTrace_846604
  have hstable : (prefixWord ++ tailWord_846604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846604).length < 2 ^ (prefixWord ++ tailWord_846604).sum := by decide
  have hdescent : baseEnd_846604 < baseStart_846604 := by decide
  rcases family_descends (prefixWord ++ tailWord_846604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846628 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_846628 : Nat := 118140960795 + 846628 * 2 ^ 59
def prefixEnd_846628 : Nat := 4983230072969 + 3 ^ 40 * 846628 * 2
def baseEnd_846628 : Nat := 144909033184939599252145

theorem tailTrace_846628 : CollatzResearch.WordTrace tailWord_846628 prefixEnd_846628 144909033184939599252145 := by
  unfold tailWord_846628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15439529988409411697954269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20586039984545882263939025 15439529988409411697954269)
  ·
    refine ⟨5789823745653529386732851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15439529988409411697954269 5789823745653529386732851)
    ·
      refine ⟨8684735618480294080099277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5789823745653529386732851 8684735618480294080099277)
      ·
        refine ⟨3256775856930110280037229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8684735618480294080099277 3256775856930110280037229)
        ·
          refine ⟨1221290946348791355013961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3256775856930110280037229 1221290946348791355013961)
          ·
            refine ⟨915968209761593516260471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1221290946348791355013961 915968209761593516260471)
            ·
              refine ⟨1373952314642390274390707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915968209761593516260471 1373952314642390274390707)
              ·
                refine ⟨2060928471963585411586061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373952314642390274390707 2060928471963585411586061)
                ·
                  refine ⟨772848176986344529344773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2060928471963585411586061 772848176986344529344773)
                  ·
                    refine ⟨144909033184939599252145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 772848176986344529344773 144909033184939599252145)
                    ·
                      rfl

theorem cell23_846628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_846628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846628 prefixEnd_846628 := by exact prefixLift 846628
  have htrace : WordTrace (prefixWord ++ tailWord_846628) baseStart_846628 baseEnd_846628 := by
    simpa [prefixWord, tailWord_846628, baseEnd_846628] using wordTrace_append hprefix tailTrace_846628
  have hstable : (prefixWord ++ tailWord_846628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846628).length < 2 ^ (prefixWord ++ tailWord_846628).sum := by decide
  have hdescent : baseEnd_846628 < baseStart_846628 := by decide
  rcases family_descends (prefixWord ++ tailWord_846628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846704 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_846704 : Nat := 118140960795 + 846704 * 2 ^ 59
def prefixEnd_846704 : Nat := 4983230072969 + 3 ^ 40 * 846704 * 2
def baseEnd_846704 : Nat := 434766124084560500406085

theorem tailTrace_846704 : CollatzResearch.WordTrace tailWord_846704 prefixEnd_846704 434766124084560500406085 := by
  unfold tailWord_846704
  simp only [CollatzResearch.WordTrace]
  refine ⟨15440915962271744187837583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20587887949695658917116777 15440915962271744187837583)
  ·
    refine ⟨23161373943407616281756375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15440915962271744187837583 23161373943407616281756375)
    ·
      refine ⟨34742060915111424422634563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23161373943407616281756375 34742060915111424422634563)
      ·
        refine ⟨52113091372667136633951845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34742060915111424422634563 52113091372667136633951845)
        ·
          refine ⟨9771204632375088118865971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52113091372667136633951845 9771204632375088118865971)
          ·
            refine ⟨14656806948562632178298957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9771204632375088118865971 14656806948562632178298957)
            ·
              refine ⟨5496302605710987066862109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14656806948562632178298957 5496302605710987066862109)
              ·
                refine ⟨2061113477141620150073291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5496302605710987066862109 2061113477141620150073291)
                ·
                  refine ⟨3091670215712430225109937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061113477141620150073291 3091670215712430225109937)
                  ·
                    refine ⟨2318752661784322668832453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3091670215712430225109937 2318752661784322668832453)
                    ·
                      refine ⟨434766124084560500406085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2318752661784322668832453 434766124084560500406085)
                      ·
                        rfl

theorem cell23_846704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_846704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846704 prefixEnd_846704 := by exact prefixLift 846704
  have htrace : WordTrace (prefixWord ++ tailWord_846704) baseStart_846704 baseEnd_846704 := by
    simpa [prefixWord, tailWord_846704, baseEnd_846704] using wordTrace_append hprefix tailTrace_846704
  have hstable : (prefixWord ++ tailWord_846704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846704).length < 2 ^ (prefixWord ++ tailWord_846704).sum := by decide
  have hdescent : baseEnd_846704 < baseStart_846704 := by decide
  rcases family_descends (prefixWord ++ tailWord_846704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846725 : List Nat := [1, 3, 1, 1, 3, 3, 1, 5, 1, 2, 2]
def baseStart_846725 : Nat := 118140960795 + 846725 * 2 ^ 59
def prefixEnd_846725 : Nat := 4983230072969 + 3 ^ 40 * 846725 * 2
def baseEnd_846725 : Nat := 434776907178304918243489

theorem tailTrace_846725 : CollatzResearch.WordTrace tailWord_846725 prefixEnd_846725 434776907178304918243489 := by
  unfold tailWord_846725
  simp only [CollatzResearch.WordTrace]
  refine ⟨30882597857467408962189629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20588398571644939308126419 30882597857467408962189629)
  ·
    refine ⟨11580974196550278360821111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30882597857467408962189629 11580974196550278360821111)
    ·
      refine ⟨17371461294825417541231667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11580974196550278360821111 17371461294825417541231667)
      ·
        refine ⟨26057191942238126311847501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17371461294825417541231667 26057191942238126311847501)
        ·
          refine ⟨9771446978339297366942813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26057191942238126311847501 9771446978339297366942813)
          ·
            refine ⟨3664292616877236512603555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9771446978339297366942813 3664292616877236512603555)
            ·
              refine ⟨5496438925315854768905333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664292616877236512603555 5496438925315854768905333)
              ·
                refine ⟨515291149248361384584875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5496438925315854768905333 515291149248361384584875)
                ·
                  refine ⟨772936723872542076877313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515291149248361384584875 772936723872542076877313)
                  ·
                    refine ⟨579702542904406557657985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 772936723872542076877313 579702542904406557657985)
                    ·
                      refine ⟨434776907178304918243489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579702542904406557657985 434776907178304918243489)
                      ·
                        rfl

theorem cell23_846725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_846725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846725 prefixEnd_846725 := by exact prefixLift 846725
  have htrace : WordTrace (prefixWord ++ tailWord_846725) baseStart_846725 baseEnd_846725 := by
    simpa [prefixWord, tailWord_846725, baseEnd_846725] using wordTrace_append hprefix tailTrace_846725
  have hstable : (prefixWord ++ tailWord_846725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846725).length < 2 ^ (prefixWord ++ tailWord_846725).sum := by decide
  have hdescent : baseEnd_846725 < baseStart_846725 := by decide
  rcases family_descends (prefixWord ++ tailWord_846725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846728 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_846728 : Nat := 118140960795 + 846728 * 2 ^ 59
def prefixEnd_846728 : Nat := 4983230072969 + 3 ^ 40 * 846728 * 2
def baseEnd_846728 : Nat := 434778447620268406505975

theorem tailTrace_846728 : CollatzResearch.WordTrace tailWord_846728 prefixEnd_846728 434778447620268406505975 := by
  unfold tailWord_846728
  simp only [CollatzResearch.WordTrace]
  refine ⟨15441353638228270237274419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20588471517637693649699225 15441353638228270237274419)
  ·
    refine ⟨23162030457342405355911629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15441353638228270237274419 23162030457342405355911629)
    ·
      refine ⟨8685761421503402008466861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23162030457342405355911629 8685761421503402008466861)
      ·
        refine ⟨3257160533063775753175073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8685761421503402008466861 3257160533063775753175073)
        ·
          refine ⟨2442870399797831814881305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257160533063775753175073 2442870399797831814881305)
          ·
            refine ⟨1832152799848373861160979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442870399797831814881305 1832152799848373861160979)
            ·
              refine ⟨2748229199772560791741469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832152799848373861160979 2748229199772560791741469)
              ·
                refine ⟨1030585949914710296903051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2748229199772560791741469 1030585949914710296903051)
                ·
                  refine ⟨1545878924872065445354577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030585949914710296903051 1545878924872065445354577)
                  ·
                    refine ⟨1159409193654049084015933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1545878924872065445354577 1159409193654049084015933)
                    ·
                      refine ⟨434778447620268406505975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1159409193654049084015933 434778447620268406505975)
                      ·
                        rfl

theorem cell23_846728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_846728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846728 prefixEnd_846728 := by exact prefixLift 846728
  have htrace : WordTrace (prefixWord ++ tailWord_846728) baseStart_846728 baseEnd_846728 := by
    simpa [prefixWord, tailWord_846728, baseEnd_846728] using wordTrace_append hprefix tailTrace_846728
  have hstable : (prefixWord ++ tailWord_846728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846728).length < 2 ^ (prefixWord ++ tailWord_846728).sum := by decide
  have hdescent : baseEnd_846728 < baseStart_846728 := by decide
  rcases family_descends (prefixWord ++ tailWord_846728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846765 : List Nat := [1, 5, 2, 3, 1, 2, 2, 7]
def baseStart_846765 : Nat := 118140960795 + 846765 * 2 ^ 59
def prefixEnd_846765 : Nat := 4983230072969 + 3 ^ 40 * 846765 * 2
def baseEnd_846765 : Nat := 16103609126092028212715

theorem tailTrace_846765 : CollatzResearch.WordTrace tailWord_846765 prefixEnd_846765 16103609126092028212715 := by
  unfold tailWord_846765
  simp only [CollatzResearch.WordTrace]
  refine ⟨30884056777322495793645749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20589371184881663862430499 30884056777322495793645749)
  ·
    refine ⟨2895380322873983980654289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30884056777322495793645749 2895380322873983980654289)
    ·
      refine ⟨2171535242155487985490717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2895380322873983980654289 2171535242155487985490717)
      ·
        refine ⟨814325715808307994559019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2171535242155487985490717 814325715808307994559019)
        ·
          refine ⟨1221488573712461991838529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814325715808307994559019 1221488573712461991838529)
          ·
            refine ⟨916116430284346493878897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1221488573712461991838529 916116430284346493878897)
            ·
              refine ⟨687087322713259870409173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916116430284346493878897 687087322713259870409173)
              ·
                refine ⟨16103609126092028212715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 687087322713259870409173 16103609126092028212715)
                ·
                  rfl

theorem cell23_846765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 7].length) (baseStart_846765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846765 prefixEnd_846765 := by exact prefixLift 846765
  have htrace : WordTrace (prefixWord ++ tailWord_846765) baseStart_846765 baseEnd_846765 := by
    simpa [prefixWord, tailWord_846765, baseEnd_846765] using wordTrace_append hprefix tailTrace_846765
  have hstable : (prefixWord ++ tailWord_846765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846765).length < 2 ^ (prefixWord ++ tailWord_846765).sum := by decide
  have hdescent : baseEnd_846765 < baseStart_846765 := by decide
  rcases family_descends (prefixWord ++ tailWord_846765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846784 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_846784 : Nat := 118140960795 + 846784 * 2 ^ 59
def prefixEnd_846784 : Nat := 4983230072969 + 3 ^ 40 * 846784 * 2
def baseEnd_846784 : Nat := 434807202536920187405717

theorem tailTrace_846784 : CollatzResearch.WordTrace tailWord_846784 prefixEnd_846784 434807202536920187405717 := by
  unfold tailWord_846784
  simp only [CollatzResearch.WordTrace]
  refine ⟨15442374882126831019293703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20589833176169108025724937 15442374882126831019293703)
  ·
    refine ⟨23163562323190246528940555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15442374882126831019293703 23163562323190246528940555)
    ·
      refine ⟨34745343484785369793410833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23163562323190246528940555 34745343484785369793410833)
      ·
        refine ⟨26059007613589027345058125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34745343484785369793410833 26059007613589027345058125)
        ·
          refine ⟨9772127855095885254396797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26059007613589027345058125 9772127855095885254396797)
          ·
            refine ⟨3664547945660956970398799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9772127855095885254396797 3664547945660956970398799)
            ·
              refine ⟨5496821918491435455598199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664547945660956970398799 5496821918491435455598199)
              ·
                refine ⟨8245232877737153183397299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5496821918491435455598199 8245232877737153183397299)
                ·
                  refine ⟨12367849316605729775095949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8245232877737153183397299 12367849316605729775095949)
                  ·
                    refine ⟨4637943493727148665660981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12367849316605729775095949 4637943493727148665660981)
                    ·
                      refine ⟨434807202536920187405717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4637943493727148665660981 434807202536920187405717)
                      ·
                        rfl

theorem cell23_846784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_846784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846784 prefixEnd_846784 := by exact prefixLift 846784
  have htrace : WordTrace (prefixWord ++ tailWord_846784) baseStart_846784 baseEnd_846784 := by
    simpa [prefixWord, tailWord_846784, baseEnd_846784] using wordTrace_append hprefix tailTrace_846784
  have hstable : (prefixWord ++ tailWord_846784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846784).length < 2 ^ (prefixWord ++ tailWord_846784).sum := by decide
  have hdescent : baseEnd_846784 < baseStart_846784 := by decide
  rcases family_descends (prefixWord ++ tailWord_846784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846818 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_846818 : Nat := 118140960795 + 846818 * 2 ^ 59
def prefixEnd_846818 : Nat := 4983230072969 + 3 ^ 40 * 846818 * 2
def baseEnd_846818 : Nat := 434824660879173054380561

theorem tailTrace_846818 : CollatzResearch.WordTrace tailWord_846818 prefixEnd_846818 434824660879173054380561 := by
  unfold tailWord_846818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721497461532621461331277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20590659897420323896883405 7721497461532621461331277)
  ·
    refine ⟨2895561548074733047999229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7721497461532621461331277 2895561548074733047999229)
    ·
      refine ⟨1085835580528024892999711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2895561548074733047999229 1085835580528024892999711)
      ·
        refine ⟨1628753370792037339499567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085835580528024892999711 1628753370792037339499567)
        ·
          refine ⟨2443130056188056009249351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628753370792037339499567 2443130056188056009249351)
          ·
            refine ⟨3664695084282084013874027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443130056188056009249351 3664695084282084013874027)
            ·
              refine ⟨5497042626423126020811041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664695084282084013874027 5497042626423126020811041)
              ·
                refine ⟨4122781969817344515608281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5497042626423126020811041 4122781969817344515608281)
                ·
                  refine ⟨3092086477363008386706211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122781969817344515608281 3092086477363008386706211)
                  ·
                    refine ⟨4638129716044512580059317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3092086477363008386706211 4638129716044512580059317)
                    ·
                      refine ⟨434824660879173054380561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4638129716044512580059317 434824660879173054380561)
                      ·
                        rfl

theorem cell23_846818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_846818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846818 prefixEnd_846818 := by exact prefixLift 846818
  have htrace : WordTrace (prefixWord ++ tailWord_846818) baseStart_846818 baseEnd_846818 := by
    simpa [prefixWord, tailWord_846818, baseEnd_846818] using wordTrace_append hprefix tailTrace_846818
  have hstable : (prefixWord ++ tailWord_846818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846818).length < 2 ^ (prefixWord ++ tailWord_846818).sum := by decide
  have hdescent : baseEnd_846818 < baseStart_846818 := by decide
  rcases family_descends (prefixWord ++ tailWord_846818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846858 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_846858 : Nat := 118140960795 + 846858 * 2 ^ 59
def prefixEnd_846858 : Nat := 4983230072969 + 3 ^ 40 * 846858 * 2
def baseEnd_846858 : Nat := 434845200105352897880377

theorem tailTrace_846858 : CollatzResearch.WordTrace tailWord_846858 prefixEnd_846858 434845200105352897880377 := by
  unfold tailWord_846858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721862191496393169195307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20591632510657048451187485 7721862191496393169195307)
  ·
    refine ⟨11582793287244589753792961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7721862191496393169195307 11582793287244589753792961)
    ·
      refine ⟨8687094965433442315344721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11582793287244589753792961 8687094965433442315344721)
      ·
        refine ⟨6515321224075081736508541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8687094965433442315344721 6515321224075081736508541)
        ·
          refine ⟨2443245459028155651190703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6515321224075081736508541 2443245459028155651190703)
          ·
            refine ⟨3664868188542233476786055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443245459028155651190703 3664868188542233476786055)
            ·
              refine ⟨5497302282813350215179083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664868188542233476786055 5497302282813350215179083)
              ·
                refine ⟨8245953424220025322768625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5497302282813350215179083 8245953424220025322768625)
                ·
                  refine ⟨6184465068165018992076469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8245953424220025322768625 6184465068165018992076469)
                  ·
                    refine ⟨579793600140470530507169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6184465068165018992076469 579793600140470530507169)
                    ·
                      refine ⟨434845200105352897880377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579793600140470530507169 434845200105352897880377)
                      ·
                        rfl

theorem cell23_846858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_846858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846858 prefixEnd_846858 := by exact prefixLift 846858
  have htrace : WordTrace (prefixWord ++ tailWord_846858) baseStart_846858 baseEnd_846858 := by
    simpa [prefixWord, tailWord_846858, baseEnd_846858] using wordTrace_append hprefix tailTrace_846858
  have hstable : (prefixWord ++ tailWord_846858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846858).length < 2 ^ (prefixWord ++ tailWord_846858).sum := by decide
  have hdescent : baseEnd_846858 < baseStart_846858 := by decide
  rcases family_descends (prefixWord ++ tailWord_846858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846891 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 3]
def baseStart_846891 : Nat := 118140960795 + 846891 * 2 ^ 59
def prefixEnd_846891 : Nat := 4983230072969 + 3 ^ 40 * 846891 * 2
def baseEnd_846891 : Nat := 434862144966951268767725

theorem tailTrace_846891 : CollatzResearch.WordTrace tailWord_846891 prefixEnd_846891 434862144966951268767725 := by
  unfold tailWord_846891
  simp only [CollatzResearch.WordTrace]
  refine ⟨30888652374866019312732527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20592434916577346208488351 30888652374866019312732527)
  ·
    refine ⟨46332978562299028969098791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30888652374866019312732527 46332978562299028969098791)
    ·
      refine ⟨69499467843448543453648187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46332978562299028969098791 69499467843448543453648187)
      ·
        refine ⟨104249201765172815180472281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69499467843448543453648187 104249201765172815180472281)
        ·
          refine ⟨78186901323879611385354211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104249201765172815180472281 78186901323879611385354211)
          ·
            refine ⟨117280351985819417078031317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78186901323879611385354211 117280351985819417078031317)
            ·
              refine ⟨2748758249667642587766359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 117280351985819417078031317 2748758249667642587766359)
              ·
                refine ⟨4123137374501463881649539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748758249667642587766359 4123137374501463881649539)
                ·
                  refine ⟨6184706061752195822474309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123137374501463881649539 6184706061752195822474309)
                  ·
                    refine ⟨1159632386578536716713933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184706061752195822474309 1159632386578536716713933)
                    ·
                      refine ⟨434862144966951268767725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1159632386578536716713933 434862144966951268767725)
                      ·
                        rfl

theorem cell23_846891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 3].length) (baseStart_846891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846891 prefixEnd_846891 := by exact prefixLift 846891
  have htrace : WordTrace (prefixWord ++ tailWord_846891) baseStart_846891 baseEnd_846891 := by
    simpa [prefixWord, tailWord_846891, baseEnd_846891] using wordTrace_append hprefix tailTrace_846891
  have hstable : (prefixWord ++ tailWord_846891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846891).length < 2 ^ (prefixWord ++ tailWord_846891).sum := by decide
  have hdescent : baseEnd_846891 < baseStart_846891 := by decide
  rcases family_descends (prefixWord ++ tailWord_846891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846938 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_846938 : Nat := 118140960795 + 846938 * 2 ^ 59
def prefixEnd_846938 : Nat := 4983230072969 + 3 ^ 40 * 846938 * 2
def baseEnd_846938 : Nat := 434886278557712584880009

theorem tailTrace_846938 : CollatzResearch.WordTrace tailWord_846938 prefixEnd_846938 434886278557712584880009 := by
  unfold tailWord_846938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722591651423936584923367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20593577737130497559795645 7722591651423936584923367)
  ·
    refine ⟨11583887477135904877385051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7722591651423936584923367 11583887477135904877385051)
    ·
      refine ⟨17375831215703857316077577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583887477135904877385051 17375831215703857316077577)
      ·
        refine ⟨13031873411777892987058183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17375831215703857316077577 13031873411777892987058183)
        ·
          refine ⟨19547810117666839480587275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13031873411777892987058183 19547810117666839480587275)
          ·
            refine ⟨29321715176500259220880913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19547810117666839480587275 29321715176500259220880913)
            ·
              refine ⟨21991286382375194415660685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29321715176500259220880913 21991286382375194415660685)
              ·
                refine ⟨8246732393390697905872757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21991286382375194415660685 8246732393390697905872757)
                ·
                  refine ⟨773131161880377928675571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8246732393390697905872757 773131161880377928675571)
                  ·
                    refine ⟨1159696742820566893013357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 773131161880377928675571 1159696742820566893013357)
                    ·
                      refine ⟨434886278557712584880009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1159696742820566893013357 434886278557712584880009)
                      ·
                        rfl

theorem cell23_846938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_846938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846938 prefixEnd_846938 := by exact prefixLift 846938
  have htrace : WordTrace (prefixWord ++ tailWord_846938) baseStart_846938 baseEnd_846938 := by
    simpa [prefixWord, tailWord_846938, baseEnd_846938] using wordTrace_append hprefix tailTrace_846938
  have hstable : (prefixWord ++ tailWord_846938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846938).length < 2 ^ (prefixWord ++ tailWord_846938).sum := by decide
  have hdescent : baseEnd_846938 < baseStart_846938 := by decide
  rcases family_descends (prefixWord ++ tailWord_846938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846942 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_846942 : Nat := 118140960795 + 846942 * 2 ^ 59
def prefixEnd_846942 : Nat := 4983230072969 + 3 ^ 40 * 846942 * 2
def baseEnd_846942 : Nat := 434888332480330569229991

theorem tailTrace_846942 : CollatzResearch.WordTrace tailWord_846942 prefixEnd_846942 434888332480330569229991 := by
  unfold tailWord_846942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861314062210156877854885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20593674998454170015226053 3861314062210156877854885)
  ·
    refine ⟨723996386664404414597791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3861314062210156877854885 723996386664404414597791)
    ·
      refine ⟨1085994579996606621896687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723996386664404414597791 1085994579996606621896687)
      ·
        refine ⟨1628991869994909932845031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085994579996606621896687 1628991869994909932845031)
        ·
          refine ⟨2443487804992364899267547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628991869994909932845031 2443487804992364899267547)
          ·
            refine ⟨3665231707488547348901321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443487804992364899267547 3665231707488547348901321)
            ·
              refine ⟨2748923780616410511675991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3665231707488547348901321 2748923780616410511675991)
              ·
                refine ⟨4123385670924615767513987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748923780616410511675991 4123385670924615767513987)
                ·
                  refine ⟨6185078506386923651270981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123385670924615767513987 6185078506386923651270981)
                  ·
                    refine ⟨1159702219947548184613309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6185078506386923651270981 1159702219947548184613309)
                    ·
                      refine ⟨434888332480330569229991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1159702219947548184613309 434888332480330569229991)
                      ·
                        rfl

theorem cell23_846942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_846942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846942 prefixEnd_846942 := by exact prefixLift 846942
  have htrace : WordTrace (prefixWord ++ tailWord_846942) baseStart_846942 baseEnd_846942 := by
    simpa [prefixWord, tailWord_846942, baseEnd_846942] using wordTrace_append hprefix tailTrace_846942
  have hstable : (prefixWord ++ tailWord_846942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846942).length < 2 ^ (prefixWord ++ tailWord_846942).sum := by decide
  have hdescent : baseEnd_846942 < baseStart_846942 := by decide
  rcases family_descends (prefixWord ++ tailWord_846942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846995 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 3, 2, 2]
def baseStart_846995 : Nat := 118140960795 + 846995 * 2 ^ 59
def prefixEnd_846995 : Nat := 4983230072969 + 3 ^ 40 * 846995 * 2
def baseEnd_846995 : Nat := 434915546955018861867247

theorem tailTrace_846995 : CollatzResearch.WordTrace tailWord_846995 prefixEnd_846995 434915546955018861867247 := by
  unfold tailWord_846995
  simp only [CollatzResearch.WordTrace]
  refine ⟨30892445566489245074518439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20594963710992830049678959 30892445566489245074518439)
  ·
    refine ⟨46338668349733867611777659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30892445566489245074518439 46338668349733867611777659)
    ·
      refine ⟨69508002524600801417666489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46338668349733867611777659 69508002524600801417666489)
      ·
        refine ⟨52131001893450601063249867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69508002524600801417666489 52131001893450601063249867)
        ·
          refine ⟨78196502840175901594874801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52131001893450601063249867 78196502840175901594874801)
          ·
            refine ⟨58647377130131926196156101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78196502840175901594874801 58647377130131926196156101)
            ·
              refine ⟨10996383211899736161779269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58647377130131926196156101 10996383211899736161779269)
              ·
                refine ⟨2061821852231200530333613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10996383211899736161779269 2061821852231200530333613)
                ·
                  refine ⟨773183194586700198875105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2061821852231200530333613 773183194586700198875105)
                  ·
                    refine ⟨579887395940025149156329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 773183194586700198875105 579887395940025149156329)
                    ·
                      refine ⟨434915546955018861867247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579887395940025149156329 434915546955018861867247)
                      ·
                        rfl

theorem cell23_846995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 2, 2].length) (baseStart_846995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_846995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_846995 prefixEnd_846995 := by exact prefixLift 846995
  have htrace : WordTrace (prefixWord ++ tailWord_846995) baseStart_846995 baseEnd_846995 := by
    simpa [prefixWord, tailWord_846995, baseEnd_846995] using wordTrace_append hprefix tailTrace_846995
  have hstable : (prefixWord ++ tailWord_846995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846995).length < 2 ^ (prefixWord ++ tailWord_846995).sum := by decide
  have hdescent : baseEnd_846995 < baseStart_846995 := by decide
  rcases family_descends (prefixWord ++ tailWord_846995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847008 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_847008 : Nat := 118140960795 + 847008 * 2 ^ 59
def prefixEnd_847008 : Nat := 4983230072969 + 3 ^ 40 * 847008 * 2
def baseEnd_847008 : Nat := 434922222203527311004687

theorem tailTrace_847008 : CollatzResearch.WordTrace tailWord_847008 prefixEnd_847008 434922222203527311004687 := by
  unfold tailWord_847008
  simp only [CollatzResearch.WordTrace]
  refine ⟨15446459857721074147370839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20595279810294765529827785 15446459857721074147370839)
  ·
    refine ⟨23169689786581611221056259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15446459857721074147370839 23169689786581611221056259)
    ·
      refine ⟨34754534679872416831584389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23169689786581611221056259 34754534679872416831584389)
      ·
        refine ⟨6516475252476078155922073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34754534679872416831584389 6516475252476078155922073)
        ·
          refine ⟨4887356439357058616941555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6516475252476078155922073 4887356439357058616941555)
          ·
            refine ⟨7331034659035587925412333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887356439357058616941555 7331034659035587925412333)
            ·
              refine ⟨2749137997138345472029625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7331034659035587925412333 2749137997138345472029625)
              ·
                refine ⟨2061853497853759104022219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2749137997138345472029625 2061853497853759104022219)
                ·
                  refine ⟨3092780246780638656033329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061853497853759104022219 3092780246780638656033329)
                  ·
                    refine ⟨2319585185085478992024997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3092780246780638656033329 2319585185085478992024997)
                    ·
                      refine ⟨434922222203527311004687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2319585185085478992024997 434922222203527311004687)
                      ·
                        rfl

theorem cell23_847008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_847008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847008 prefixEnd_847008 := by exact prefixLift 847008
  have htrace : WordTrace (prefixWord ++ tailWord_847008) baseStart_847008 baseEnd_847008 := by
    simpa [prefixWord, tailWord_847008, baseEnd_847008] using wordTrace_append hprefix tailTrace_847008
  have hstable : (prefixWord ++ tailWord_847008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847008).length < 2 ^ (prefixWord ++ tailWord_847008).sum := by decide
  have hdescent : baseEnd_847008 < baseStart_847008 := by decide
  rcases family_descends (prefixWord ++ tailWord_847008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847012 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_847012 : Nat := 118140960795 + 847012 * 2 ^ 59
def prefixEnd_847012 : Nat := 4983230072969 + 3 ^ 40 * 847012 * 2
def baseEnd_847012 : Nat := 434924276126145295354669

theorem tailTrace_847012 : CollatzResearch.WordTrace tailWord_847012 prefixEnd_847012 434924276126145295354669 := by
  unfold tailWord_847012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15446532803713828488943645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20595377071618437985258193 15446532803713828488943645)
  ·
    refine ⟨5792449801392685683353867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15446532803713828488943645 5792449801392685683353867)
    ·
      refine ⟨8688674702089028525030801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5792449801392685683353867 8688674702089028525030801)
      ·
        refine ⟨6516506026566771393773101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8688674702089028525030801 6516506026566771393773101)
        ·
          refine ⟨2443689759962539272664913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6516506026566771393773101 2443689759962539272664913)
          ·
            refine ⟨1832767319971904454498685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2443689759962539272664913 1832767319971904454498685)
            ·
              refine ⟨687287744989464170437007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1832767319971904454498685 687287744989464170437007)
              ·
                refine ⟨1030931617484196255655511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687287744989464170437007 1030931617484196255655511)
                ·
                  refine ⟨1546397426226294383483267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030931617484196255655511 1546397426226294383483267)
                  ·
                    refine ⟨2319596139339441575224901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1546397426226294383483267 2319596139339441575224901)
                    ·
                      refine ⟨434924276126145295354669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2319596139339441575224901 434924276126145295354669)
                      ·
                        rfl

theorem cell23_847012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_847012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847012 prefixEnd_847012 := by exact prefixLift 847012
  have htrace : WordTrace (prefixWord ++ tailWord_847012) baseStart_847012 baseEnd_847012 := by
    simpa [prefixWord, tailWord_847012, baseEnd_847012] using wordTrace_append hprefix tailTrace_847012
  have hstable : (prefixWord ++ tailWord_847012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847012).length < 2 ^ (prefixWord ++ tailWord_847012).sum := by decide
  have hdescent : baseEnd_847012 < baseStart_847012 := by decide
  rcases family_descends (prefixWord ++ tailWord_847012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847015 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_847015 : Nat := 118140960795 + 847015 * 2 ^ 59
def prefixEnd_847015 : Nat := 4983230072969 + 3 ^ 40 * 847015 * 2
def baseEnd_847015 : Nat := 434925816568108783617155

theorem tailTrace_847015 : CollatzResearch.WordTrace tailWord_847015 prefixEnd_847015 434925816568108783617155 := by
  unfold tailWord_847015
  simp only [CollatzResearch.WordTrace]
  refine ⟨30893175026416788490246499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20595450017611192326830999 30893175026416788490246499)
  ·
    refine ⟨46339762539625182735369749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30893175026416788490246499 46339762539625182735369749)
    ·
      refine ⟨2172176369044930440720457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46339762539625182735369749 2172176369044930440720457)
      ·
        refine ⟨1629132276783697830540343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2172176369044930440720457 1629132276783697830540343)
        ·
          refine ⟨2443698415175546745810515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629132276783697830540343 2443698415175546745810515)
          ·
            refine ⟨3665547622763320118715773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443698415175546745810515 3665547622763320118715773)
            ·
              refine ⟨1374580358536245044518415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3665547622763320118715773 1374580358536245044518415)
              ·
                refine ⟨2061870537804367566777623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374580358536245044518415 2061870537804367566777623)
                ·
                  refine ⟨3092805806706551350166435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061870537804367566777623 3092805806706551350166435)
                  ·
                    refine ⟨4639208710059827025249653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3092805806706551350166435 4639208710059827025249653)
                    ·
                      refine ⟨434925816568108783617155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4639208710059827025249653 434925816568108783617155)
                      ·
                        rfl

theorem cell23_847015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_847015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847015 prefixEnd_847015 := by exact prefixLift 847015
  have htrace : WordTrace (prefixWord ++ tailWord_847015) baseStart_847015 baseEnd_847015 := by
    simpa [prefixWord, tailWord_847015, baseEnd_847015] using wordTrace_append hprefix tailTrace_847015
  have hstable : (prefixWord ++ tailWord_847015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847015).length < 2 ^ (prefixWord ++ tailWord_847015).sum := by decide
  have hdescent : baseEnd_847015 < baseStart_847015 := by decide
  rcases family_descends (prefixWord ++ tailWord_847015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847018 : List Nat := [3, 1, 5, 1, 1, 12]
def baseStart_847018 : Nat := 118140960795 + 847018 * 2 ^ 59
def prefixEnd_847018 : Nat := 4983230072969 + 3 ^ 40 * 847018 * 2
def baseEnd_847018 : Nat := 1789824514444741859587

theorem tailTrace_847018 : CollatzResearch.WordTrace tailWord_847018 prefixEnd_847018 1789824514444741859587 := by
  unfold tailWord_847018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7723321111351480000651427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20595522963603946668403805 7723321111351480000651427)
  ·
    refine ⟨11584981667027220000977141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7723321111351480000651427 11584981667027220000977141)
    ·
      refine ⟨1086092031283801875091607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11584981667027220000977141 1086092031283801875091607)
      ·
        refine ⟨1629138046925702812637411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086092031283801875091607 1629138046925702812637411)
        ·
          refine ⟨2443707070388554218956117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629138046925702812637411 2443707070388554218956117)
          ·
            refine ⟨1789824514444741859587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2443707070388554218956117 1789824514444741859587)
            ·
              rfl

theorem cell23_847018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 12].length) (baseStart_847018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847018 prefixEnd_847018 := by exact prefixLift 847018
  have htrace : WordTrace (prefixWord ++ tailWord_847018) baseStart_847018 baseEnd_847018 := by
    simpa [prefixWord, tailWord_847018, baseEnd_847018] using wordTrace_append hprefix tailTrace_847018
  have hstable : (prefixWord ++ tailWord_847018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847018).length < 2 ^ (prefixWord ++ tailWord_847018).sum := by decide
  have hdescent : baseEnd_847018 < baseStart_847018 := by decide
  rcases family_descends (prefixWord ++ tailWord_847018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847031 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 1, 9]
def baseStart_847031 : Nat := 118140960795 + 847031 * 2 ^ 59
def prefixEnd_847031 : Nat := 4983230072969 + 3 ^ 40 * 847031 * 2
def baseEnd_847031 : Nat := 144978010752860240339027

theorem tailTrace_847031 : CollatzResearch.WordTrace tailWord_847031 prefixEnd_847031 144978010752860240339027 := by
  unfold tailWord_847031
  simp only [CollatzResearch.WordTrace]
  refine ⟨30893758594358823222828947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20595839062905882148552631 30893758594358823222828947)
  ·
    refine ⟨46340637891538234834243421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30893758594358823222828947 46340637891538234834243421)
    ·
      refine ⟨17377739209326838062841283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46340637891538234834243421 17377739209326838062841283)
      ·
        refine ⟨26066608813990257094261925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17377739209326838062841283 26066608813990257094261925)
        ·
          refine ⟨4887489152623173205174111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26066608813990257094261925 4887489152623173205174111)
          ·
            refine ⟨7331233728934759807761167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887489152623173205174111 7331233728934759807761167)
            ·
              refine ⟨10996850593402139711641751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331233728934759807761167 10996850593402139711641751)
              ·
                refine ⟨16495275890103209567462627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10996850593402139711641751 16495275890103209567462627)
                ·
                  refine ⟨24742913835154814351193941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16495275890103209567462627 24742913835154814351193941)
                  ·
                    refine ⟨144978010752860240339027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 24742913835154814351193941 144978010752860240339027)
                    ·
                      rfl

theorem cell23_847031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_847031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847031 prefixEnd_847031 := by exact prefixLift 847031
  have htrace : WordTrace (prefixWord ++ tailWord_847031) baseStart_847031 baseEnd_847031 := by
    simpa [prefixWord, tailWord_847031, baseEnd_847031] using wordTrace_append hprefix tailTrace_847031
  have hstable : (prefixWord ++ tailWord_847031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847031).length < 2 ^ (prefixWord ++ tailWord_847031).sum := by decide
  have hdescent : baseEnd_847031 < baseStart_847031 := by decide
  rcases family_descends (prefixWord ++ tailWord_847031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847058 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_847058 : Nat := 118140960795 + 847058 * 2 ^ 59
def prefixEnd_847058 : Nat := 4983230072969 + 3 ^ 40 * 847058 * 2
def baseEnd_847058 : Nat := 434947896236252115379457

theorem tailTrace_847058 : CollatzResearch.WordTrace tailWord_847058 prefixEnd_847058 434947896236252115379457 := by
  unfold tailWord_847058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7723685841315251708515457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20596495576840671222707885 7723685841315251708515457)
  ·
    refine ⟨5792764380986438781386593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7723685841315251708515457 5792764380986438781386593)
    ·
      refine ⟨4344573285739829086039945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5792764380986438781386593 4344573285739829086039945)
      ·
        refine ⟨3258429964304871814529959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4344573285739829086039945 3258429964304871814529959)
        ·
          refine ⟨4887644946457307721794939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3258429964304871814529959 4887644946457307721794939)
          ·
            refine ⟨7331467419685961582692409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887644946457307721794939 7331467419685961582692409)
            ·
              refine ⟨5498600564764471187019307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7331467419685961582692409 5498600564764471187019307)
              ·
                refine ⟨8247900847146706780528961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498600564764471187019307 8247900847146706780528961)
                ·
                  refine ⟨6185925635360030085396721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8247900847146706780528961 6185925635360030085396721)
                  ·
                    refine ⟨4639444226520022564047541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6185925635360030085396721 4639444226520022564047541)
                    ·
                      refine ⟨434947896236252115379457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4639444226520022564047541 434947896236252115379457)
                      ·
                        rfl

theorem cell23_847058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_847058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847058 prefixEnd_847058 := by exact prefixLift 847058
  have htrace : WordTrace (prefixWord ++ tailWord_847058) baseStart_847058 baseEnd_847058 := by
    simpa [prefixWord, tailWord_847058, baseEnd_847058] using wordTrace_append hprefix tailTrace_847058
  have hstable : (prefixWord ++ tailWord_847058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847058).length < 2 ^ (prefixWord ++ tailWord_847058).sum := by decide
  have hdescent : baseEnd_847058 < baseStart_847058 := by decide
  rcases family_descends (prefixWord ++ tailWord_847058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847072 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 1, 3, 2]
def baseStart_847072 : Nat := 118140960795 + 847072 * 2 ^ 59
def prefixEnd_847072 : Nat := 4983230072969 + 3 ^ 40 * 847072 * 2
def baseEnd_847072 : Nat := 434955084965415060604393

theorem tailTrace_847072 : CollatzResearch.WordTrace tailWord_847072 prefixEnd_847072 434955084965415060604393 := by
  unfold tailWord_847072
  simp only [CollatzResearch.WordTrace]
  refine ⟨15447626993605143612535735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20596835991473524816714313 15447626993605143612535735)
  ·
    refine ⟨23171440490407715418803603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15447626993605143612535735 23171440490407715418803603)
    ·
      refine ⟨34757160735611573128205405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23171440490407715418803603 34757160735611573128205405)
      ·
        refine ⟨13033935275854339923077027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34757160735611573128205405 13033935275854339923077027)
        ·
          refine ⟨19550902913781509884615541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13033935275854339923077027 19550902913781509884615541)
          ·
            refine ⟨1832897148167016551682707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19550902913781509884615541 1832897148167016551682707)
            ·
              refine ⟨2749345722250524827524061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832897148167016551682707 2749345722250524827524061)
              ·
                refine ⟨1031004645843946810321523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2749345722250524827524061 1031004645843946810321523)
                ·
                  refine ⟨1546506968765920215482285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031004645843946810321523 1546506968765920215482285)
                  ·
                    refine ⟨579940113287220080805857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546506968765920215482285 579940113287220080805857)
                    ·
                      refine ⟨434955084965415060604393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579940113287220080805857 434955084965415060604393)
                      ·
                        rfl

theorem cell23_847072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_847072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847072 prefixEnd_847072 := by exact prefixLift 847072
  have htrace : WordTrace (prefixWord ++ tailWord_847072) baseStart_847072 baseEnd_847072 := by
    simpa [prefixWord, tailWord_847072, baseEnd_847072] using wordTrace_append hprefix tailTrace_847072
  have hstable : (prefixWord ++ tailWord_847072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847072).length < 2 ^ (prefixWord ++ tailWord_847072).sum := by decide
  have hdescent : baseEnd_847072 < baseStart_847072 := by decide
  rcases family_descends (prefixWord ++ tailWord_847072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847081 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_847081 : Nat := 118140960795 + 847081 * 2 ^ 59
def prefixEnd_847081 : Nat := 4983230072969 + 3 ^ 40 * 847081 * 2
def baseEnd_847081 : Nat := 434959706291305525391851

theorem tailTrace_847081 : CollatzResearch.WordTrace tailWord_847081 prefixEnd_847081 434959706291305525391851 := by
  unfold tailWord_847081
  simp only [CollatzResearch.WordTrace]
  refine ⟨30895582244177681762149097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20597054829451787841432731 30895582244177681762149097)
  ·
    refine ⟨23171686683133261321611823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30895582244177681762149097 23171686683133261321611823)
    ·
      refine ⟨34757530024699891982417735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23171686683133261321611823 34757530024699891982417735)
      ·
        refine ⟨52136295037049837973626603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34757530024699891982417735 52136295037049837973626603)
        ·
          refine ⟨78204442555574756960439905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52136295037049837973626603 78204442555574756960439905)
          ·
            refine ⟨58653331916681067720329929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78204442555574756960439905 58653331916681067720329929)
            ·
              refine ⟨43989998937510800790247447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58653331916681067720329929 43989998937510800790247447)
              ·
                refine ⟨65984998406266201185371171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43989998937510800790247447 65984998406266201185371171)
                ·
                  refine ⟨98977497609399301778056757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65984998406266201185371171 98977497609399301778056757)
                  ·
                    refine ⟨9279140400881184541692821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98977497609399301778056757 9279140400881184541692821)
                    ·
                      refine ⟨434959706291305525391851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9279140400881184541692821 434959706291305525391851)
                      ·
                        rfl

theorem cell23_847081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_847081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847081 prefixEnd_847081 := by exact prefixLift 847081
  have htrace : WordTrace (prefixWord ++ tailWord_847081) baseStart_847081 baseEnd_847081 := by
    simpa [prefixWord, tailWord_847081, baseEnd_847081] using wordTrace_append hprefix tailTrace_847081
  have hstable : (prefixWord ++ tailWord_847081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847081).length < 2 ^ (prefixWord ++ tailWord_847081).sum := by decide
  have hdescent : baseEnd_847081 < baseStart_847081 := by decide
  rcases family_descends (prefixWord ++ tailWord_847081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847098 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_847098 : Nat := 118140960795 + 847098 * 2 ^ 59
def prefixEnd_847098 : Nat := 4983230072969 + 3 ^ 40 * 847098 * 2
def baseEnd_847098 : Nat := 434968435462431958879273

theorem tailTrace_847098 : CollatzResearch.WordTrace tailWord_847098 prefixEnd_847098 434968435462431958879273 := by
  unfold tailWord_847098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7724050571279023416379487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20597468190077395777011965 7724050571279023416379487)
  ·
    refine ⟨11586075856918535124569231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7724050571279023416379487 11586075856918535124569231)
    ·
      refine ⟨17379113785377802686853847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11586075856918535124569231 17379113785377802686853847)
      ·
        refine ⟨26068670678066704030280771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17379113785377802686853847 26068670678066704030280771)
        ·
          refine ⟨39103006017100056045421157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26068670678066704030280771 39103006017100056045421157)
          ·
            refine ⟨7331813628206260508516467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39103006017100056045421157 7331813628206260508516467)
            ·
              refine ⟨10997720442309390762774701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331813628206260508516467 10997720442309390762774701)
              ·
                refine ⟨4124145165866021536040513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10997720442309390762774701 4124145165866021536040513)
                ·
                  refine ⟨3093108874399516152030385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4124145165866021536040513 3093108874399516152030385)
                  ·
                    refine ⟨2319831655799637114022789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3093108874399516152030385 2319831655799637114022789)
                    ·
                      refine ⟨434968435462431958879273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2319831655799637114022789 434968435462431958879273)
                      ·
                        rfl

theorem cell23_847098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_847098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847098 prefixEnd_847098 := by exact prefixLift 847098
  have htrace : WordTrace (prefixWord ++ tailWord_847098) baseStart_847098 baseEnd_847098 := by
    simpa [prefixWord, tailWord_847098, baseEnd_847098] using wordTrace_append hprefix tailTrace_847098
  have hstable : (prefixWord ++ tailWord_847098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847098).length < 2 ^ (prefixWord ++ tailWord_847098).sum := by decide
  have hdescent : baseEnd_847098 < baseStart_847098 := by decide
  rcases family_descends (prefixWord ++ tailWord_847098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847106 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_847106 : Nat := 118140960795 + 847106 * 2 ^ 59
def prefixEnd_847106 : Nat := 4983230072969 + 3 ^ 40 * 847106 * 2
def baseEnd_847106 : Nat := 434972543307667927579237

theorem tailTrace_847106 : CollatzResearch.WordTrace tailWord_847106 prefixEnd_847106 434972543307667927579237 := by
  unfold tailWord_847106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7724123517271777757952293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20597662712724740687872781 7724123517271777757952293)
  ·
    refine ⟨1448273159488458329616055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7724123517271777757952293 1448273159488458329616055)
    ·
      refine ⟨2172409739232687494424083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448273159488458329616055 2172409739232687494424083)
      ·
        refine ⟨3258614608849031241636125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172409739232687494424083 3258614608849031241636125)
        ·
          refine ⟨1221980478318386715613547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3258614608849031241636125 1221980478318386715613547)
          ·
            refine ⟨1832970717477580073420321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221980478318386715613547 1832970717477580073420321)
            ·
              refine ⟨1374728038108185055065241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832970717477580073420321 1374728038108185055065241)
              ·
                refine ⟨1031046028581138791298931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374728038108185055065241 1031046028581138791298931)
                ·
                  refine ⟨1546569042871708186948397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031046028581138791298931 1546569042871708186948397)
                  ·
                    refine ⟨579963391076890570105649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546569042871708186948397 579963391076890570105649)
                    ·
                      refine ⟨434972543307667927579237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 579963391076890570105649 434972543307667927579237)
                      ·
                        rfl

theorem cell23_847106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_847106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847106 prefixEnd_847106 := by exact prefixLift 847106
  have htrace : WordTrace (prefixWord ++ tailWord_847106) baseStart_847106 baseEnd_847106 := by
    simpa [prefixWord, tailWord_847106, baseEnd_847106] using wordTrace_append hprefix tailTrace_847106
  have hstable : (prefixWord ++ tailWord_847106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847106).length < 2 ^ (prefixWord ++ tailWord_847106).sum := by decide
  have hdescent : baseEnd_847106 < baseStart_847106 := by decide
  rcases family_descends (prefixWord ++ tailWord_847106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847172 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_847172 : Nat := 118140960795 + 847172 * 2 ^ 59
def prefixEnd_847172 : Nat := 4983230072969 + 3 ^ 40 * 847172 * 2
def baseEnd_847172 : Nat := 145002144343621556451311

theorem tailTrace_847172 : CollatzResearch.WordTrace tailWord_847172 prefixEnd_847172 145002144343621556451311 := by
  unfold tailWord_847172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15449450643424002151855885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20599267524565336202474513 15449450643424002151855885)
  ·
    refine ⟨5793543991284000806945957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15449450643424002151855885 5793543991284000806945957)
    ·
      refine ⟨1086289498365750151302367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5793543991284000806945957 1086289498365750151302367)
      ·
        refine ⟨1629434247548625226953551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086289498365750151302367 1629434247548625226953551)
        ·
          refine ⟨2444151371322937840430327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629434247548625226953551 2444151371322937840430327)
          ·
            refine ⟨3666227056984406760645491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444151371322937840430327 3666227056984406760645491)
            ·
              refine ⟨5499340585476610140968237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666227056984406760645491 5499340585476610140968237)
              ·
                refine ⟨2062252719553728802863089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5499340585476610140968237 2062252719553728802863089)
                ·
                  refine ⟨1546689539665296602147317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2062252719553728802863089 1546689539665296602147317)
                  ·
                    refine ⟨145002144343621556451311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1546689539665296602147317 145002144343621556451311)
                    ·
                      rfl

theorem cell23_847172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_847172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847172 prefixEnd_847172 := by exact prefixLift 847172
  have htrace : WordTrace (prefixWord ++ tailWord_847172) baseStart_847172 baseEnd_847172 := by
    simpa [prefixWord, tailWord_847172, baseEnd_847172] using wordTrace_append hprefix tailTrace_847172
  have hstable : (prefixWord ++ tailWord_847172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847172).length < 2 ^ (prefixWord ++ tailWord_847172).sum := by decide
  have hdescent : baseEnd_847172 < baseStart_847172 := by decide
  rcases family_descends (prefixWord ++ tailWord_847172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847175 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_847175 : Nat := 118140960795 + 847175 * 2 ^ 59
def prefixEnd_847175 : Nat := 4983230072969 + 3 ^ 40 * 847175 * 2
def baseEnd_847175 : Nat := 435007973472828157616419

theorem tailTrace_847175 : CollatzResearch.WordTrace tailWord_847175 prefixEnd_847175 435007973472828157616419 := by
  unfold tailWord_847175
  simp only [CollatzResearch.WordTrace]
  refine ⟨30899010705837135816070979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20599340470558090544047319 30899010705837135816070979)
  ·
    refine ⟨46348516058755703724106469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30899010705837135816070979 46348516058755703724106469)
    ·
      refine ⟨8690346761016694448269963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46348516058755703724106469 8690346761016694448269963)
      ·
        refine ⟨13035520141525041672404945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8690346761016694448269963 13035520141525041672404945)
        ·
          refine ⟨9776640106143781254303709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13035520141525041672404945 9776640106143781254303709)
          ·
            refine ⟨3666240039803917970363891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9776640106143781254303709 3666240039803917970363891)
            ·
              refine ⟨5499360059705876955545837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666240039803917970363891 5499360059705876955545837)
              ·
                refine ⟨2062260022389703858329689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5499360059705876955545837 2062260022389703858329689)
                ·
                  refine ⟨1546695016792277893747267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2062260022389703858329689 1546695016792277893747267)
                  ·
                    refine ⟨2320042525188416840620901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1546695016792277893747267 2320042525188416840620901)
                    ·
                      refine ⟨435007973472828157616419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2320042525188416840620901 435007973472828157616419)
                      ·
                        rfl

theorem cell23_847175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_847175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847175 prefixEnd_847175 := by exact prefixLift 847175
  have htrace : WordTrace (prefixWord ++ tailWord_847175) baseStart_847175 baseEnd_847175 := by
    simpa [prefixWord, tailWord_847175, baseEnd_847175] using wordTrace_append hprefix tailTrace_847175
  have hstable : (prefixWord ++ tailWord_847175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847175).length < 2 ^ (prefixWord ++ tailWord_847175).sum := by decide
  have hdescent : baseEnd_847175 < baseStart_847175 := by decide
  rcases family_descends (prefixWord ++ tailWord_847175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847202 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_847202 : Nat := 118140960795 + 847202 * 2 ^ 59
def prefixEnd_847202 : Nat := 4983230072969 + 3 ^ 40 * 847202 * 2
def baseEnd_847202 : Nat := 145007279150166517326265

theorem tailTrace_847202 : CollatzResearch.WordTrace tailWord_847202 prefixEnd_847202 145007279150166517326265 := by
  unfold tailWord_847202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7724998869184829856825965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20599996984492879618202573 7724998869184829856825965)
  ·
    refine ⟨2896874575944311196309737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7724998869184829856825965 2896874575944311196309737)
    ·
      refine ⟨2172655931958233397232303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2896874575944311196309737 2172655931958233397232303)
      ·
        refine ⟨3258983897937350095848455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172655931958233397232303 3258983897937350095848455)
        ·
          refine ⟨4888475846906025143772683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3258983897937350095848455 4888475846906025143772683)
          ·
            refine ⟨7332713770359037715659025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888475846906025143772683 7332713770359037715659025)
            ·
              refine ⟨5499535327769278286744269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7332713770359037715659025 5499535327769278286744269)
              ·
                refine ⟨2062325747913479357529101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5499535327769278286744269 2062325747913479357529101)
                ·
                  refine ⟨773372155467554759073413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2062325747913479357529101 773372155467554759073413)
                  ·
                    refine ⟨145007279150166517326265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773372155467554759073413 145007279150166517326265)
                    ·
                      rfl

theorem cell23_847202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_847202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847202 prefixEnd_847202 := by exact prefixLift 847202
  have htrace : WordTrace (prefixWord ++ tailWord_847202) baseStart_847202 baseEnd_847202 := by
    simpa [prefixWord, tailWord_847202, baseEnd_847202] using wordTrace_append hprefix tailTrace_847202
  have hstable : (prefixWord ++ tailWord_847202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847202).length < 2 ^ (prefixWord ++ tailWord_847202).sum := by decide
  have hdescent : baseEnd_847202 < baseStart_847202 := by decide
  rcases family_descends (prefixWord ++ tailWord_847202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847295 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_847295 : Nat := 118140960795 + 847295 * 2 ^ 59
def prefixEnd_847295 : Nat := 4983230072969 + 3 ^ 40 * 847295 * 2
def baseEnd_847295 : Nat := 435069591151367688115867

theorem tailTrace_847295 : CollatzResearch.WordTrace tailWord_847295 prefixEnd_847295 435069591151367688115867 := by
  unfold tailWord_847295
  simp only [CollatzResearch.WordTrace]
  refine ⟨30903387465402396310439339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20602258310268264206959559 30903387465402396310439339)
  ·
    refine ⟨46355081198103594465659009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30903387465402396310439339 46355081198103594465659009)
    ·
      refine ⟨34766310898577695849244257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46355081198103594465659009 34766310898577695849244257)
      ·
        refine ⟨26074733173933271886933193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34766310898577695849244257 26074733173933271886933193)
        ·
          refine ⟨19556049880449953915199895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26074733173933271886933193 19556049880449953915199895)
          ·
            refine ⟨29334074820674930872799843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19556049880449953915199895 29334074820674930872799843)
            ·
              refine ⟨44001112231012396309199765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29334074820674930872799843 44001112231012396309199765)
              ·
                refine ⟨2062552135828706076993739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44001112231012396309199765 2062552135828706076993739)
                ·
                  refine ⟨3093828203743059115490609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062552135828706076993739 3093828203743059115490609)
                  ·
                    refine ⟨2320371152807294336617957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3093828203743059115490609 2320371152807294336617957)
                    ·
                      refine ⟨435069591151367688115867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2320371152807294336617957 435069591151367688115867)
                      ·
                        rfl

theorem cell23_847295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_847295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847295 prefixEnd_847295 := by exact prefixLift 847295
  have htrace : WordTrace (prefixWord ++ tailWord_847295) baseStart_847295 baseEnd_847295 := by
    simpa [prefixWord, tailWord_847295, baseEnd_847295] using wordTrace_append hprefix tailTrace_847295
  have hstable : (prefixWord ++ tailWord_847295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847295).length < 2 ^ (prefixWord ++ tailWord_847295).sum := by decide
  have hdescent : baseEnd_847295 < baseStart_847295 := by decide
  rcases family_descends (prefixWord ++ tailWord_847295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847349 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_847349 : Nat := 118140960795 + 847349 * 2 ^ 59
def prefixEnd_847349 : Nat := 4983230072969 + 3 ^ 40 * 847349 * 2
def baseEnd_847349 : Nat := 435097319106710476840619

theorem tailTrace_847349 : CollatzResearch.WordTrace tailWord_847349 prefixEnd_847349 435097319106710476840619 := by
  unfold tailWord_847349
  simp only [CollatzResearch.WordTrace]
  refine ⟨30905357007206763532905101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20603571338137842355270067 30905357007206763532905101)
  ·
    refine ⟨11589508877702536324839413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30905357007206763532905101 11589508877702536324839413)
    ·
      refine ⟨1086516457284612780453695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11589508877702536324839413 1086516457284612780453695)
      ·
        refine ⟨1629774685926919170680543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086516457284612780453695 1629774685926919170680543)
        ·
          refine ⟨2444662028890378756020815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629774685926919170680543 2444662028890378756020815)
          ·
            refine ⟨3666993043335568134031223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444662028890378756020815 3666993043335568134031223)
            ·
              refine ⟨5500489565003352201046835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666993043335568134031223 5500489565003352201046835)
              ·
                refine ⟨8250734347505028301570253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500489565003352201046835 8250734347505028301570253)
                ·
                  refine ⟨3094025380314385613088845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8250734347505028301570253 3094025380314385613088845)
                  ·
                    refine ⟨1160259517617894604908317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094025380314385613088845 1160259517617894604908317)
                    ·
                      refine ⟨435097319106710476840619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1160259517617894604908317 435097319106710476840619)
                      ·
                        rfl

theorem cell23_847349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_847349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847349 prefixEnd_847349 := by exact prefixLift 847349
  have htrace : WordTrace (prefixWord ++ tailWord_847349) baseStart_847349 baseEnd_847349 := by
    simpa [prefixWord, tailWord_847349, baseEnd_847349] using wordTrace_append hprefix tailTrace_847349
  have hstable : (prefixWord ++ tailWord_847349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847349).length < 2 ^ (prefixWord ++ tailWord_847349).sum := by decide
  have hdescent : baseEnd_847349 < baseStart_847349 := by decide
  rcases family_descends (prefixWord ++ tailWord_847349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847365 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_847365 : Nat := 118140960795 + 847365 * 2 ^ 59
def prefixEnd_847365 : Nat := 4983230072969 + 3 ^ 40 * 847365 * 2
def baseEnd_847365 : Nat := 145035178265727471413515

theorem tailTrace_847365 : CollatzResearch.WordTrace tailWord_847365 prefixEnd_847365 145035178265727471413515 := by
  unfold tailWord_847365
  simp only [CollatzResearch.WordTrace]
  refine ⟨30905940575148798265487549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20603960383432532176991699 30905940575148798265487549)
  ·
    refine ⟨11589727715680799349557831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30905940575148798265487549 11589727715680799349557831)
    ·
      refine ⟨17384591573521199024336747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11589727715680799349557831 17384591573521199024336747)
      ·
        refine ⟨26076887360281798536505121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17384591573521199024336747 26076887360281798536505121)
        ·
          refine ⟨19557665520211348902378841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26076887360281798536505121 19557665520211348902378841)
          ·
            refine ⟨14668249140158511676784131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19557665520211348902378841 14668249140158511676784131)
            ·
              refine ⟨22002373710237767515176197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14668249140158511676784131 22002373710237767515176197)
              ·
                refine ⟨4125445070669581409095537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22002373710237767515176197 4125445070669581409095537)
                ·
                  refine ⟨3094083803002186056821653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4125445070669581409095537 3094083803002186056821653)
                  ·
                    refine ⟨145035178265727471413515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3094083803002186056821653 145035178265727471413515)
                    ·
                      rfl

theorem cell23_847365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_847365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847365 prefixEnd_847365 := by exact prefixLift 847365
  have htrace : WordTrace (prefixWord ++ tailWord_847365) baseStart_847365 baseEnd_847365 := by
    simpa [prefixWord, tailWord_847365, baseEnd_847365] using wordTrace_append hprefix tailTrace_847365
  have hstable : (prefixWord ++ tailWord_847365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847365).length < 2 ^ (prefixWord ++ tailWord_847365).sum := by decide
  have hdescent : baseEnd_847365 < baseStart_847365 := by decide
  rcases family_descends (prefixWord ++ tailWord_847365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847373 : List Nat := [1, 7, 1, 1, 3, 1, 1, 8]
def baseStart_847373 : Nat := 118140960795 + 847373 * 2 ^ 59
def prefixEnd_847373 : Nat := 4983230072969 + 3 ^ 40 * 847373 * 2
def baseEnd_847373 : Nat := 16115171949719199368167

theorem tailTrace_847373 : CollatzResearch.WordTrace tailWord_847373 prefixEnd_847373 16115171949719199368167 := by
  unfold tailWord_847373
  simp only [CollatzResearch.WordTrace]
  refine ⟨30906232359119815631778773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20604154906079877087852515 30906232359119815631778773)
  ·
    refine ⟨724364820916870678869815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30906232359119815631778773 724364820916870678869815)
    ·
      refine ⟨1086547231375306018304723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724364820916870678869815 1086547231375306018304723)
      ·
        refine ⟨1629820847062959027457085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086547231375306018304723 1629820847062959027457085)
        ·
          refine ⟨611182817648609635296407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1629820847062959027457085 611182817648609635296407)
          ·
            refine ⟨916774226472914452944611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611182817648609635296407 916774226472914452944611)
            ·
              refine ⟨1375161339709371679416917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916774226472914452944611 1375161339709371679416917)
              ·
                refine ⟨16115171949719199368167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1375161339709371679416917 16115171949719199368167)
                ·
                  rfl

theorem cell23_847373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 8].length) (baseStart_847373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847373 prefixEnd_847373 := by exact prefixLift 847373
  have htrace : WordTrace (prefixWord ++ tailWord_847373) baseStart_847373 baseEnd_847373 := by
    simpa [prefixWord, tailWord_847373, baseEnd_847373] using wordTrace_append hprefix tailTrace_847373
  have hstable : (prefixWord ++ tailWord_847373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847373).length < 2 ^ (prefixWord ++ tailWord_847373).sum := by decide
  have hdescent : baseEnd_847373 < baseStart_847373 := by decide
  rcases family_descends (prefixWord ++ tailWord_847373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847402 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_847402 : Nat := 118140960795 + 847402 * 2 ^ 59
def prefixEnd_847402 : Nat := 4983230072969 + 3 ^ 40 * 847402 * 2
def baseEnd_847402 : Nat := 435124533581398769477875

theorem tailTrace_847402 : CollatzResearch.WordTrace tailWord_847402 prefixEnd_847402 435124533581398769477875 := by
  unfold tailWord_847402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726822519003688396146115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20604860050676502389722973 7726822519003688396146115)
  ·
    refine ⟨11590233778505532594219173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7726822519003688396146115 11590233778505532594219173)
    ·
      refine ⟨2173168833469787361416095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11590233778505532594219173 2173168833469787361416095)
      ·
        refine ⟨3259753250204681042124143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173168833469787361416095 3259753250204681042124143)
        ·
          refine ⟨4889629875307021563186215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259753250204681042124143 4889629875307021563186215)
          ·
            refine ⟨7334444812960532344779323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889629875307021563186215 7334444812960532344779323)
            ·
              refine ⟨11001667219440798517168985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334444812960532344779323 11001667219440798517168985)
              ·
                refine ⟨8251250414580598887876739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11001667219440798517168985 8251250414580598887876739)
                ·
                  refine ⟨12376875621870898331815109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8251250414580598887876739 12376875621870898331815109)
                  ·
                    refine ⟨2320664179100793437215333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12376875621870898331815109 2320664179100793437215333)
                    ·
                      refine ⟨435124533581398769477875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2320664179100793437215333 435124533581398769477875)
                      ·
                        rfl

theorem cell23_847402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_847402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847402 prefixEnd_847402 := by exact prefixLift 847402
  have htrace : WordTrace (prefixWord ++ tailWord_847402) baseStart_847402 baseEnd_847402 := by
    simpa [prefixWord, tailWord_847402, baseEnd_847402] using wordTrace_append hprefix tailTrace_847402
  have hstable : (prefixWord ++ tailWord_847402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847402).length < 2 ^ (prefixWord ++ tailWord_847402).sum := by decide
  have hdescent : baseEnd_847402 < baseStart_847402 := by decide
  rcases family_descends (prefixWord ++ tailWord_847402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847406 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_847406 : Nat := 118140960795 + 847406 * 2 ^ 59
def prefixEnd_847406 : Nat := 4983230072969 + 3 ^ 40 * 847406 * 2
def baseEnd_847406 : Nat := 435126587504016753827857

theorem tailTrace_847406 : CollatzResearch.WordTrace tailWord_847406 prefixEnd_847406 435126587504016753827857 := by
  unfold tailWord_847406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863429496000032783466259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20604957312000174845153381 3863429496000032783466259)
  ·
    refine ⟨5795144244000049175199389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3863429496000032783466259 5795144244000049175199389)
    ·
      refine ⟨2173179091500018440699771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5795144244000049175199389 2173179091500018440699771)
      ·
        refine ⟨3259768637250027661049657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173179091500018440699771 3259768637250027661049657)
        ·
          refine ⟨2444826477937520745787243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3259768637250027661049657 2444826477937520745787243)
          ·
            refine ⟨3667239716906281118680865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444826477937520745787243 3667239716906281118680865)
            ·
              refine ⟨2750429787679710839010649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667239716906281118680865 2750429787679710839010649)
              ·
                refine ⟨2062822340759783129257987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2750429787679710839010649 2062822340759783129257987)
                ·
                  refine ⟨3094233511139674693886981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062822340759783129257987 3094233511139674693886981)
                  ·
                    refine ⟨580168783338689005103809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3094233511139674693886981 580168783338689005103809)
                    ·
                      refine ⟨435126587504016753827857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 580168783338689005103809 435126587504016753827857)
                      ·
                        rfl

theorem cell23_847406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_847406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847406 prefixEnd_847406 := by exact prefixLift 847406
  have htrace : WordTrace (prefixWord ++ tailWord_847406) baseStart_847406 baseEnd_847406 := by
    simpa [prefixWord, tailWord_847406, baseEnd_847406] using wordTrace_append hprefix tailTrace_847406
  have hstable : (prefixWord ++ tailWord_847406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847406).length < 2 ^ (prefixWord ++ tailWord_847406).sum := by decide
  have hdescent : baseEnd_847406 < baseStart_847406 := by decide
  rcases family_descends (prefixWord ++ tailWord_847406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847423 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 2, 2, 2]
def baseStart_847423 : Nat := 118140960795 + 847423 * 2 ^ 59
def prefixEnd_847423 : Nat := 4983230072969 + 3 ^ 40 * 847423 * 2
def baseEnd_847423 : Nat := 435135316675143187315279

theorem tailTrace_847423 : CollatzResearch.WordTrace tailWord_847423 prefixEnd_847423 435135316675143187315279 := by
  unfold tailWord_847423
  simp only [CollatzResearch.WordTrace]
  refine ⟨30908056008938674171098923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20605370672625782780732615 30908056008938674171098923)
  ·
    refine ⟨46362084013408011256648385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30908056008938674171098923 46362084013408011256648385)
    ·
      refine ⟨34771563010056008442486289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46362084013408011256648385 34771563010056008442486289)
      ·
        refine ⟨26078672257542006331864717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34771563010056008442486289 26078672257542006331864717)
        ·
          refine ⟨9779502096578252374449269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26078672257542006331864717 9779502096578252374449269)
          ·
            refine ⟨916828321554211160104619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9779502096578252374449269 916828321554211160104619)
            ·
              refine ⟨1375242482331316740156929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916828321554211160104619 1375242482331316740156929)
              ·
                refine ⟨1031431861748487555117697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375242482331316740156929 1031431861748487555117697)
                ·
                  refine ⟨773573896311365666338273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1031431861748487555117697 773573896311365666338273)
                  ·
                    refine ⟨580180422233524249753705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 773573896311365666338273 580180422233524249753705)
                    ·
                      refine ⟨435135316675143187315279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 580180422233524249753705 435135316675143187315279)
                      ·
                        rfl

theorem cell23_847423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_847423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847423 prefixEnd_847423 := by exact prefixLift 847423
  have htrace : WordTrace (prefixWord ++ tailWord_847423) baseStart_847423 baseEnd_847423 := by
    simpa [prefixWord, tailWord_847423, baseEnd_847423] using wordTrace_append hprefix tailTrace_847423
  have hstable : (prefixWord ++ tailWord_847423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847423).length < 2 ^ (prefixWord ++ tailWord_847423).sum := by decide
  have hdescent : baseEnd_847423 < baseStart_847423 := by decide
  rcases family_descends (prefixWord ++ tailWord_847423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847435 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 7]
def baseStart_847435 : Nat := 118140960795 + 847435 * 2 ^ 59
def prefixEnd_847435 : Nat := 4983230072969 + 3 ^ 40 * 847435 * 2
def baseEnd_847435 : Nat := 435141478442997140365223

theorem tailTrace_847435 : CollatzResearch.WordTrace tailWord_847435 prefixEnd_847435 435141478442997140365223 := by
  unfold tailWord_847435
  simp only [CollatzResearch.WordTrace]
  refine ⟨30908493684895200220535759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20605662456596800147023839 30908493684895200220535759)
  ·
    refine ⟨46362740527342800330803639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30908493684895200220535759 46362740527342800330803639)
    ·
      refine ⟨69544110791014200496205459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46362740527342800330803639 69544110791014200496205459)
      ·
        refine ⟨104316166186521300744308189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69544110791014200496205459 104316166186521300744308189)
        ·
          refine ⟨39118562319945487779115571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104316166186521300744308189 39118562319945487779115571)
          ·
            refine ⟨58677843479918231668673357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39118562319945487779115571 58677843479918231668673357)
            ·
              refine ⟨22004191304969336875752509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58677843479918231668673357 22004191304969336875752509)
              ·
                refine ⟨8251571739363501328407191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22004191304969336875752509 8251571739363501328407191)
                ·
                  refine ⟨12377357609045251992610787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8251571739363501328407191 12377357609045251992610787)
                  ·
                    refine ⟨18566036413567877988916181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12377357609045251992610787 18566036413567877988916181)
                    ·
                      refine ⟨435141478442997140365223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18566036413567877988916181 435141478442997140365223)
                      ·
                        rfl

theorem cell23_847435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_847435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847435 prefixEnd_847435 := by exact prefixLift 847435
  have htrace : WordTrace (prefixWord ++ tailWord_847435) baseStart_847435 baseEnd_847435 := by
    simpa [prefixWord, tailWord_847435, baseEnd_847435] using wordTrace_append hprefix tailTrace_847435
  have hstable : (prefixWord ++ tailWord_847435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847435).length < 2 ^ (prefixWord ++ tailWord_847435).sum := by decide
  have hdescent : baseEnd_847435 < baseStart_847435 := by decide
  rcases family_descends (prefixWord ++ tailWord_847435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847442 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_847442 : Nat := 118140960795 + 847442 * 2 ^ 59
def prefixEnd_847442 : Nat := 4983230072969 + 3 ^ 40 * 847442 * 2
def baseEnd_847442 : Nat := 145048357602526204325897

theorem tailTrace_847442 : CollatzResearch.WordTrace tailWord_847442 prefixEnd_847442 145048357602526204325897 := by
  unfold tailWord_847442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727187248967460104010145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20605832663913226944027053 7727187248967460104010145)
  ·
    refine ⟨5795390436725595078007609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7727187248967460104010145 5795390436725595078007609)
    ·
      refine ⟨4346542827544196308505707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5795390436725595078007609 4346542827544196308505707)
      ·
        refine ⟨6519814241316294462758561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346542827544196308505707 6519814241316294462758561)
        ·
          refine ⟨4889860680987220847068921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6519814241316294462758561 4889860680987220847068921)
          ·
            refine ⟨3667395510740415635301691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4889860680987220847068921 3667395510740415635301691)
            ·
              refine ⟨5501093266110623452952537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667395510740415635301691 5501093266110623452952537)
              ·
                refine ⟨4125819949582967589714403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5501093266110623452952537 4125819949582967589714403)
                ·
                  refine ⟨6188729924374451384571605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125819949582967589714403 6188729924374451384571605)
                  ·
                    refine ⟨145048357602526204325897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6188729924374451384571605 145048357602526204325897)
                    ·
                      rfl

theorem cell23_847442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_847442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847442 prefixEnd_847442 := by exact prefixLift 847442
  have htrace : WordTrace (prefixWord ++ tailWord_847442) baseStart_847442 baseEnd_847442 := by
    simpa [prefixWord, tailWord_847442, baseEnd_847442] using wordTrace_append hprefix tailTrace_847442
  have hstable : (prefixWord ++ tailWord_847442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847442).length < 2 ^ (prefixWord ++ tailWord_847442).sum := by decide
  have hdescent : baseEnd_847442 < baseStart_847442 := by decide
  rcases family_descends (prefixWord ++ tailWord_847442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847482 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_847482 : Nat := 118140960795 + 847482 * 2 ^ 59
def prefixEnd_847482 : Nat := 4983230072969 + 3 ^ 40 * 847482 * 2
def baseEnd_847482 : Nat := 435165612033758456477507

theorem tailTrace_847482 : CollatzResearch.WordTrace tailWord_847482 prefixEnd_847482 435165612033758456477507 := by
  unfold tailWord_847482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727551978931231811874175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20606805277149951498331133 7727551978931231811874175)
  ·
    refine ⟨11591327968396847717811263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7727551978931231811874175 11591327968396847717811263)
    ·
      refine ⟨17386991952595271576716895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11591327968396847717811263 17386991952595271576716895)
      ·
        refine ⟨26080487928892907365075343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17386991952595271576716895 26080487928892907365075343)
        ·
          refine ⟨39120731893339361047613015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26080487928892907365075343 39120731893339361047613015)
          ·
            refine ⟨58681097840009041571419523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39120731893339361047613015 58681097840009041571419523)
            ·
              refine ⟨88021646760013562357129285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58681097840009041571419523 88021646760013562357129285)
              ·
                refine ⟨16504058767502542941961741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88021646760013562357129285 16504058767502542941961741)
                ·
                  refine ⟨6189022037813453603235653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16504058767502542941961741 6189022037813453603235653)
                  ·
                    refine ⟨1160441632090022550606685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189022037813453603235653 1160441632090022550606685)
                    ·
                      refine ⟨435165612033758456477507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1160441632090022550606685 435165612033758456477507)
                      ·
                        rfl

theorem cell23_847482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_847482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847482 prefixEnd_847482 := by exact prefixLift 847482
  have htrace : WordTrace (prefixWord ++ tailWord_847482) baseStart_847482 baseEnd_847482 := by
    simpa [prefixWord, tailWord_847482, baseEnd_847482] using wordTrace_append hprefix tailTrace_847482
  have hstable : (prefixWord ++ tailWord_847482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847482).length < 2 ^ (prefixWord ++ tailWord_847482).sum := by decide
  have hdescent : baseEnd_847482 < baseStart_847482 := by decide
  rcases family_descends (prefixWord ++ tailWord_847482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847556 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_847556 : Nat := 118140960795 + 847556 * 2 ^ 59
def prefixEnd_847556 : Nat := 4983230072969 + 3 ^ 40 * 847556 * 2
def baseEnd_847556 : Nat := 435203609602191166952167

theorem tailTrace_847556 : CollatzResearch.WordTrace tailWord_847556 prefixEnd_847556 435203609602191166952167 := by
  unfold tailWord_847556
  simp only [CollatzResearch.WordTrace]
  refine ⟨15456453458728418942845261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20608604611637891923793681 15456453458728418942845261)
  ·
    refine ⟨5796170047023157103566973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15456453458728418942845261 5796170047023157103566973)
    ·
      refine ⟨2173563767633683913837615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5796170047023157103566973 2173563767633683913837615)
      ·
        refine ⟨3260345651450525870756423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173563767633683913837615 3260345651450525870756423)
        ·
          refine ⟨4890518477175788806134635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260345651450525870756423 4890518477175788806134635)
          ·
            refine ⟨7335777715763683209201953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890518477175788806134635 7335777715763683209201953)
            ·
              refine ⟨5501833286822762406901465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7335777715763683209201953 5501833286822762406901465)
              ·
                refine ⟨4126374965117071805176099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5501833286822762406901465 4126374965117071805176099)
                ·
                  refine ⟨6189562447675607707764149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126374965117071805176099 6189562447675607707764149)
                  ·
                    refine ⟨580271479469588222602889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6189562447675607707764149 580271479469588222602889)
                    ·
                      refine ⟨435203609602191166952167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 580271479469588222602889 435203609602191166952167)
                      ·
                        rfl

theorem cell23_847556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_847556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847556 prefixEnd_847556 := by exact prefixLift 847556
  have htrace : WordTrace (prefixWord ++ tailWord_847556) baseStart_847556 baseEnd_847556 := by
    simpa [prefixWord, tailWord_847556, baseEnd_847556] using wordTrace_append hprefix tailTrace_847556
  have hstable : (prefixWord ++ tailWord_847556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847556).length < 2 ^ (prefixWord ++ tailWord_847556).sum := by decide
  have hdescent : baseEnd_847556 < baseStart_847556 := by decide
  rcases family_descends (prefixWord ++ tailWord_847556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847569 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_847569 : Nat := 118140960795 + 847569 * 2 ^ 59
def prefixEnd_847569 : Nat := 4983230072969 + 3 ^ 40 * 847569 * 2
def baseEnd_847569 : Nat := 435210284850699616089607

theorem tailTrace_847569 : CollatzResearch.WordTrace tailWord_847569 prefixEnd_847569 435210284850699616089607 := by
  unfold tailWord_847569
  simp only [CollatzResearch.WordTrace]
  refine ⟨30913381066409741105913761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20608920710939827403942507 30913381066409741105913761)
  ·
    refine ⟨23185035799807305829435321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30913381066409741105913761 23185035799807305829435321)
    ·
      refine ⟨17388776849855479372076491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23185035799807305829435321 17388776849855479372076491)
      ·
        refine ⟨26083165274783219058114737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17388776849855479372076491 26083165274783219058114737)
        ·
          refine ⟨19562373956087414293586053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26083165274783219058114737 19562373956087414293586053)
          ·
            refine ⟨3667945116766390180047385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19562373956087414293586053 3667945116766390180047385)
            ·
              refine ⟨2750958837574792635035539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667945116766390180047385 2750958837574792635035539)
              ·
                refine ⟨4126438256362188952553309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750958837574792635035539 4126438256362188952553309)
                ·
                  refine ⟨1547414346135820857207491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4126438256362188952553309 1547414346135820857207491)
                  ·
                    refine ⟨2321121519203731285811237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1547414346135820857207491 2321121519203731285811237)
                    ·
                      refine ⟨435210284850699616089607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2321121519203731285811237 435210284850699616089607)
                      ·
                        rfl

theorem cell23_847569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_847569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847569 prefixEnd_847569 := by exact prefixLift 847569
  have htrace : WordTrace (prefixWord ++ tailWord_847569) baseStart_847569 baseEnd_847569 := by
    simpa [prefixWord, tailWord_847569, baseEnd_847569] using wordTrace_append hprefix tailTrace_847569
  have hstable : (prefixWord ++ tailWord_847569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847569).length < 2 ^ (prefixWord ++ tailWord_847569).sum := by decide
  have hdescent : baseEnd_847569 < baseStart_847569 := by decide
  rcases family_descends (prefixWord ++ tailWord_847569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847589 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_847589 : Nat := 118140960795 + 847589 * 2 ^ 59
def prefixEnd_847589 : Nat := 4983230072969 + 3 ^ 40 * 847589 * 2
def baseEnd_847589 : Nat := 435220554463789537839515

theorem tailTrace_847589 : CollatzResearch.WordTrace tailWord_847589 prefixEnd_847589 435220554463789537839515 := by
  unfold tailWord_847589
  simp only [CollatzResearch.WordTrace]
  refine ⟨30914110526337284521641821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20609407017558189681094547 30914110526337284521641821)
  ·
    refine ⟨11592791447376481695615683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30914110526337284521641821 11592791447376481695615683)
    ·
      refine ⟨17389187171064722543423525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11592791447376481695615683 17389187171064722543423525)
      ·
        refine ⟨3260472594574635476891911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17389187171064722543423525 3260472594574635476891911)
        ·
          refine ⟨4890708891861953215337867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260472594574635476891911 4890708891861953215337867)
          ·
            refine ⟨7336063337792929823006801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890708891861953215337867 7336063337792929823006801)
            ·
              refine ⟨5502047503344697367255101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7336063337792929823006801 5502047503344697367255101)
              ·
                refine ⟨2063267813754261512720663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5502047503344697367255101 2063267813754261512720663)
                ·
                  refine ⟨3094901720631392269080995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063267813754261512720663 3094901720631392269080995)
                  ·
                    refine ⟨4642352580947088403621493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3094901720631392269080995 4642352580947088403621493)
                    ·
                      refine ⟨435220554463789537839515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4642352580947088403621493 435220554463789537839515)
                      ·
                        rfl

theorem cell23_847589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_847589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847589 prefixEnd_847589 := by exact prefixLift 847589
  have htrace : WordTrace (prefixWord ++ tailWord_847589) baseStart_847589 baseEnd_847589 := by
    simpa [prefixWord, tailWord_847589, baseEnd_847589] using wordTrace_append hprefix tailTrace_847589
  have hstable : (prefixWord ++ tailWord_847589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847589).length < 2 ^ (prefixWord ++ tailWord_847589).sum := by decide
  have hdescent : baseEnd_847589 < baseStart_847589 := by decide
  rcases family_descends (prefixWord ++ tailWord_847589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847596 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_847596 : Nat := 118140960795 + 847596 * 2 ^ 59
def prefixEnd_847596 : Nat := 4983230072969 + 3 ^ 40 * 847596 * 2
def baseEnd_847596 : Nat := 145074716276123670150661

theorem tailTrace_847596 : CollatzResearch.WordTrace tailWord_847596 prefixEnd_847596 145074716276123670150661 := by
  unfold tailWord_847596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457182918655962358573321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20609577224874616478097761 15457182918655962358573321)
  ·
    refine ⟨11592887188991971768929991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15457182918655962358573321 11592887188991971768929991)
    ·
      refine ⟨17389330783487957653394987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11592887188991971768929991 17389330783487957653394987)
      ·
        refine ⟨26083996175231936480092481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17389330783487957653394987 26083996175231936480092481)
        ·
          refine ⟨19562997131423952360069361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26083996175231936480092481 19562997131423952360069361)
          ·
            refine ⟨14672247848567964270052021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19562997131423952360069361 14672247848567964270052021)
            ·
              refine ⟨1375523235803246650317377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14672247848567964270052021 1375523235803246650317377)
              ·
                refine ⟨1031642426852434987738033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375523235803246650317377 1031642426852434987738033)
                ·
                  refine ⟨773731820139326240803525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1031642426852434987738033 773731820139326240803525)
                  ·
                    refine ⟨145074716276123670150661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773731820139326240803525 145074716276123670150661)
                    ·
                      rfl

theorem cell23_847596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_847596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847596 prefixEnd_847596 := by exact prefixLift 847596
  have htrace : WordTrace (prefixWord ++ tailWord_847596) baseStart_847596 baseEnd_847596 := by
    simpa [prefixWord, tailWord_847596, baseEnd_847596] using wordTrace_append hprefix tailTrace_847596
  have hstable : (prefixWord ++ tailWord_847596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847596).length < 2 ^ (prefixWord ++ tailWord_847596).sum := by decide
  have hdescent : baseEnd_847596 < baseStart_847596 := by decide
  rcases family_descends (prefixWord ++ tailWord_847596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847606 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_847606 : Nat := 118140960795 + 847606 * 2 ^ 59
def prefixEnd_847606 : Nat := 4983230072969 + 3 ^ 40 * 847606 * 2
def baseEnd_847606 : Nat := 435229283634915971326937

theorem tailTrace_847606 : CollatzResearch.WordTrace tailWord_847606 prefixEnd_847606 435229283634915971326937 := by
  unfold tailWord_847606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932170660454731026563167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20609820378183797616673781 1932170660454731026563167)
  ·
    refine ⟨2898255990682096539844751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1932170660454731026563167 2898255990682096539844751)
    ·
      refine ⟨4347383986023144809767127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898255990682096539844751 4347383986023144809767127)
      ·
        refine ⟨6521075979034717214650691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4347383986023144809767127 6521075979034717214650691)
        ·
          refine ⟨9781613968552075821976037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521075979034717214650691 9781613968552075821976037)
          ·
            refine ⟨1834052619103514216620507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9781613968552075821976037 1834052619103514216620507)
            ·
              refine ⟨2751078928655271324930761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834052619103514216620507 2751078928655271324930761)
              ·
                refine ⟨2063309196491453493698071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2751078928655271324930761 2063309196491453493698071)
                ·
                  refine ⟨3094963794737180240547107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063309196491453493698071 3094963794737180240547107)
                  ·
                    refine ⟨4642445692105770360820661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3094963794737180240547107 4642445692105770360820661)
                    ·
                      refine ⟨435229283634915971326937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4642445692105770360820661 435229283634915971326937)
                      ·
                        rfl

theorem cell23_847606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_847606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847606 prefixEnd_847606 := by exact prefixLift 847606
  have htrace : WordTrace (prefixWord ++ tailWord_847606) baseStart_847606 baseEnd_847606 := by
    simpa [prefixWord, tailWord_847606, baseEnd_847606] using wordTrace_append hprefix tailTrace_847606
  have hstable : (prefixWord ++ tailWord_847606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847606).length < 2 ^ (prefixWord ++ tailWord_847606).sum := by decide
  have hdescent : baseEnd_847606 < baseStart_847606 := by decide
  rcases family_descends (prefixWord ++ tailWord_847606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847626 : List Nat := [3, 1, 2, 2, 1, 5, 2, 7]
def baseStart_847626 : Nat := 118140960795 + 847626 * 2 ^ 59
def prefixEnd_847626 : Nat := 4983230072969 + 3 ^ 40 * 847626 * 2
def baseEnd_847626 : Nat := 16119983453629847891735

theorem tailTrace_847626 : CollatzResearch.WordTrace tailWord_847626 prefixEnd_847626 16119983453629847891735 := by
  unfold tailWord_847626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728865006800809960184683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20610306684802159893825821 7728865006800809960184683)
  ·
    refine ⟨11593297510201214940277025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7728865006800809960184683 11593297510201214940277025)
    ·
      refine ⟨8694973132650911205207769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11593297510201214940277025 8694973132650911205207769)
      ·
        refine ⟨6521229849488183403905827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8694973132650911205207769 6521229849488183403905827)
        ·
          refine ⟨9781844774232275105858741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521229849488183403905827 9781844774232275105858741)
          ·
            refine ⟨917047947584275791174257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9781844774232275105858741 917047947584275791174257)
            ·
              refine ⟨687785960688206843380693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917047947584275791174257 687785960688206843380693)
              ·
                refine ⟨16119983453629847891735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 687785960688206843380693 16119983453629847891735)
                ·
                  rfl

theorem cell23_847626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 7].length) (baseStart_847626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847626 prefixEnd_847626 := by exact prefixLift 847626
  have htrace : WordTrace (prefixWord ++ tailWord_847626) baseStart_847626 baseEnd_847626 := by
    simpa [prefixWord, tailWord_847626, baseEnd_847626] using wordTrace_append hprefix tailTrace_847626
  have hstable : (prefixWord ++ tailWord_847626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847626).length < 2 ^ (prefixWord ++ tailWord_847626).sum := by decide
  have hdescent : baseEnd_847626 < baseStart_847626 := by decide
  rcases family_descends (prefixWord ++ tailWord_847626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847637 : List Nat := [1, 3, 2, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_847637 : Nat := 118140960795 + 847637 * 2 ^ 59
def prefixEnd_847637 : Nat := 4983230072969 + 3 ^ 40 * 847637 * 2
def baseEnd_847637 : Nat := 435245201535205350039295

theorem tailTrace_847637 : CollatzResearch.WordTrace tailWord_847637 prefixEnd_847637 435245201535205350039295 := by
  unfold tailWord_847637
  simp only [CollatzResearch.WordTrace]
  refine ⟨30915861230163388719389165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20610574153442259146259443 30915861230163388719389165)
  ·
    refine ⟨11593447961311270769770937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30915861230163388719389165 11593447961311270769770937)
    ·
      refine ⟨8695085970983453077328203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11593447961311270769770937 8695085970983453077328203)
      ·
        refine ⟨13042628956475179615992305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8695085970983453077328203 13042628956475179615992305)
        ·
          refine ⟨9781971717356384711994229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13042628956475179615992305 9781971717356384711994229)
          ·
            refine ⟨917059848502161066749459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9781971717356384711994229 917059848502161066749459)
            ·
              refine ⟨1375589772753241600124189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917059848502161066749459 1375589772753241600124189)
              ·
                refine ⟨515846164782465600046571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375589772753241600124189 515846164782465600046571)
                ·
                  refine ⟨773769247173698400069857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515846164782465600046571 773769247173698400069857)
                  ·
                    refine ⟨580326935380273800052393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 773769247173698400069857 580326935380273800052393)
                    ·
                      refine ⟨435245201535205350039295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 580326935380273800052393 435245201535205350039295)
                      ·
                        rfl

theorem cell23_847637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_847637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847637 prefixEnd_847637 := by exact prefixLift 847637
  have htrace : WordTrace (prefixWord ++ tailWord_847637) baseStart_847637 baseEnd_847637 := by
    simpa [prefixWord, tailWord_847637, baseEnd_847637] using wordTrace_append hprefix tailTrace_847637
  have hstable : (prefixWord ++ tailWord_847637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847637).length < 2 ^ (prefixWord ++ tailWord_847637).sum := by decide
  have hdescent : baseEnd_847637 < baseStart_847637 := by decide
  rcases family_descends (prefixWord ++ tailWord_847637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847729 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 1, 7]
def baseStart_847729 : Nat := 118140960795 + 847729 * 2 ^ 59
def prefixEnd_847729 : Nat := 4983230072969 + 3 ^ 40 * 847729 * 2
def baseEnd_847729 : Nat := 145097480585139663362957

theorem tailTrace_847729 : CollatzResearch.WordTrace tailWord_847729 prefixEnd_847729 145097480585139663362957 := by
  unfold tailWord_847729
  simp only [CollatzResearch.WordTrace]
  refine ⟨30919216745830088431738241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20612811163886725621158827 30919216745830088431738241)
  ·
    refine ⟨23189412559372566323803681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30919216745830088431738241 23189412559372566323803681)
    ·
      refine ⟨17392059419529424742852761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23189412559372566323803681 17392059419529424742852761)
      ·
        refine ⟨13044044564647068557139571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17392059419529424742852761 13044044564647068557139571)
        ·
          refine ⟨19566066846970602835709357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13044044564647068557139571 19566066846970602835709357)
          ·
            refine ⟨7337275067613976063391009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19566066846970602835709357 7337275067613976063391009)
            ·
              refine ⟨5502956300710482047543257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7337275067613976063391009 5502956300710482047543257)
              ·
                refine ⟨4127217225532861535657443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5502956300710482047543257 4127217225532861535657443)
                ·
                  refine ⟨6190825838299292303486165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127217225532861535657443 6190825838299292303486165)
                  ·
                    refine ⟨145097480585139663362957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6190825838299292303486165 145097480585139663362957)
                    ·
                      rfl

theorem cell23_847729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_847729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847729 prefixEnd_847729 := by exact prefixLift 847729
  have htrace : WordTrace (prefixWord ++ tailWord_847729) baseStart_847729 baseEnd_847729 := by
    simpa [prefixWord, tailWord_847729, baseEnd_847729] using wordTrace_append hprefix tailTrace_847729
  have hstable : (prefixWord ++ tailWord_847729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847729).length < 2 ^ (prefixWord ++ tailWord_847729).sum := by decide
  have hdescent : baseEnd_847729 < baseStart_847729 := by decide
  rcases family_descends (prefixWord ++ tailWord_847729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847769 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_847769 : Nat := 118140960795 + 847769 * 2 ^ 59
def prefixEnd_847769 : Nat := 4983230072969 + 3 ^ 40 * 847769 * 2
def baseEnd_847769 : Nat := 435312980981598833588687

theorem tailTrace_847769 : CollatzResearch.WordTrace tailWord_847769 prefixEnd_847769 435312980981598833588687 := by
  unfold tailWord_847769
  simp only [CollatzResearch.WordTrace]
  refine ⟨30920675665685175263194361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20613783777123450175462907 30920675665685175263194361)
  ·
    refine ⟨23190506749263881447395771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30920675665685175263194361 23190506749263881447395771)
    ·
      refine ⟨34785760123895822171093657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23190506749263881447395771 34785760123895822171093657)
      ·
        refine ⟨26089320092921866628320243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34785760123895822171093657 26089320092921866628320243)
        ·
          refine ⟨39133980139382799942480365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26089320092921866628320243 39133980139382799942480365)
          ·
            refine ⟨14675242552268549978430137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39133980139382799942480365 14675242552268549978430137)
            ·
              refine ⟨11006431914201412483822603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14675242552268549978430137 11006431914201412483822603)
              ·
                refine ⟨16509647871302118725733905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11006431914201412483822603 16509647871302118725733905)
                ·
                  refine ⟨12382235903476589044300429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16509647871302118725733905 12382235903476589044300429)
                  ·
                    refine ⟨4643338463803720891612661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12382235903476589044300429 4643338463803720891612661)
                    ·
                      refine ⟨435312980981598833588687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4643338463803720891612661 435312980981598833588687)
                      ·
                        rfl

theorem cell23_847769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_847769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847769 prefixEnd_847769 := by exact prefixLift 847769
  have htrace : WordTrace (prefixWord ++ tailWord_847769) baseStart_847769 baseEnd_847769 := by
    simpa [prefixWord, tailWord_847769, baseEnd_847769] using wordTrace_append hprefix tailTrace_847769
  have hstable : (prefixWord ++ tailWord_847769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847769).length < 2 ^ (prefixWord ++ tailWord_847769).sum := by decide
  have hdescent : baseEnd_847769 < baseStart_847769 := by decide
  rcases family_descends (prefixWord ++ tailWord_847769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847779 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 6]
def baseStart_847779 : Nat := 118140960795 + 847779 * 2 ^ 59
def prefixEnd_847779 : Nat := 4983230072969 + 3 ^ 40 * 847779 * 2
def baseEnd_847779 : Nat := 435318115788143794463641

theorem tailTrace_847779 : CollatzResearch.WordTrace tailWord_847779 prefixEnd_847779 435318115788143794463641 := by
  unfold tailWord_847779
  simp only [CollatzResearch.WordTrace]
  refine ⟨30921040395648946971058391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20614026930432631314038927 30921040395648946971058391)
  ·
    refine ⟨46381560593473420456587587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30921040395648946971058391 46381560593473420456587587)
    ·
      refine ⟨69572340890210130684881381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46381560593473420456587587 69572340890210130684881381)
      ·
        refine ⟨13044813916914399503415259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69572340890210130684881381 13044813916914399503415259)
        ·
          refine ⟨19567220875371599255122889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13044813916914399503415259 19567220875371599255122889)
          ·
            refine ⟨14675415656528699441342167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19567220875371599255122889 14675415656528699441342167)
            ·
              refine ⟨22013123484793049162013251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14675415656528699441342167 22013123484793049162013251)
              ·
                refine ⟨33019685227189573743019877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22013123484793049162013251 33019685227189573743019877)
                ·
                  refine ⟨6191190980098045076816227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33019685227189573743019877 6191190980098045076816227)
                  ·
                    refine ⟨9286786470147067615224341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6191190980098045076816227 9286786470147067615224341)
                    ·
                      refine ⟨435318115788143794463641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9286786470147067615224341 435318115788143794463641)
                      ·
                        rfl

theorem cell23_847779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_847779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847779 prefixEnd_847779 := by exact prefixLift 847779
  have htrace : WordTrace (prefixWord ++ tailWord_847779) baseStart_847779 baseEnd_847779 := by
    simpa [prefixWord, tailWord_847779, baseEnd_847779] using wordTrace_append hprefix tailTrace_847779
  have hstable : (prefixWord ++ tailWord_847779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847779).length < 2 ^ (prefixWord ++ tailWord_847779).sum := by decide
  have hdescent : baseEnd_847779 < baseStart_847779 := by decide
  rcases family_descends (prefixWord ++ tailWord_847779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847793 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 3, 4]
def baseStart_847793 : Nat := 118140960795 + 847793 * 2 ^ 59
def prefixEnd_847793 : Nat := 4983230072969 + 3 ^ 40 * 847793 * 2
def baseEnd_847793 : Nat := 145108434839102246562859

theorem tailTrace_847793 : CollatzResearch.WordTrace tailWord_847793 prefixEnd_847793 145108434839102246562859 := by
  unfold tailWord_847793
  simp only [CollatzResearch.WordTrace]
  refine ⟨30921551017598227362068033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20614367345065484908045355 30921551017598227362068033)
  ·
    refine ⟨23191163263198670521551025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30921551017598227362068033 23191163263198670521551025)
    ·
      refine ⟨17393372447399002891163269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23191163263198670521551025 17393372447399002891163269)
      ·
        refine ⟨3261257333887313042093113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17393372447399002891163269 3261257333887313042093113)
        ·
          refine ⟨2445943000415484781569835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3261257333887313042093113 2445943000415484781569835)
          ·
            refine ⟨3668914500623227172354753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445943000415484781569835 3668914500623227172354753)
            ·
              refine ⟨2751685875467420379266065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668914500623227172354753 2751685875467420379266065)
              ·
                refine ⟨2063764406600565284449549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2751685875467420379266065 2063764406600565284449549)
                ·
                  refine ⟨773911652475211981668581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2063764406600565284449549 773911652475211981668581)
                  ·
                    refine ⟨145108434839102246562859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773911652475211981668581 145108434839102246562859)
                    ·
                      rfl

theorem cell23_847793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_847793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847793 prefixEnd_847793 := by exact prefixLift 847793
  have htrace : WordTrace (prefixWord ++ tailWord_847793) baseStart_847793 baseEnd_847793 := by
    simpa [prefixWord, tailWord_847793, baseEnd_847793] using wordTrace_append hprefix tailTrace_847793
  have hstable : (prefixWord ++ tailWord_847793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847793).length < 2 ^ (prefixWord ++ tailWord_847793).sum := by decide
  have hdescent : baseEnd_847793 < baseStart_847793 := by decide
  rcases family_descends (prefixWord ++ tailWord_847793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847806 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_847806 : Nat := 118140960795 + 847806 * 2 ^ 59
def prefixEnd_847806 : Nat := 4983230072969 + 3 ^ 40 * 847806 * 2
def baseEnd_847806 : Nat := 48370219973979465425113

theorem tailTrace_847806 : CollatzResearch.WordTrace tailWord_847806 prefixEnd_847806 48370219973979465425113 := by
  unfold tailWord_847806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3865253145818891322786409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20614683444367420388194181 3865253145818891322786409)
  ·
    refine ⟨2898939859364168492089807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3865253145818891322786409 2898939859364168492089807)
    ·
      refine ⟨4348409789046252738134711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898939859364168492089807 4348409789046252738134711)
      ·
        refine ⟨6522614683569379107202067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348409789046252738134711 6522614683569379107202067)
        ·
          refine ⟨9783922025354068660803101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522614683569379107202067 9783922025354068660803101)
          ·
            refine ⟨3668970759507775747801163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9783922025354068660803101 3668970759507775747801163)
            ·
              refine ⟨5503456139261663621701745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668970759507775747801163 5503456139261663621701745)
              ·
                refine ⟨4127592104446247716276309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503456139261663621701745 4127592104446247716276309)
                ·
                  refine ⟨48370219973979465425113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4127592104446247716276309 48370219973979465425113)
                  ·
                    rfl

theorem cell23_847806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_847806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847806 prefixEnd_847806 := by exact prefixLift 847806
  have htrace : WordTrace (prefixWord ++ tailWord_847806) baseStart_847806 baseEnd_847806 := by
    simpa [prefixWord, tailWord_847806, baseEnd_847806] using wordTrace_append hprefix tailTrace_847806
  have hstable : (prefixWord ++ tailWord_847806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847806).length < 2 ^ (prefixWord ++ tailWord_847806).sum := by decide
  have hdescent : baseEnd_847806 < baseStart_847806 := by decide
  rcases family_descends (prefixWord ++ tailWord_847806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847878 : List Nat := [6, 2, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_847878 : Nat := 118140960795 + 847878 * 2 ^ 59
def prefixEnd_847878 : Nat := 4983230072969 + 3 ^ 40 * 847878 * 2
def baseEnd_847878 : Nat := 145122983457646302375229

theorem tailTrace_847878 : CollatzResearch.WordTrace tailWord_847878 prefixEnd_847878 145122983457646302375229 := by
  unfold tailWord_847878
  simp only [CollatzResearch.WordTrace]
  refine ⟨966395350696571464966009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20616434148193524585941525 966395350696571464966009)
  ·
    refine ⟨724796513022428598724507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 966395350696571464966009 724796513022428598724507)
    ·
      refine ⟨1087194769533642898086761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724796513022428598724507 1087194769533642898086761)
      ·
        refine ⟨815396077150232173565071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1087194769533642898086761 815396077150232173565071)
        ·
          refine ⟨1223094115725348260347607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815396077150232173565071 1223094115725348260347607)
          ·
            refine ⟨1834641173588022390521411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223094115725348260347607 1834641173588022390521411)
            ·
              refine ⟨2751961760382033585782117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834641173588022390521411 2751961760382033585782117)
              ·
                refine ⟨515992830071631297334147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2751961760382033585782117 515992830071631297334147)
                ·
                  refine ⟨773989245107446946001221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515992830071631297334147 773989245107446946001221)
                  ·
                    refine ⟨145122983457646302375229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773989245107446946001221 145122983457646302375229)
                    ·
                      rfl

theorem cell23_847878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_847878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847878 prefixEnd_847878 := by exact prefixLift 847878
  have htrace : WordTrace (prefixWord ++ tailWord_847878) baseStart_847878 baseEnd_847878 := by
    simpa [prefixWord, tailWord_847878, baseEnd_847878] using wordTrace_append hprefix tailTrace_847878
  have hstable : (prefixWord ++ tailWord_847878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847878).length < 2 ^ (prefixWord ++ tailWord_847878).sum := by decide
  have hdescent : baseEnd_847878 < baseStart_847878 := by decide
  rcases family_descends (prefixWord ++ tailWord_847878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847900 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_847900 : Nat := 118140960795 + 847900 * 2 ^ 59
def prefixEnd_847900 : Nat := 4983230072969 + 3 ^ 40 * 847900 * 2
def baseEnd_847900 : Nat := 145126748982445940350195

theorem tailTrace_847900 : CollatzResearch.WordTrace tailWord_847900 prefixEnd_847900 145126748982445940350195 := by
  unfold tailWord_847900
  simp only [CollatzResearch.WordTrace]
  refine ⟨15462726814105292318106577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20616969085473723090808769 15462726814105292318106577)
  ·
    refine ⟨11597045110578969238579933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15462726814105292318106577 11597045110578969238579933)
    ·
      refine ⟨4348891916467113464467475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11597045110578969238579933 4348891916467113464467475)
      ·
        refine ⟨6523337874700670196701213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348891916467113464467475 6523337874700670196701213)
        ·
          refine ⟨2446251703012751323762955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6523337874700670196701213 2446251703012751323762955)
          ·
            refine ⟨3669377554519126985644433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446251703012751323762955 3669377554519126985644433)
            ·
              refine ⟨2752033165889345239233325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3669377554519126985644433 2752033165889345239233325)
              ·
                refine ⟨1032012437208504464712497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2752033165889345239233325 1032012437208504464712497)
                ·
                  refine ⟨774009327906378348534373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032012437208504464712497 774009327906378348534373)
                  ·
                    refine ⟨145126748982445940350195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774009327906378348534373 145126748982445940350195)
                    ·
                      rfl

theorem cell23_847900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_847900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847900 prefixEnd_847900 := by exact prefixLift 847900
  have htrace : WordTrace (prefixWord ++ tailWord_847900) baseStart_847900 baseEnd_847900 := by
    simpa [prefixWord, tailWord_847900, baseEnd_847900] using wordTrace_append hprefix tailTrace_847900
  have hstable : (prefixWord ++ tailWord_847900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847900).length < 2 ^ (prefixWord ++ tailWord_847900).sum := by decide
  have hdescent : baseEnd_847900 < baseStart_847900 := by decide
  rcases family_descends (prefixWord ++ tailWord_847900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847903 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 4]
def baseStart_847903 : Nat := 118140960795 + 847903 * 2 ^ 59
def prefixEnd_847903 : Nat := 4983230072969 + 3 ^ 40 * 847903 * 2
def baseEnd_847903 : Nat := 435381787389301309313071

theorem tailTrace_847903 : CollatzResearch.WordTrace tailWord_847903 prefixEnd_847903 435381787389301309313071 := by
  unfold tailWord_847903
  simp only [CollatzResearch.WordTrace]
  refine ⟨30925563047199716148572363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20617042031466477432381575 30925563047199716148572363)
  ·
    refine ⟨46388344570799574222858545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30925563047199716148572363 46388344570799574222858545)
    ·
      refine ⟨34791258428099680667143909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46388344570799574222858545 34791258428099680667143909)
      ·
        refine ⟨6523360955268690125089483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34791258428099680667143909 6523360955268690125089483)
        ·
          refine ⟨9785041432903035187634225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6523360955268690125089483 9785041432903035187634225)
          ·
            refine ⟨7338781074677276390725669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9785041432903035187634225 7338781074677276390725669)
            ·
              refine ⟨1376021451501989323261063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7338781074677276390725669 1376021451501989323261063)
              ·
                refine ⟨2064032177252983984891595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376021451501989323261063 2064032177252983984891595)
                ·
                  refine ⟨3096048265879475977337393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064032177252983984891595 3096048265879475977337393)
                  ·
                    refine ⟨2322036199409606983003045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3096048265879475977337393 2322036199409606983003045)
                    ·
                      refine ⟨435381787389301309313071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2322036199409606983003045 435381787389301309313071)
                      ·
                        rfl

theorem cell23_847903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_847903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847903 prefixEnd_847903 := by exact prefixLift 847903
  have htrace : WordTrace (prefixWord ++ tailWord_847903) baseStart_847903 baseEnd_847903 := by
    simpa [prefixWord, tailWord_847903, baseEnd_847903] using wordTrace_append hprefix tailTrace_847903
  have hstable : (prefixWord ++ tailWord_847903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847903).length < 2 ^ (prefixWord ++ tailWord_847903).sum := by decide
  have hdescent : baseEnd_847903 < baseStart_847903 := by decide
  rcases family_descends (prefixWord ++ tailWord_847903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847911 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_847911 : Nat := 118140960795 + 847911 * 2 ^ 59
def prefixEnd_847911 : Nat := 4983230072969 + 3 ^ 40 * 847911 * 2
def baseEnd_847911 : Nat := 435385895234537278013035

theorem tailTrace_847911 : CollatzResearch.WordTrace tailWord_847911 prefixEnd_847911 435385895234537278013035 := by
  unfold tailWord_847911
  simp only [CollatzResearch.WordTrace]
  refine ⟨30925854831170733514863587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20617236554113822343242391 30925854831170733514863587)
  ·
    refine ⟨46388782246756100272295381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30925854831170733514863587 46388782246756100272295381)
    ·
      refine ⟨1087237083908346100131923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46388782246756100272295381 1087237083908346100131923)
      ·
        refine ⟨1630855625862519150197885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087237083908346100131923 1630855625862519150197885)
        ·
          refine ⟨611570859698444681324207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1630855625862519150197885 611570859698444681324207)
          ·
            refine ⟨917356289547667021986311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611570859698444681324207 917356289547667021986311)
            ·
              refine ⟨1376034434321500532979467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917356289547667021986311 1376034434321500532979467)
              ·
                refine ⟨2064051651482250799469201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376034434321500532979467 2064051651482250799469201)
                ·
                  refine ⟨1548038738611688099601901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2064051651482250799469201 1548038738611688099601901)
                  ·
                    refine ⟨580514526979383037350713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548038738611688099601901 580514526979383037350713)
                    ·
                      refine ⟨435385895234537278013035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 580514526979383037350713 435385895234537278013035)
                      ·
                        rfl

theorem cell23_847911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_847911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847911 prefixEnd_847911 := by exact prefixLift 847911
  have htrace : WordTrace (prefixWord ++ tailWord_847911) baseStart_847911 baseEnd_847911 := by
    simpa [prefixWord, tailWord_847911, baseEnd_847911] using wordTrace_append hprefix tailTrace_847911
  have hstable : (prefixWord ++ tailWord_847911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847911).length < 2 ^ (prefixWord ++ tailWord_847911).sum := by decide
  have hdescent : baseEnd_847911 < baseStart_847911 := by decide
  rcases family_descends (prefixWord ++ tailWord_847911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847923 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 3]
def baseStart_847923 : Nat := 118140960795 + 847923 * 2 ^ 59
def prefixEnd_847923 : Nat := 4983230072969 + 3 ^ 40 * 847923 * 2
def baseEnd_847923 : Nat := 435392057002391231062979

theorem tailTrace_847923 : CollatzResearch.WordTrace tailWord_847923 prefixEnd_847923 435392057002391231062979 := by
  unfold tailWord_847923
  simp only [CollatzResearch.WordTrace]
  refine ⟨30926292507127259564300423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20617528338084839709533615 30926292507127259564300423)
  ·
    refine ⟨46389438760690889346450635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30926292507127259564300423 46389438760690889346450635)
    ·
      refine ⟨69584158141036334019675953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46389438760690889346450635 69584158141036334019675953)
      ·
        refine ⟨52188118605777250514756965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69584158141036334019675953 52188118605777250514756965)
        ·
          refine ⟨9785272238583234471516931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52188118605777250514756965 9785272238583234471516931)
          ·
            refine ⟨14677908357874851707275397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785272238583234471516931 14677908357874851707275397)
            ·
              refine ⟨2752107817101534695114137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14677908357874851707275397 2752107817101534695114137)
              ·
                refine ⟨2064080862826151021335603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2752107817101534695114137 2064080862826151021335603)
                ·
                  refine ⟨3096121294239226532003405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064080862826151021335603 3096121294239226532003405)
                  ·
                    refine ⟨1161045485339709949501277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096121294239226532003405 1161045485339709949501277)
                    ·
                      refine ⟨435392057002391231062979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1161045485339709949501277 435392057002391231062979)
                      ·
                        rfl

theorem cell23_847923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_847923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847923 prefixEnd_847923 := by exact prefixLift 847923
  have htrace : WordTrace (prefixWord ++ tailWord_847923) baseStart_847923 baseEnd_847923 := by
    simpa [prefixWord, tailWord_847923, baseEnd_847923] using wordTrace_append hprefix tailTrace_847923
  have hstable : (prefixWord ++ tailWord_847923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847923).length < 2 ^ (prefixWord ++ tailWord_847923).sum := by decide
  have hdescent : baseEnd_847923 < baseStart_847923 := by decide
  rcases family_descends (prefixWord ++ tailWord_847923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847934 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_847934 : Nat := 118140960795 + 847934 * 2 ^ 59
def prefixEnd_847934 : Nat := 4983230072969 + 3 ^ 40 * 847934 * 2
def baseEnd_847934 : Nat := 145132568429863562675143

theorem tailTrace_847934 : CollatzResearch.WordTrace tailWord_847934 prefixEnd_847934 145132568429863562675143 := by
  unfold tailWord_847934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3865836713760926055368857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20617795806724938961967237 3865836713760926055368857)
  ·
    refine ⟨2899377535320694541526643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3865836713760926055368857 2899377535320694541526643)
    ·
      refine ⟨4349066302981041812289965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2899377535320694541526643 4349066302981041812289965)
      ·
        refine ⟨1630899863617890679608737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4349066302981041812289965 1630899863617890679608737)
        ·
          refine ⟨1223174897713418009706553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630899863617890679608737 1223174897713418009706553)
          ·
            refine ⟨917381173285063507279915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223174897713418009706553 917381173285063507279915)
            ·
              refine ⟨1376071759927595260919873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917381173285063507279915 1376071759927595260919873)
              ·
                refine ⟨1032053819945696445689905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376071759927595260919873 1032053819945696445689905)
                ·
                  refine ⟨774040364959272334267429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032053819945696445689905 774040364959272334267429)
                  ·
                    refine ⟨145132568429863562675143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774040364959272334267429 145132568429863562675143)
                    ·
                      rfl

theorem cell23_847934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_847934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847934 prefixEnd_847934 := by exact prefixLift 847934
  have htrace : WordTrace (prefixWord ++ tailWord_847934) baseStart_847934 baseEnd_847934 := by
    simpa [prefixWord, tailWord_847934, baseEnd_847934] using wordTrace_append hprefix tailTrace_847934
  have hstable : (prefixWord ++ tailWord_847934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847934).length < 2 ^ (prefixWord ++ tailWord_847934).sum := by decide
  have hdescent : baseEnd_847934 < baseStart_847934 := by decide
  rcases family_descends (prefixWord ++ tailWord_847934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847983 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_847983 : Nat := 118140960795 + 847983 * 2 ^ 59
def prefixEnd_847983 : Nat := 4983230072969 + 3 ^ 40 * 847983 * 2
def baseEnd_847983 : Nat := 435422865841660996312703

theorem tailTrace_847983 : CollatzResearch.WordTrace tailWord_847983 prefixEnd_847983 435422865841660996312703 := by
  unfold tailWord_847983
  simp only [CollatzResearch.WordTrace]
  refine ⟨30928480886909889811484603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20618987257939926540989735 30928480886909889811484603)
  ·
    refine ⟨46392721330364834717226905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30928480886909889811484603 46392721330364834717226905)
    ·
      refine ⟨34794540997773626037920179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46392721330364834717226905 34794540997773626037920179)
      ·
        refine ⟨52191811496660439056880269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34794540997773626037920179 52191811496660439056880269)
        ·
          refine ⟨19571929311247664646330101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52191811496660439056880269 19571929311247664646330101)
          ·
            refine ⟨1834868372929468560593447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19571929311247664646330101 1834868372929468560593447)
            ·
              refine ⟨2752302559394202840890171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834868372929468560593447 2752302559394202840890171)
              ·
                refine ⟨4128453839091304261335257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752302559394202840890171 4128453839091304261335257)
                ·
                  refine ⟨3096340379318478196001443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4128453839091304261335257 3096340379318478196001443)
                  ·
                    refine ⟨4644510568977717294002165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3096340379318478196001443 4644510568977717294002165)
                    ·
                      refine ⟨435422865841660996312703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4644510568977717294002165 435422865841660996312703)
                      ·
                        rfl

theorem cell23_847983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_847983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847983 prefixEnd_847983 := by exact prefixLift 847983
  have htrace : WordTrace (prefixWord ++ tailWord_847983) baseStart_847983 baseEnd_847983 := by
    simpa [prefixWord, tailWord_847983, baseEnd_847983] using wordTrace_append hprefix tailTrace_847983
  have hstable : (prefixWord ++ tailWord_847983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847983).length < 2 ^ (prefixWord ++ tailWord_847983).sum := by decide
  have hdescent : baseEnd_847983 < baseStart_847983 := by decide
  rcases family_descends (prefixWord ++ tailWord_847983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847997 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_847997 : Nat := 118140960795 + 847997 * 2 ^ 59
def prefixEnd_847997 : Nat := 4983230072969 + 3 ^ 40 * 847997 * 2
def baseEnd_847997 : Nat := 435430054570823941537639

theorem tailTrace_847997 : CollatzResearch.WordTrace tailWord_847997 prefixEnd_847997 435430054570823941537639 := by
  unfold tailWord_847997
  simp only [CollatzResearch.WordTrace]
  refine ⟨30928991508859170202494245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20619327672572780134996163 30928991508859170202494245)
  ·
    refine ⟨5799185907911094412967671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30928991508859170202494245 5799185907911094412967671)
    ·
      refine ⟨8698778861866641619451507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5799185907911094412967671 8698778861866641619451507)
      ·
        refine ⟨13048168292799962429177261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8698778861866641619451507 13048168292799962429177261)
        ·
          refine ⟨4893063109799985910941473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13048168292799962429177261 4893063109799985910941473)
          ·
            refine ⟨3669797332349989433206105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4893063109799985910941473 3669797332349989433206105)
            ·
              refine ⟨2752347999262492074904579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3669797332349989433206105 2752347999262492074904579)
              ·
                refine ⟨4128521998893738112356869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752347999262492074904579 4128521998893738112356869)
                ·
                  refine ⟨774097874792575896066913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4128521998893738112356869 774097874792575896066913)
                  ·
                    refine ⟨580573406094431922050185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 774097874792575896066913 580573406094431922050185)
                    ·
                      refine ⟨435430054570823941537639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 580573406094431922050185 435430054570823941537639)
                      ·
                        rfl

theorem cell23_847997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_847997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_847997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_847997 prefixEnd_847997 := by exact prefixLift 847997
  have htrace : WordTrace (prefixWord ++ tailWord_847997) baseStart_847997 baseEnd_847997 := by
    simpa [prefixWord, tailWord_847997, baseEnd_847997] using wordTrace_append hprefix tailTrace_847997
  have hstable : (prefixWord ++ tailWord_847997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847997).length < 2 ^ (prefixWord ++ tailWord_847997).sum := by decide
  have hdescent : baseEnd_847997 < baseStart_847997 := by decide
  rcases family_descends (prefixWord ++ tailWord_847997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848003 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 7]
def baseStart_848003 : Nat := 118140960795 + 848003 * 2 ^ 59
def prefixEnd_848003 : Nat := 4983230072969 + 3 ^ 40 * 848003 * 2
def baseEnd_848003 : Nat := 48381459494972324229179

theorem tailTrace_848003 : CollatzResearch.WordTrace tailWord_848003 prefixEnd_848003 48381459494972324229179 := by
  unfold tailWord_848003
  simp only [CollatzResearch.WordTrace]
  refine ⟨30929210346837433227212663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20619473564558288818141775 30929210346837433227212663)
  ·
    refine ⟨46393815520256149840818995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30929210346837433227212663 46393815520256149840818995)
    ·
      refine ⟨69590723280384224761228493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46393815520256149840818995 69590723280384224761228493)
      ·
        refine ⟨26096521230144084285460685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69590723280384224761228493 26096521230144084285460685)
        ·
          refine ⟨9786195461304031607047757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26096521230144084285460685 9786195461304031607047757)
          ·
            refine ⟨3669823297989011852642909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9786195461304031607047757 3669823297989011852642909)
            ·
              refine ⟨1376183736745879444741091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3669823297989011852642909 1376183736745879444741091)
              ·
                refine ⟨2064275605118819167111637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376183736745879444741091 2064275605118819167111637)
                ·
                  refine ⟨48381459494972324229179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2064275605118819167111637 48381459494972324229179)
                  ·
                    rfl

theorem cell23_848003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 7].length) (baseStart_848003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848003 prefixEnd_848003 := by exact prefixLift 848003
  have htrace : WordTrace (prefixWord ++ tailWord_848003) baseStart_848003 baseEnd_848003 := by
    simpa [prefixWord, tailWord_848003, baseEnd_848003] using wordTrace_append hprefix tailTrace_848003
  have hstable : (prefixWord ++ tailWord_848003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848003).length < 2 ^ (prefixWord ++ tailWord_848003).sum := by decide
  have hdescent : baseEnd_848003 < baseStart_848003 := by decide
  rcases family_descends (prefixWord ++ tailWord_848003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848113 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_848113 : Nat := 118140960795 + 848113 * 2 ^ 59
def prefixEnd_848113 : Nat := 4983230072969 + 3 ^ 40 * 848113 * 2
def baseEnd_848113 : Nat := 435489618326745487687105

theorem tailTrace_848113 : CollatzResearch.WordTrace tailWord_848113 prefixEnd_848113 435489618326745487687105 := by
  unfold tailWord_848113
  simp only [CollatzResearch.WordTrace]
  refine ⟨30933222376438922013716993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20622148250959281342477995 30933222376438922013716993)
  ·
    refine ⟨23199916782329191510287745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30933222376438922013716993 23199916782329191510287745)
    ·
      refine ⟨17399937586746893632715809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23199916782329191510287745 17399937586746893632715809)
      ·
        refine ⟨13049953190060170224536857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17399937586746893632715809 13049953190060170224536857)
        ·
          refine ⟨9787464892545127668402643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13049953190060170224536857 9787464892545127668402643)
          ·
            refine ⟨14681197338817691502603965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9787464892545127668402643 14681197338817691502603965)
            ·
              refine ⟨5505449002056634313476487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14681197338817691502603965 5505449002056634313476487)
              ·
                refine ⟨8258173503084951470214731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505449002056634313476487 8258173503084951470214731)
                ·
                  refine ⟨12387260254627427205322097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8258173503084951470214731 12387260254627427205322097)
                  ·
                    refine ⟨9290445190970570403991573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12387260254627427205322097 9290445190970570403991573)
                    ·
                      refine ⟨435489618326745487687105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9290445190970570403991573 435489618326745487687105)
                      ·
                        rfl

theorem cell23_848113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_848113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848113 prefixEnd_848113 := by exact prefixLift 848113
  have htrace : WordTrace (prefixWord ++ tailWord_848113) baseStart_848113 baseEnd_848113 := by
    simpa [prefixWord, tailWord_848113, baseEnd_848113] using wordTrace_append hprefix tailTrace_848113
  have hstable : (prefixWord ++ tailWord_848113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848113).length < 2 ^ (prefixWord ++ tailWord_848113).sum := by decide
  have hdescent : baseEnd_848113 < baseStart_848113 := by decide
  rcases family_descends (prefixWord ++ tailWord_848113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848114 : List Nat := [3, 2, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_848114 : Nat := 118140960795 + 848114 * 2 ^ 59
def prefixEnd_848114 : Nat := 4983230072969 + 3 ^ 40 * 848114 * 2
def baseEnd_848114 : Nat := 145163377269133327924867

theorem tailTrace_848114 : CollatzResearch.WordTrace tailWord_848114 prefixEnd_848114 145163377269133327924867 := by
  unfold tailWord_848114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733314712358824796125849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20622172566290199456335597 7733314712358824796125849)
  ·
    refine ⟨5799986034269118597094387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7733314712358824796125849 5799986034269118597094387)
    ·
      refine ⟨8699979051403677895641581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5799986034269118597094387 8699979051403677895641581)
      ·
        refine ⟨3262492144276379210865593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8699979051403677895641581 3262492144276379210865593)
        ·
          refine ⟨2446869108207284408149195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3262492144276379210865593 2446869108207284408149195)
          ·
            refine ⟨3670303662310926612223793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446869108207284408149195 3670303662310926612223793)
            ·
              refine ⟨2752727746733194959167845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3670303662310926612223793 2752727746733194959167845)
              ·
                refine ⟨516136452512474054843971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2752727746733194959167845 516136452512474054843971)
                ·
                  refine ⟨774204678768711082265957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516136452512474054843971 774204678768711082265957)
                  ·
                    refine ⟨145163377269133327924867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774204678768711082265957 145163377269133327924867)
                    ·
                      rfl

theorem cell23_848114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_848114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848114 prefixEnd_848114 := by exact prefixLift 848114
  have htrace : WordTrace (prefixWord ++ tailWord_848114) baseStart_848114 baseEnd_848114 := by
    simpa [prefixWord, tailWord_848114, baseEnd_848114] using wordTrace_append hprefix tailTrace_848114
  have hstable : (prefixWord ++ tailWord_848114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848114).length < 2 ^ (prefixWord ++ tailWord_848114).sum := by decide
  have hdescent : baseEnd_848114 < baseStart_848114 := by decide
  rcases family_descends (prefixWord ++ tailWord_848114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848137 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 3]
def baseStart_848137 : Nat := 118140960795 + 848137 * 2 ^ 59
def prefixEnd_848137 : Nat := 4983230072969 + 3 ^ 40 * 848137 * 2
def baseEnd_848137 : Nat := 435501941862453393786995

theorem tailTrace_848137 : CollatzResearch.WordTrace tailWord_848137 prefixEnd_848137 435501941862453393786995 := by
  unfold tailWord_848137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30934097728351974112590665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20622731818901316075060443 30934097728351974112590665)
  ·
    refine ⟨23200573296263980584442999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30934097728351974112590665 23200573296263980584442999)
    ·
      refine ⟨34800859944395970876664499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23200573296263980584442999 34800859944395970876664499)
      ·
        refine ⟨52201289916593956314996749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34800859944395970876664499 52201289916593956314996749)
        ·
          refine ⟨19575483718722733618123781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52201289916593956314996749 19575483718722733618123781)
          ·
            refine ⟨3670403197260512553398209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19575483718722733618123781 3670403197260512553398209)
            ·
              refine ⟨2752802397945384415048657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3670403197260512553398209 2752802397945384415048657)
              ·
                refine ⟨2064601798459038311286493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2752802397945384415048657 2064601798459038311286493)
                ·
                  refine ⟨774225674422139366732435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2064601798459038311286493 774225674422139366732435)
                  ·
                    refine ⟨1161338511633209050098653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 774225674422139366732435 1161338511633209050098653)
                    ·
                      refine ⟨435501941862453393786995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1161338511633209050098653 435501941862453393786995)
                      ·
                        rfl

theorem cell23_848137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 3].length) (baseStart_848137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848137 prefixEnd_848137 := by exact prefixLift 848137
  have htrace : WordTrace (prefixWord ++ tailWord_848137) baseStart_848137 baseEnd_848137 := by
    simpa [prefixWord, tailWord_848137, baseEnd_848137] using wordTrace_append hprefix tailTrace_848137
  have hstable : (prefixWord ++ tailWord_848137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848137).length < 2 ^ (prefixWord ++ tailWord_848137).sum := by decide
  have hdescent : baseEnd_848137 < baseStart_848137 := by decide
  rcases family_descends (prefixWord ++ tailWord_848137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848143 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_848143 : Nat := 118140960795 + 848143 * 2 ^ 59
def prefixEnd_848143 : Nat := 4983230072969 + 3 ^ 40 * 848143 * 2
def baseEnd_848143 : Nat := 435505022746380370311967

theorem tailTrace_848143 : CollatzResearch.WordTrace tailWord_848143 prefixEnd_848143 435505022746380370311967 := by
  unfold tailWord_848143
  simp only [CollatzResearch.WordTrace]
  refine ⟨30934316566330237137309083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20622877710886824758206055 30934316566330237137309083)
  ·
    refine ⟨46401474849495355705963625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30934316566330237137309083 46401474849495355705963625)
    ·
      refine ⟨34801106137121516779472719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46401474849495355705963625 34801106137121516779472719)
      ·
        refine ⟨52201659205682275169209079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34801106137121516779472719 52201659205682275169209079)
        ·
          refine ⟨78302488808523412753813619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52201659205682275169209079 78302488808523412753813619)
          ·
            refine ⟨117453733212785119130720429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78302488808523412753813619 117453733212785119130720429)
            ·
              refine ⟨44045149954794419674020161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117453733212785119130720429 44045149954794419674020161)
              ·
                refine ⟨33033862466095814755515121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44045149954794419674020161 33033862466095814755515121)
                ·
                  refine ⟨24775396849571861066636341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33033862466095814755515121 24775396849571861066636341)
                  ·
                    refine ⟨2322693454647361974997157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24775396849571861066636341 2322693454647361974997157)
                    ·
                      refine ⟨435505022746380370311967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2322693454647361974997157 435505022746380370311967)
                      ·
                        rfl

theorem cell23_848143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_848143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848143 prefixEnd_848143 := by exact prefixLift 848143
  have htrace : WordTrace (prefixWord ++ tailWord_848143) baseStart_848143 baseEnd_848143 := by
    simpa [prefixWord, tailWord_848143, baseEnd_848143] using wordTrace_append hprefix tailTrace_848143
  have hstable : (prefixWord ++ tailWord_848143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848143).length < 2 ^ (prefixWord ++ tailWord_848143).sum := by decide
  have hdescent : baseEnd_848143 < baseStart_848143 := by decide
  rcases family_descends (prefixWord ++ tailWord_848143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848164 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_848164 : Nat := 118140960795 + 848164 * 2 ^ 59
def prefixEnd_848164 : Nat := 4983230072969 + 3 ^ 40 * 848164 * 2
def baseEnd_848164 : Nat := 435515805840124788149371

theorem tailTrace_848164 : CollatzResearch.WordTrace tailWord_848164 prefixEnd_848164 435515805840124788149371 := by
  unfold tailWord_848164
  simp only [CollatzResearch.WordTrace]
  refine ⟨15467541249627078861911773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20623388332836105149215697 15467541249627078861911773)
  ·
    refine ⟨5800327968610154573216915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15467541249627078861911773 5800327968610154573216915)
    ·
      refine ⟨8700491952915231859825373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5800327968610154573216915 8700491952915231859825373)
      ·
        refine ⟨3262684482343211947434515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8700491952915231859825373 3262684482343211947434515)
        ·
          refine ⟨4894026723514817921151773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262684482343211947434515 4894026723514817921151773)
          ·
            refine ⟨1835260021318056720431915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4894026723514817921151773 1835260021318056720431915)
            ·
              refine ⟨2752890031977085080647873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835260021318056720431915 2752890031977085080647873)
              ·
                refine ⟨2064667523982813810485905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2752890031977085080647873 2064667523982813810485905)
                ·
                  refine ⟨1548500642987110357864429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2064667523982813810485905 1548500642987110357864429)
                  ·
                    refine ⟨580687741120166384199161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548500642987110357864429 580687741120166384199161)
                    ·
                      refine ⟨435515805840124788149371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 580687741120166384199161 435515805840124788149371)
                      ·
                        rfl

theorem cell23_848164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_848164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848164 prefixEnd_848164 := by exact prefixLift 848164
  have htrace : WordTrace (prefixWord ++ tailWord_848164) baseStart_848164 baseEnd_848164 := by
    simpa [prefixWord, tailWord_848164, baseEnd_848164] using wordTrace_append hprefix tailTrace_848164
  have hstable : (prefixWord ++ tailWord_848164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848164).length < 2 ^ (prefixWord ++ tailWord_848164).sum := by decide
  have hdescent : baseEnd_848164 < baseStart_848164 := by decide
  rcases family_descends (prefixWord ++ tailWord_848164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848260 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_848260 : Nat := 118140960795 + 848260 * 2 ^ 59
def prefixEnd_848260 : Nat := 4983230072969 + 3 ^ 40 * 848260 * 2
def baseEnd_848260 : Nat := 145188366660985470849643

theorem tailTrace_848260 : CollatzResearch.WordTrace tailWord_848260 prefixEnd_848260 145188366660985470849643 := by
  unfold tailWord_848260
  simp only [CollatzResearch.WordTrace]
  refine ⟨15469291953453183059659117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20625722604604244079545489 15469291953453183059659117)
  ·
    refine ⟨5800984482544943647372169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15469291953453183059659117 5800984482544943647372169)
    ·
      refine ⟨4350738361908707735529127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5800984482544943647372169 4350738361908707735529127)
      ·
        refine ⟨6526107542863061603293691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4350738361908707735529127 6526107542863061603293691)
        ·
          refine ⟨9789161314294592404940537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526107542863061603293691 9789161314294592404940537)
          ·
            refine ⟨7341870985720944303705403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9789161314294592404940537 7341870985720944303705403)
            ·
              refine ⟨11012806478581416455558105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7341870985720944303705403 11012806478581416455558105)
              ·
                refine ⟨8259604858936062341668579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11012806478581416455558105 8259604858936062341668579)
                ·
                  refine ⟨12389407288404093512502869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8259604858936062341668579 12389407288404093512502869)
                  ·
                    refine ⟨145188366660985470849643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12389407288404093512502869 145188366660985470849643)
                    ·
                      rfl

theorem cell23_848260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_848260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848260 prefixEnd_848260 := by exact prefixLift 848260
  have htrace : WordTrace (prefixWord ++ tailWord_848260) baseStart_848260 baseEnd_848260 := by
    simpa [prefixWord, tailWord_848260, baseEnd_848260] using wordTrace_append hprefix tailTrace_848260
  have hstable : (prefixWord ++ tailWord_848260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848260).length < 2 ^ (prefixWord ++ tailWord_848260).sum := by decide
  have hdescent : baseEnd_848260 < baseStart_848260 := by decide
  rcases family_descends (prefixWord ++ tailWord_848260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848341 : List Nat := [1, 3, 2, 3, 1, 3, 3, 2, 5]
def baseStart_848341 : Nat := 118140960795 + 848341 * 2 ^ 59
def prefixEnd_848341 : Nat := 4983230072969 + 3 ^ 40 * 848341 * 2
def baseEnd_848341 : Nat := 48400743546218955070673

theorem tailTrace_848341 : CollatzResearch.WordTrace tailWord_848341 prefixEnd_848341 48400743546218955070673 := by
  unfold tailWord_848341
  simp only [CollatzResearch.WordTrace]
  refine ⟨30941538219612916953016877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20627692146408611302011251 30941538219612916953016877)
  ·
    refine ⟨11603076832354843857381329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30941538219612916953016877 11603076832354843857381329)
    ·
      refine ⟨8702307624266132893035997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11603076832354843857381329 8702307624266132893035997)
      ·
        refine ⟨3263365359099799834888499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8702307624266132893035997 3263365359099799834888499)
        ·
          refine ⟨4895048038649699752332749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263365359099799834888499 4895048038649699752332749)
          ·
            refine ⟨1835643014493637407124781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4895048038649699752332749 1835643014493637407124781)
            ·
              refine ⟨688366130435114027671793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1835643014493637407124781 688366130435114027671793)
              ·
                refine ⟨516274597826335520753845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688366130435114027671793 516274597826335520753845)
                ·
                  refine ⟨48400743546218955070673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 516274597826335520753845 48400743546218955070673)
                  ·
                    rfl

theorem cell23_848341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_848341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848341 prefixEnd_848341 := by exact prefixLift 848341
  have htrace : WordTrace (prefixWord ++ tailWord_848341) baseStart_848341 baseEnd_848341 := by
    simpa [prefixWord, tailWord_848341, baseEnd_848341] using wordTrace_append hprefix tailTrace_848341
  have hstable : (prefixWord ++ tailWord_848341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848341).length < 2 ^ (prefixWord ++ tailWord_848341).sum := by decide
  have hdescent : baseEnd_848341 < baseStart_848341 := by decide
  rcases family_descends (prefixWord ++ tailWord_848341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848367 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 5, 4]
def baseStart_848367 : Nat := 118140960795 + 848367 * 2 ^ 59
def prefixEnd_848367 : Nat := 4983230072969 + 3 ^ 40 * 848367 * 2
def baseEnd_848367 : Nat := 145206680804329164636979

theorem tailTrace_848367 : CollatzResearch.WordTrace tailWord_848367 prefixEnd_848367 145206680804329164636979 := by
  unfold tailWord_848367
  simp only [CollatzResearch.WordTrace]
  refine ⟨30942486517518723393463355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20628324345012482262308903 30942486517518723393463355)
  ·
    refine ⟨46413729776278085090195033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30942486517518723393463355 46413729776278085090195033)
    ·
      refine ⟨34810297332208563817646275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46413729776278085090195033 34810297332208563817646275)
      ·
        refine ⟨52215445998312845726469413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34810297332208563817646275 52215445998312845726469413)
        ·
          refine ⟨9790396124683658573713015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52215445998312845726469413 9790396124683658573713015)
          ·
            refine ⟨14685594187025487860569523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9790396124683658573713015 14685594187025487860569523)
            ·
              refine ⟨22028391280538231790854285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14685594187025487860569523 22028391280538231790854285)
              ·
                refine ⟨8260646730201836921570357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22028391280538231790854285 8260646730201836921570357)
                ·
                  refine ⟨774435630956422211397221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8260646730201836921570357 774435630956422211397221)
                  ·
                    refine ⟨145206680804329164636979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774435630956422211397221 145206680804329164636979)
                    ·
                      rfl

theorem cell23_848367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 4].length) (baseStart_848367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848367 prefixEnd_848367 := by exact prefixLift 848367
  have htrace : WordTrace (prefixWord ++ tailWord_848367) baseStart_848367 baseEnd_848367 := by
    simpa [prefixWord, tailWord_848367, baseEnd_848367] using wordTrace_append hprefix tailTrace_848367
  have hstable : (prefixWord ++ tailWord_848367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848367).length < 2 ^ (prefixWord ++ tailWord_848367).sum := by decide
  have hdescent : baseEnd_848367 < baseStart_848367 := by decide
  rcases family_descends (prefixWord ++ tailWord_848367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848377 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 3]
def baseStart_848377 : Nat := 118140960795 + 848377 * 2 ^ 59
def prefixEnd_848377 : Nat := 4983230072969 + 3 ^ 40 * 848377 * 2
def baseEnd_848377 : Nat := 435625177219532454785891

theorem tailTrace_848377 : CollatzResearch.WordTrace tailWord_848377 prefixEnd_848377 435625177219532454785891 := by
  unfold tailWord_848377
  simp only [CollatzResearch.WordTrace]
  refine ⟨30942851247482495101327385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20628567498321663400884923 30942851247482495101327385)
  ·
    refine ⟨23207138435611871325995539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30942851247482495101327385 23207138435611871325995539)
    ·
      refine ⟨34810707653417806988993309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23207138435611871325995539 34810707653417806988993309)
      ·
        refine ⟨13054015370031677620872491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34810707653417806988993309 13054015370031677620872491)
        ·
          refine ⟨19581023055047516431308737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054015370031677620872491 19581023055047516431308737)
          ·
            refine ⟨14685767291285637323481553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19581023055047516431308737 14685767291285637323481553)
            ·
              refine ⟨11014325468464227992611165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14685767291285637323481553 11014325468464227992611165)
              ·
                refine ⟨4130372050674085497229187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11014325468464227992611165 4130372050674085497229187)
                ·
                  refine ⟨6195558076011128245843781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130372050674085497229187 6195558076011128245843781)
                  ·
                    refine ⟨1161667139252086546095709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6195558076011128245843781 1161667139252086546095709)
                    ·
                      refine ⟨435625177219532454785891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1161667139252086546095709 435625177219532454785891)
                      ·
                        rfl

theorem cell23_848377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_848377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848377 prefixEnd_848377 := by exact prefixLift 848377
  have htrace : WordTrace (prefixWord ++ tailWord_848377) baseStart_848377 baseEnd_848377 := by
    simpa [prefixWord, tailWord_848377, baseEnd_848377] using wordTrace_append hprefix tailTrace_848377
  have hstable : (prefixWord ++ tailWord_848377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848377).length < 2 ^ (prefixWord ++ tailWord_848377).sum := by decide
  have hdescent : baseEnd_848377 < baseStart_848377 := by decide
  rcases family_descends (prefixWord ++ tailWord_848377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848394 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_848394 : Nat := 118140960795 + 848394 * 2 ^ 59
def prefixEnd_848394 : Nat := 4983230072969 + 3 ^ 40 * 848394 * 2
def baseEnd_848394 : Nat := 435633906390658888273313

theorem tailTrace_848394 : CollatzResearch.WordTrace tailWord_848394 prefixEnd_848394 435633906390658888273313 := by
  unfold tailWord_848394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735867822105226751174059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20628980858947271336464157 7735867822105226751174059)
  ·
    refine ⟨11603801733157840126761089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7735867822105226751174059 11603801733157840126761089)
    ·
      refine ⟨8702851299868380095070817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11603801733157840126761089 8702851299868380095070817)
      ·
        refine ⟨6527138474901285071303113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8702851299868380095070817 6527138474901285071303113)
        ·
          refine ⟨4895353856175963803477335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6527138474901285071303113 4895353856175963803477335)
          ·
            refine ⟨7343030784263945705216003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895353856175963803477335 7343030784263945705216003)
            ·
              refine ⟨11014546176395918557824005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343030784263945705216003 11014546176395918557824005)
              ·
                refine ⟨2065227408074234729592001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11014546176395918557824005 2065227408074234729592001)
                ·
                  refine ⟨1548920556055676047194001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2065227408074234729592001 1548920556055676047194001)
                  ·
                    refine ⟨1161690417041757035395501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1548920556055676047194001 1161690417041757035395501)
                    ·
                      refine ⟨435633906390658888273313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1161690417041757035395501 435633906390658888273313)
                      ·
                        rfl

theorem cell23_848394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_848394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848394 prefixEnd_848394 := by exact prefixLift 848394
  have htrace : WordTrace (prefixWord ++ tailWord_848394) baseStart_848394 baseEnd_848394 := by
    simpa [prefixWord, tailWord_848394, baseEnd_848394] using wordTrace_append hprefix tailTrace_848394
  have hstable : (prefixWord ++ tailWord_848394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848394).length < 2 ^ (prefixWord ++ tailWord_848394).sum := by decide
  have hdescent : baseEnd_848394 < baseStart_848394 := by decide
  rcases family_descends (prefixWord ++ tailWord_848394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848458 : List Nat := [3, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_848458 : Nat := 118140960795 + 848458 * 2 ^ 59
def prefixEnd_848458 : Nat := 4983230072969 + 3 ^ 40 * 848458 * 2
def baseEnd_848458 : Nat := 435666769152546637873019

theorem tailTrace_848458 : CollatzResearch.WordTrace tailWord_848458 prefixEnd_848458 435666769152546637873019 := by
  unfold tailWord_848458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736451390047261483756507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20630537040126030623350685 7736451390047261483756507)
  ·
    refine ⟨11604677085070892225634761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7736451390047261483756507 11604677085070892225634761)
    ·
      refine ⟨8703507813803169169226071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11604677085070892225634761 8703507813803169169226071)
      ·
        refine ⟨13055261720704753753839107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8703507813803169169226071 13055261720704753753839107)
        ·
          refine ⟨19582892581057130630758661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055261720704753753839107 19582892581057130630758661)
          ·
            refine ⟨3671792358948211993267249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19582892581057130630758661 3671792358948211993267249)
            ·
              refine ⟨2753844269211158994950437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3671792358948211993267249 2753844269211158994950437)
              ·
                refine ⟨516345800477092311553207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2753844269211158994950437 516345800477092311553207)
                ·
                  refine ⟨774518700715638467329811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516345800477092311553207 774518700715638467329811)
                  ·
                    refine ⟨1161778051073457700994717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 774518700715638467329811 1161778051073457700994717)
                    ·
                      refine ⟨435666769152546637873019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1161778051073457700994717 435666769152546637873019)
                      ·
                        rfl

theorem cell23_848458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_848458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848458 prefixEnd_848458 := by exact prefixLift 848458
  have htrace : WordTrace (prefixWord ++ tailWord_848458) baseStart_848458 baseEnd_848458 := by
    simpa [prefixWord, tailWord_848458, baseEnd_848458] using wordTrace_append hprefix tailTrace_848458
  have hstable : (prefixWord ++ tailWord_848458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848458).length < 2 ^ (prefixWord ++ tailWord_848458).sum := by decide
  have hdescent : baseEnd_848458 < baseStart_848458 := by decide
  rcases family_descends (prefixWord ++ tailWord_848458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848481 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_848481 : Nat := 118140960795 + 848481 * 2 ^ 59
def prefixEnd_848481 : Nat := 4983230072969 + 3 ^ 40 * 848481 * 2
def baseEnd_848481 : Nat := 435678579207600047885413

theorem tailTrace_848481 : CollatzResearch.WordTrace tailWord_848481 prefixEnd_848481 435678579207600047885413 := by
  unfold tailWord_848481
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946644439105720863113297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20631096292737147242075531 30946644439105720863113297)
  ·
    refine ⟨23209983329329290647334973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30946644439105720863113297 23209983329329290647334973)
    ·
      refine ⟨8703743748498483992750615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23209983329329290647334973 8703743748498483992750615)
      ·
        refine ⟨13055615622747725989125923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8703743748498483992750615 13055615622747725989125923)
        ·
          refine ⟨19583423434121588983688885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055615622747725989125923 19583423434121588983688885)
          ·
            refine ⟨1835945946948898967220833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19583423434121588983688885 1835945946948898967220833)
            ·
              refine ⟨1376959460211674225415625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835945946948898967220833 1376959460211674225415625)
              ·
                refine ⟨1032719595158755669061719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376959460211674225415625 1032719595158755669061719)
                ·
                  refine ⟨1549079392738133503592579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032719595158755669061719 1549079392738133503592579)
                  ·
                    refine ⟨2323619089107200255388869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1549079392738133503592579 2323619089107200255388869)
                    ·
                      refine ⟨435678579207600047885413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2323619089107200255388869 435678579207600047885413)
                      ·
                        rfl

theorem cell23_848481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_848481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848481 prefixEnd_848481 := by exact prefixLift 848481
  have htrace : WordTrace (prefixWord ++ tailWord_848481) baseStart_848481 baseEnd_848481 := by
    simpa [prefixWord, tailWord_848481, baseEnd_848481] using wordTrace_append hprefix tailTrace_848481
  have hstable : (prefixWord ++ tailWord_848481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848481).length < 2 ^ (prefixWord ++ tailWord_848481).sum := by decide
  have hdescent : baseEnd_848481 < baseStart_848481 := by decide
  rcases family_descends (prefixWord ++ tailWord_848481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848527 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_848527 : Nat := 118140960795 + 848527 * 2 ^ 59
def prefixEnd_848527 : Nat := 4983230072969 + 3 ^ 40 * 848527 * 2
def baseEnd_848527 : Nat := 435702199317706867910201

theorem tailTrace_848527 : CollatzResearch.WordTrace tailWord_848527 prefixEnd_848527 435702199317706867910201 := by
  unfold tailWord_848527
  simp only [CollatzResearch.WordTrace]
  refine ⟨30948322196939070719287835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20632214797959380479525223 30948322196939070719287835)
  ·
    refine ⟨46422483295408606078931753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30948322196939070719287835 46422483295408606078931753)
    ·
      refine ⟨34816862471556454559198815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46422483295408606078931753 34816862471556454559198815)
      ·
        refine ⟨52225293707334681838798223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34816862471556454559198815 52225293707334681838798223)
        ·
          refine ⟨78337940561002022758197335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52225293707334681838798223 78337940561002022758197335)
          ·
            refine ⟨117506910841503034137296003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78337940561002022758197335 117506910841503034137296003)
            ·
              refine ⟨176260366262254551205944005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117506910841503034137296003 176260366262254551205944005)
              ·
                refine ⟨33048818674172728351114501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176260366262254551205944005 33048818674172728351114501)
                ·
                  refine ⟨6196653501407386565833969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33048818674172728351114501 6196653501407386565833969)
                  ·
                    refine ⟨4647490126055539924375477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196653501407386565833969 4647490126055539924375477)
                    ·
                      refine ⟨435702199317706867910201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4647490126055539924375477 435702199317706867910201)
                      ·
                        rfl

theorem cell23_848527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_848527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848527 prefixEnd_848527 := by exact prefixLift 848527
  have htrace : WordTrace (prefixWord ++ tailWord_848527) baseStart_848527 baseEnd_848527 := by
    simpa [prefixWord, tailWord_848527, baseEnd_848527] using wordTrace_append hprefix tailTrace_848527
  have hstable : (prefixWord ++ tailWord_848527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848527).length < 2 ^ (prefixWord ++ tailWord_848527).sum := by decide
  have hdescent : baseEnd_848527 < baseStart_848527 := by decide
  rcases family_descends (prefixWord ++ tailWord_848527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848531 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 3]
def baseStart_848531 : Nat := 118140960795 + 848531 * 2 ^ 59
def prefixEnd_848531 : Nat := 4983230072969 + 3 ^ 40 * 848531 * 2
def baseEnd_848531 : Nat := 435704253240324852260183

theorem tailTrace_848531 : CollatzResearch.WordTrace tailWord_848531 prefixEnd_848531 435704253240324852260183 := by
  unfold tailWord_848531
  simp only [CollatzResearch.WordTrace]
  refine ⟨30948468088924579402433447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20632312059283052934955631 30948468088924579402433447)
  ·
    refine ⟨46422702133386869103650171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30948468088924579402433447 46422702133386869103650171)
    ·
      refine ⟨69634053200080303655475257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46422702133386869103650171 69634053200080303655475257)
      ·
        refine ⟨52225539900060227741606443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69634053200080303655475257 52225539900060227741606443)
        ·
          refine ⟨78338309850090341612409665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52225539900060227741606443 78338309850090341612409665)
          ·
            refine ⟨58753732387567756209307249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78338309850090341612409665 58753732387567756209307249)
            ·
              refine ⟨44065299290675817156980437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58753732387567756209307249 44065299290675817156980437)
              ·
                refine ⟨1032780452125214464616729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44065299290675817156980437 1032780452125214464616729)
                ·
                  refine ⟨774585339093910848462547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032780452125214464616729 774585339093910848462547)
                  ·
                    refine ⟨1161878008640866272693821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 774585339093910848462547 1161878008640866272693821)
                    ·
                      refine ⟨435704253240324852260183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1161878008640866272693821 435704253240324852260183)
                      ·
                        rfl

theorem cell23_848531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 3].length) (baseStart_848531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848531 prefixEnd_848531 := by exact prefixLift 848531
  have htrace : WordTrace (prefixWord ++ tailWord_848531) baseStart_848531 baseEnd_848531 := by
    simpa [prefixWord, tailWord_848531, baseEnd_848531] using wordTrace_append hprefix tailTrace_848531
  have hstable : (prefixWord ++ tailWord_848531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848531).length < 2 ^ (prefixWord ++ tailWord_848531).sum := by decide
  have hdescent : baseEnd_848531 < baseStart_848531 := by decide
  rcases family_descends (prefixWord ++ tailWord_848531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848547 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 3, 8]
def baseStart_848547 : Nat := 118140960795 + 848547 * 2 ^ 59
def prefixEnd_848547 : Nat := 4983230072969 + 3 ^ 40 * 848547 * 2
def baseEnd_848547 : Nat := 145237489643598929886703

theorem tailTrace_848547 : CollatzResearch.WordTrace tailWord_848547 prefixEnd_848547 145237489643598929886703 := by
  unfold tailWord_848547
  simp only [CollatzResearch.WordTrace]
  refine ⟨30949051656866614135015895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20632701104577742756677263 30949051656866614135015895)
  ·
    refine ⟨46423577485299921202523843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30949051656866614135015895 46423577485299921202523843)
    ·
      refine ⟨69635366227949881803785765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46423577485299921202523843 69635366227949881803785765)
      ·
        refine ⟨13056631167740602838209831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69635366227949881803785765 13056631167740602838209831)
        ·
          refine ⟨19584946751610904257314747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13056631167740602838209831 19584946751610904257314747)
          ·
            refine ⟨29377420127416356385972121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19584946751610904257314747 29377420127416356385972121)
            ·
              refine ⟨22033065095562267289479091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29377420127416356385972121 22033065095562267289479091)
              ·
                refine ⟨33049597643343400934218637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22033065095562267289479091 33049597643343400934218637)
                ·
                  refine ⟨12393599116253775350331989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33049597643343400934218637 12393599116253775350331989)
                  ·
                    refine ⟨145237489643598929886703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12393599116253775350331989 145237489643598929886703)
                    ·
                      rfl

theorem cell23_848547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 8].length) (baseStart_848547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848547 prefixEnd_848547 := by exact prefixLift 848547
  have htrace : WordTrace (prefixWord ++ tailWord_848547) baseStart_848547 baseEnd_848547 := by
    simpa [prefixWord, tailWord_848547, baseEnd_848547] using wordTrace_append hprefix tailTrace_848547
  have hstable : (prefixWord ++ tailWord_848547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848547).length < 2 ^ (prefixWord ++ tailWord_848547).sum := by decide
  have hdescent : baseEnd_848547 < baseStart_848547 := by decide
  rcases family_descends (prefixWord ++ tailWord_848547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848565 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_848565 : Nat := 118140960795 + 848565 * 2 ^ 59
def prefixEnd_848565 : Nat := 4983230072969 + 3 ^ 40 * 848565 * 2
def baseEnd_848565 : Nat := 435721711582577719235027

theorem tailTrace_848565 : CollatzResearch.WordTrace tailWord_848565 prefixEnd_848565 435721711582577719235027 := by
  unfold tailWord_848565
  simp only [CollatzResearch.WordTrace]
  refine ⟨30949708170801403209171149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20633138780534268806114099 30949708170801403209171149)
  ·
    refine ⟨11606140564050526203439181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30949708170801403209171149 11606140564050526203439181)
    ·
      refine ⟨4352302711518947326289693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11606140564050526203439181 4352302711518947326289693)
      ·
        refine ⟨1632113516819605247358635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4352302711518947326289693 1632113516819605247358635)
        ·
          refine ⟨2448170275229407871037953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632113516819605247358635 2448170275229407871037953)
          ·
            refine ⟨1836127706422055903278465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448170275229407871037953 1836127706422055903278465)
            ·
              refine ⟨1377095779816541927458849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836127706422055903278465 1377095779816541927458849)
              ·
                refine ⟨1032821834862406445594137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377095779816541927458849 1032821834862406445594137)
                ·
                  refine ⟨774616376146804834195603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032821834862406445594137 774616376146804834195603)
                  ·
                    refine ⟨1161924564220207251293405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 774616376146804834195603 1161924564220207251293405)
                    ·
                      refine ⟨435721711582577719235027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1161924564220207251293405 435721711582577719235027)
                      ·
                        rfl

theorem cell23_848565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_848565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848565 prefixEnd_848565 := by exact prefixLift 848565
  have htrace : WordTrace (prefixWord ++ tailWord_848565) baseStart_848565 baseEnd_848565 := by
    simpa [prefixWord, tailWord_848565, baseEnd_848565] using wordTrace_append hprefix tailTrace_848565
  have hstable : (prefixWord ++ tailWord_848565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848565).length < 2 ^ (prefixWord ++ tailWord_848565).sum := by decide
  have hdescent : baseEnd_848565 < baseStart_848565 := by decide
  rcases family_descends (prefixWord ++ tailWord_848565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848582 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_848582 : Nat := 118140960795 + 848582 * 2 ^ 59
def prefixEnd_848582 : Nat := 4983230072969 + 3 ^ 40 * 848582 * 2
def baseEnd_848582 : Nat := 435730440753704152722449

theorem tailTrace_848582 : CollatzResearch.WordTrace tailWord_848582 prefixEnd_848582 435730440753704152722449 := by
  unfold tailWord_848582
  simp only [CollatzResearch.WordTrace]
  refine ⟨967197756616869222266875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20633552141159876741693333 967197756616869222266875)
  ·
    refine ⟨1450796634925303833400313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967197756616869222266875 1450796634925303833400313)
    ·
      refine ⟨1088097476193977875050235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1450796634925303833400313 1088097476193977875050235)
      ·
        refine ⟨1632146214290966812575353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088097476193977875050235 1632146214290966812575353)
        ·
          refine ⟨1224109660718225109431515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1632146214290966812575353 1224109660718225109431515)
          ·
            refine ⟨1836164491077337664147273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224109660718225109431515 1836164491077337664147273)
            ·
              refine ⟨1377123368308003248110455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836164491077337664147273 1377123368308003248110455)
              ·
                refine ⟨2065685052462004872165683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377123368308003248110455 2065685052462004872165683)
                ·
                  refine ⟨3098527578693007308248525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065685052462004872165683 3098527578693007308248525)
                  ·
                    refine ⟨1161947842009877740593197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098527578693007308248525 1161947842009877740593197)
                    ·
                      refine ⟨435730440753704152722449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1161947842009877740593197 435730440753704152722449)
                      ·
                        rfl

theorem cell23_848582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_848582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848582 prefixEnd_848582 := by exact prefixLift 848582
  have htrace : WordTrace (prefixWord ++ tailWord_848582) baseStart_848582 baseEnd_848582 := by
    simpa [prefixWord, tailWord_848582, baseEnd_848582] using wordTrace_append hprefix tailTrace_848582
  have hstable : (prefixWord ++ tailWord_848582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848582).length < 2 ^ (prefixWord ++ tailWord_848582).sum := by decide
  have hdescent : baseEnd_848582 < baseStart_848582 := by decide
  rcases family_descends (prefixWord ++ tailWord_848582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848584 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_848584 : Nat := 118140960795 + 848584 * 2 ^ 59
def prefixEnd_848584 : Nat := 4983230072969 + 3 ^ 40 * 848584 * 2
def baseEnd_848584 : Nat := 435731467715013144897439

theorem tailTrace_848584 : CollatzResearch.WordTrace tailWord_848584 prefixEnd_848584 435731467715013144897439 := by
  unfold tailWord_848584
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475200578866284727056403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20633600771821712969408537 15475200578866284727056403)
  ·
    refine ⟨23212800868299427090584605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15475200578866284727056403 23212800868299427090584605)
    ·
      refine ⟨8704800325612285158969227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23212800868299427090584605 8704800325612285158969227)
      ·
        refine ⟨13057200488418427738453841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8704800325612285158969227 13057200488418427738453841)
        ·
          refine ⟨9792900366313820803840381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13057200488418427738453841 9792900366313820803840381)
          ·
            refine ⟨3672337637367682801440143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9792900366313820803840381 3672337637367682801440143)
            ·
              refine ⟨5508506456051524202160215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672337637367682801440143 5508506456051524202160215)
              ·
                refine ⟨8262759684077286303240323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508506456051524202160215 8262759684077286303240323)
                ·
                  refine ⟨12394139526115929454860485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8262759684077286303240323 12394139526115929454860485)
                  ·
                    refine ⟨2323901161146736772786341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12394139526115929454860485 2323901161146736772786341)
                    ·
                      refine ⟨435731467715013144897439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2323901161146736772786341 435731467715013144897439)
                      ·
                        rfl

theorem cell23_848584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_848584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848584 prefixEnd_848584 := by exact prefixLift 848584
  have htrace : WordTrace (prefixWord ++ tailWord_848584) baseStart_848584 baseEnd_848584 := by
    simpa [prefixWord, tailWord_848584, baseEnd_848584] using wordTrace_append hprefix tailTrace_848584
  have hstable : (prefixWord ++ tailWord_848584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848584).length < 2 ^ (prefixWord ++ tailWord_848584).sum := by decide
  have hdescent : baseEnd_848584 < baseStart_848584 := by decide
  rcases family_descends (prefixWord ++ tailWord_848584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848588 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 1, 4, 2]
def baseStart_848588 : Nat := 118140960795 + 848588 * 2 ^ 59
def prefixEnd_848588 : Nat := 4983230072969 + 3 ^ 40 * 848588 * 2
def baseEnd_848588 : Nat := 435733521637631129247421

theorem tailTrace_848588 : CollatzResearch.WordTrace tailWord_848588 prefixEnd_848588 435733521637631129247421 := by
  unfold tailWord_848588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475273524859039068629209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20633698033145385424838945 15475273524859039068629209)
  ·
    refine ⟨11606455143644279301471907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15475273524859039068629209 11606455143644279301471907)
    ·
      refine ⟨17409682715466418952207861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11606455143644279301471907 17409682715466418952207861)
      ·
        refine ⟨1632157754574976776769487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17409682715466418952207861 1632157754574976776769487)
        ·
          refine ⟨2448236631862465165154231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632157754574976776769487 2448236631862465165154231)
          ·
            refine ⟨3672354947793697747731347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448236631862465165154231 3672354947793697747731347)
            ·
              refine ⟨5508532421690546621597021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672354947793697747731347 5508532421690546621597021)
              ·
                refine ⟨2065699658133954983098883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5508532421690546621597021 2065699658133954983098883)
                ·
                  refine ⟨3098549487200932474648325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065699658133954983098883 3098549487200932474648325)
                  ·
                    refine ⟨580978028850174838996561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3098549487200932474648325 580978028850174838996561)
                    ·
                      refine ⟨435733521637631129247421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 580978028850174838996561 435733521637631129247421)
                      ·
                        rfl

theorem cell23_848588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_848588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848588 prefixEnd_848588 := by exact prefixLift 848588
  have htrace : WordTrace (prefixWord ++ tailWord_848588) baseStart_848588 baseEnd_848588 := by
    simpa [prefixWord, tailWord_848588, baseEnd_848588] using wordTrace_append hprefix tailTrace_848588
  have hstable : (prefixWord ++ tailWord_848588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848588).length < 2 ^ (prefixWord ++ tailWord_848588).sum := by decide
  have hdescent : baseEnd_848588 < baseStart_848588 := by decide
  rcases family_descends (prefixWord ++ tailWord_848588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848621 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_848621 : Nat := 118140960795 + 848621 * 2 ^ 59
def prefixEnd_848621 : Nat := 4983230072969 + 3 ^ 40 * 848621 * 2
def baseEnd_848621 : Nat := 435750466499229500134769

theorem tailTrace_848621 : CollatzResearch.WordTrace tailWord_848621 prefixEnd_848621 435750466499229500134769 := by
  unfold tailWord_848621
  simp only [CollatzResearch.WordTrace]
  refine ⟨30951750658598524773209717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20634500439065683182139811 30951750658598524773209717)
  ·
    refine ⟨2901726624243611697488411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30951750658598524773209717 2901726624243611697488411)
    ·
      refine ⟨4352589936365417546232617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2901726624243611697488411 4352589936365417546232617)
      ·
        refine ⟨3264442452274063159674463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4352589936365417546232617 3264442452274063159674463)
        ·
          refine ⟨4896663678411094739511695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264442452274063159674463 4896663678411094739511695)
          ·
            refine ⟨7344995517616642109267543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4896663678411094739511695 7344995517616642109267543)
            ·
              refine ⟨11017493276424963163901315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344995517616642109267543 11017493276424963163901315)
              ·
                refine ⟨16526239914637444745851973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11017493276424963163901315 16526239914637444745851973)
                ·
                  refine ⟨3098669983994520889847245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16526239914637444745851973 3098669983994520889847245)
                  ·
                    refine ⟨1162001243997945333692717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098669983994520889847245 1162001243997945333692717)
                    ·
                      refine ⟨435750466499229500134769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1162001243997945333692717 435750466499229500134769)
                      ·
                        rfl

theorem cell23_848621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_848621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848621 prefixEnd_848621 := by exact prefixLift 848621
  have htrace : WordTrace (prefixWord ++ tailWord_848621) baseStart_848621 baseEnd_848621 := by
    simpa [prefixWord, tailWord_848621, baseEnd_848621] using wordTrace_append hprefix tailTrace_848621
  have hstable : (prefixWord ++ tailWord_848621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848621).length < 2 ^ (prefixWord ++ tailWord_848621).sum := by decide
  have hdescent : baseEnd_848621 < baseStart_848621 := by decide
  rcases family_descends (prefixWord ++ tailWord_848621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848622 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_848622 : Nat := 118140960795 + 848622 * 2 ^ 59
def prefixEnd_848622 : Nat := 4983230072969 + 3 ^ 40 * 848622 * 2
def baseEnd_848622 : Nat := 435750979979883996222265

theorem tailTrace_848622 : CollatzResearch.WordTrace tailWord_848622 prefixEnd_848622 435750979979883996222265 := by
  unfold tailWord_848622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868973391449362742999515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20634524754396601295997413 3868973391449362742999515)
  ·
    refine ⟨5803460087174044114499273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3868973391449362742999515 5803460087174044114499273)
    ·
      refine ⟨4352595065380533085874455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5803460087174044114499273 4352595065380533085874455)
      ·
        refine ⟨6528892598070799628811683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4352595065380533085874455 6528892598070799628811683)
        ·
          refine ⟨9793338897106199443217525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528892598070799628811683 9793338897106199443217525)
          ·
            refine ⟨918125521603706197801643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9793338897106199443217525 918125521603706197801643)
            ·
              refine ⟨1377188282405559296702465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918125521603706197801643 1377188282405559296702465)
              ·
                refine ⟨1032891211804169472526849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377188282405559296702465 1032891211804169472526849)
                ·
                  refine ⟨774668408853127104395137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032891211804169472526849 774668408853127104395137)
                  ·
                    refine ⟨581001306639845328296353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 774668408853127104395137 581001306639845328296353)
                    ·
                      refine ⟨435750979979883996222265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581001306639845328296353 435750979979883996222265)
                      ·
                        rfl

theorem cell23_848622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_848622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848622 prefixEnd_848622 := by exact prefixLift 848622
  have htrace : WordTrace (prefixWord ++ tailWord_848622) baseStart_848622 baseEnd_848622 := by
    simpa [prefixWord, tailWord_848622, baseEnd_848622] using wordTrace_append hprefix tailTrace_848622
  have hstable : (prefixWord ++ tailWord_848622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848622).length < 2 ^ (prefixWord ++ tailWord_848622).sum := by decide
  have hdescent : baseEnd_848622 < baseStart_848622 := by decide
  rcases family_descends (prefixWord ++ tailWord_848622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848624 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 4, 5]
def baseStart_848624 : Nat := 118140960795 + 848624 * 2 ^ 59
def prefixEnd_848624 : Nat := 4983230072969 + 3 ^ 40 * 848624 * 2
def baseEnd_848624 : Nat := 145250668980397662799085

theorem tailTrace_848624 : CollatzResearch.WordTrace tailWord_848624 prefixEnd_848624 145250668980397662799085 := by
  unfold tailWord_848624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475930038793828142784463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20634573385058437523712617 15475930038793828142784463)
  ·
    refine ⟨23213895058190742214176695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15475930038793828142784463 23213895058190742214176695)
    ·
      refine ⟨34820842587286113321265043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23213895058190742214176695 34820842587286113321265043)
      ·
        refine ⟨52231263880929169981897565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34820842587286113321265043 52231263880929169981897565)
        ·
          refine ⟨19586723955348438743211587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52231263880929169981897565 19586723955348438743211587)
          ·
            refine ⟨29380085933022658114817381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19586723955348438743211587 29380085933022658114817381)
            ·
              refine ⟨5508766112441748396528259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29380085933022658114817381 5508766112441748396528259)
              ·
                refine ⟨8263149168662622594792389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508766112441748396528259 8263149168662622594792389)
                ·
                  refine ⟨1549340469124241736523573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8263149168662622594792389 1549340469124241736523573)
                  ·
                    refine ⟨145250668980397662799085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1549340469124241736523573 145250668980397662799085)
                    ·
                      rfl

theorem cell23_848624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_848624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848624 prefixEnd_848624 := by exact prefixLift 848624
  have htrace : WordTrace (prefixWord ++ tailWord_848624) baseStart_848624 baseEnd_848624 := by
    simpa [prefixWord, tailWord_848624, baseEnd_848624] using wordTrace_append hprefix tailTrace_848624
  have hstable : (prefixWord ++ tailWord_848624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848624).length < 2 ^ (prefixWord ++ tailWord_848624).sum := by decide
  have hdescent : baseEnd_848624 < baseStart_848624 := by decide
  rcases family_descends (prefixWord ++ tailWord_848624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848634 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_848634 : Nat := 118140960795 + 848634 * 2 ^ 59
def prefixEnd_848634 : Nat := 4983230072969 + 3 ^ 40 * 848634 * 2
def baseEnd_848634 : Nat := 435757141747737949272209

theorem tailTrace_848634 : CollatzResearch.WordTrace tailWord_848634 prefixEnd_848634 435757141747737949272209 := by
  unfold tailWord_848634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7738056201887856998358239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20634816538367618662288637 7738056201887856998358239)
  ·
    refine ⟨11607084302831785497537359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7738056201887856998358239 11607084302831785497537359)
    ·
      refine ⟨17410626454247678246306039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11607084302831785497537359 17410626454247678246306039)
      ·
        refine ⟨26115939681371517369459059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17410626454247678246306039 26115939681371517369459059)
        ·
          refine ⟨39173909522057276054188589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26115939681371517369459059 39173909522057276054188589)
          ·
            refine ⟨14690216070771478520320721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39173909522057276054188589 14690216070771478520320721)
            ·
              refine ⟨11017662053078608890240541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14690216070771478520320721 11017662053078608890240541)
              ·
                refine ⟨4131623269904478333840203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11017662053078608890240541 4131623269904478333840203)
                ·
                  refine ⟨6197434904856717500760305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131623269904478333840203 6197434904856717500760305)
                  ·
                    refine ⟨4648076178642538125570229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6197434904856717500760305 4648076178642538125570229)
                    ·
                      refine ⟨435757141747737949272209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4648076178642538125570229 435757141747737949272209)
                      ·
                        rfl

theorem cell23_848634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_848634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848634 prefixEnd_848634 := by exact prefixLift 848634
  have htrace : WordTrace (prefixWord ++ tailWord_848634) baseStart_848634 baseEnd_848634 := by
    simpa [prefixWord, tailWord_848634, baseEnd_848634] using wordTrace_append hprefix tailTrace_848634
  have hstable : (prefixWord ++ tailWord_848634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848634).length < 2 ^ (prefixWord ++ tailWord_848634).sum := by decide
  have hdescent : baseEnd_848634 < baseStart_848634 := by decide
  rcases family_descends (prefixWord ++ tailWord_848634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848638 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_848638 : Nat := 118140960795 + 848638 * 2 ^ 59
def prefixEnd_848638 : Nat := 4983230072969 + 3 ^ 40 * 848638 * 2
def baseEnd_848638 : Nat := 435759195670355933622191

theorem tailTrace_848638 : CollatzResearch.WordTrace tailWord_848638 prefixEnd_848638 435759195670355933622191 := by
  unfold tailWord_848638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869046337442117084572321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20634913799691291117719045 3869046337442117084572321)
  ·
    refine ⟨2901784753081587813429241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3869046337442117084572321 2901784753081587813429241)
    ·
      refine ⟨2176338564811190860071931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2901784753081587813429241 2176338564811190860071931)
      ·
        refine ⟨3264507847216786290107897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176338564811190860071931 3264507847216786290107897)
        ·
          refine ⟨2448380885412589717580923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3264507847216786290107897 2448380885412589717580923)
          ·
            refine ⟨3672571328118884576371385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448380885412589717580923 3672571328118884576371385)
            ·
              refine ⟨2754428496089163432278539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3672571328118884576371385 2754428496089163432278539)
              ·
                refine ⟨4131642744133745148417809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754428496089163432278539 4131642744133745148417809)
                ·
                  refine ⟨3098732058100308861313357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4131642744133745148417809 3098732058100308861313357)
                  ·
                    refine ⟨1162024521787615822992509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098732058100308861313357 1162024521787615822992509)
                    ·
                      refine ⟨435759195670355933622191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1162024521787615822992509 435759195670355933622191)
                      ·
                        rfl

theorem cell23_848638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_848638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848638 prefixEnd_848638 := by exact prefixLift 848638
  have htrace : WordTrace (prefixWord ++ tailWord_848638) baseStart_848638 baseEnd_848638 := by
    simpa [prefixWord, tailWord_848638, baseEnd_848638] using wordTrace_append hprefix tailTrace_848638
  have hstable : (prefixWord ++ tailWord_848638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848638).length < 2 ^ (prefixWord ++ tailWord_848638).sum := by decide
  have hdescent : baseEnd_848638 < baseStart_848638 := by decide
  rcases family_descends (prefixWord ++ tailWord_848638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848654 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_848654 : Nat := 118140960795 + 848654 * 2 ^ 59
def prefixEnd_848654 : Nat := 4983230072969 + 3 ^ 40 * 848654 * 2
def baseEnd_848654 : Nat := 145255803786942623674039

theorem tailTrace_848654 : CollatzResearch.WordTrace tailWord_848654 prefixEnd_848654 145255803786942623674039 := by
  unfold tailWord_848654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869119283434871426145127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20635302844985980939440677 3869119283434871426145127)
  ·
    refine ⟨5803678925152307139217691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3869119283434871426145127 5803678925152307139217691)
    ·
      refine ⟨8705518387728460708826537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5803678925152307139217691 8705518387728460708826537)
      ·
        refine ⟨6529138790796345531619903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8705518387728460708826537 6529138790796345531619903)
        ·
          refine ⟨9793708186194518297429855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529138790796345531619903 9793708186194518297429855)
          ·
            refine ⟨14690562279291777446144783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9793708186194518297429855 14690562279291777446144783)
            ·
              refine ⟨22035843418937666169217175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14690562279291777446144783 22035843418937666169217175)
              ·
                refine ⟨33053765128406499253825763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22035843418937666169217175 33053765128406499253825763)
                ·
                  refine ⟨49580647692609748880738645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33053765128406499253825763 49580647692609748880738645)
                  ·
                    refine ⟨145255803786942623674039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 49580647692609748880738645 145255803786942623674039)
                    ·
                      rfl

theorem cell23_848654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_848654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848654 prefixEnd_848654 := by exact prefixLift 848654
  have htrace : WordTrace (prefixWord ++ tailWord_848654) baseStart_848654 baseEnd_848654 := by
    simpa [prefixWord, tailWord_848654, baseEnd_848654] using wordTrace_append hprefix tailTrace_848654
  have hstable : (prefixWord ++ tailWord_848654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848654).length < 2 ^ (prefixWord ++ tailWord_848654).sum := by decide
  have hdescent : baseEnd_848654 < baseStart_848654 := by decide
  rcases family_descends (prefixWord ++ tailWord_848654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848661 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_848661 : Nat := 118140960795 + 848661 * 2 ^ 59
def prefixEnd_848661 : Nat := 4983230072969 + 3 ^ 40 * 848661 * 2
def baseEnd_848661 : Nat := 435771005725409343634585

theorem tailTrace_848661 : CollatzResearch.WordTrace tailWord_848661 prefixEnd_848661 435771005725409343634585 := by
  unfold tailWord_848661
  simp only [CollatzResearch.WordTrace]
  refine ⟨30953209578453611604665837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20635473052302407736443891 30953209578453611604665837)
  ·
    refine ⟨11607453591920104351749689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30953209578453611604665837 11607453591920104351749689)
    ·
      refine ⟨8705590193940078263812267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11607453591920104351749689 8705590193940078263812267)
      ·
        refine ⟨13058385290910117395718401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8705590193940078263812267 13058385290910117395718401)
        ·
          refine ⟨9793788968182588046788801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13058385290910117395718401 9793788968182588046788801)
          ·
            refine ⟨7345341726136941035091601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9793788968182588046788801 7345341726136941035091601)
            ·
              refine ⟨5509006294602705776318701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7345341726136941035091601 5509006294602705776318701)
              ·
                refine ⟨2065877360476014666119513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5509006294602705776318701 2065877360476014666119513)
                ·
                  refine ⟨1549408020357010999589635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2065877360476014666119513 1549408020357010999589635)
                  ·
                    refine ⟨2324112030535516499384453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1549408020357010999589635 2324112030535516499384453)
                    ·
                      refine ⟨435771005725409343634585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2324112030535516499384453 435771005725409343634585)
                      ·
                        rfl

theorem cell23_848661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_848661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848661 prefixEnd_848661 := by exact prefixLift 848661
  have htrace : WordTrace (prefixWord ++ tailWord_848661) baseStart_848661 baseEnd_848661 := by
    simpa [prefixWord, tailWord_848661, baseEnd_848661] using wordTrace_append hprefix tailTrace_848661
  have hstable : (prefixWord ++ tailWord_848661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848661).length < 2 ^ (prefixWord ++ tailWord_848661).sum := by decide
  have hdescent : baseEnd_848661 < baseStart_848661 := by decide
  rcases family_descends (prefixWord ++ tailWord_848661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848664 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_848664 : Nat := 118140960795 + 848664 * 2 ^ 59
def prefixEnd_848664 : Nat := 4983230072969 + 3 ^ 40 * 848664 * 2
def baseEnd_848664 : Nat := 435772546167372831897071

theorem tailTrace_848664 : CollatzResearch.WordTrace tailWord_848664 prefixEnd_848664 435772546167372831897071 := by
  unfold tailWord_848664
  simp only [CollatzResearch.WordTrace]
  refine ⟨15476659498721371558512523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20635545998295162078016697 15476659498721371558512523)
  ·
    refine ⟨23214989248082057337768785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15476659498721371558512523 23214989248082057337768785)
    ·
      refine ⟨17411241936061543003326589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23214989248082057337768785 17411241936061543003326589)
      ·
        refine ⟨6529215726023078626247471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17411241936061543003326589 6529215726023078626247471)
        ·
          refine ⟨9793823589034617939371207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529215726023078626247471 9793823589034617939371207)
          ·
            refine ⟨14690735383551926909056811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9793823589034617939371207 14690735383551926909056811)
            ·
              refine ⟨22036103075327890363585217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14690735383551926909056811 22036103075327890363585217)
              ·
                refine ⟨16527077306495917772688913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22036103075327890363585217 16527077306495917772688913)
                ·
                  refine ⟨12395307979871938329516685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16527077306495917772688913 12395307979871938329516685)
                  ·
                    refine ⟨4648240492451976873568757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12395307979871938329516685 4648240492451976873568757)
                    ·
                      refine ⟨435772546167372831897071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4648240492451976873568757 435772546167372831897071)
                      ·
                        rfl

theorem cell23_848664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_848664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848664 prefixEnd_848664 := by exact prefixLift 848664
  have htrace : WordTrace (prefixWord ++ tailWord_848664) baseStart_848664 baseEnd_848664 := by
    simpa [prefixWord, tailWord_848664, baseEnd_848664] using wordTrace_append hprefix tailTrace_848664
  have hstable : (prefixWord ++ tailWord_848664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848664).length < 2 ^ (prefixWord ++ tailWord_848664).sum := by decide
  have hdescent : baseEnd_848664 < baseStart_848664 := by decide
  rcases family_descends (prefixWord ++ tailWord_848664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848681 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 3]
def baseStart_848681 : Nat := 118140960795 + 848681 * 2 ^ 59
def prefixEnd_848681 : Nat := 4983230072969 + 3 ^ 40 * 848681 * 2
def baseEnd_848681 : Nat := 435781275338499265384493

theorem tailTrace_848681 : CollatzResearch.WordTrace tailWord_848681 prefixEnd_848681 435781275338499265384493 := by
  unfold tailWord_848681
  simp only [CollatzResearch.WordTrace]
  refine ⟨30953939038381155020393897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20635959358920770013595931 30953939038381155020393897)
  ·
    refine ⟨23215454278785866265295423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30953939038381155020393897 23215454278785866265295423)
    ·
      refine ⟨34823181418178799397943135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23215454278785866265295423 34823181418178799397943135)
      ·
        refine ⟨52234772127268199096914703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34823181418178799397943135 52234772127268199096914703)
        ·
          refine ⟨78352158190902298645372055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52234772127268199096914703 78352158190902298645372055)
          ·
            refine ⟨117528237286353447968058083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78352158190902298645372055 117528237286353447968058083)
            ·
              refine ⟨176292355929530171952087125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117528237286353447968058083 176292355929530171952087125)
              ·
                refine ⟨2065926046049181702563521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 176292355929530171952087125 2065926046049181702563521)
                ·
                  refine ⟨1549444534536886276922641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2065926046049181702563521 1549444534536886276922641)
                  ·
                    refine ⟨1162083400902664707691981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1549444534536886276922641 1162083400902664707691981)
                    ·
                      refine ⟨435781275338499265384493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1162083400902664707691981 435781275338499265384493)
                      ·
                        rfl

theorem cell23_848681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_848681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848681 prefixEnd_848681 := by exact prefixLift 848681
  have htrace : WordTrace (prefixWord ++ tailWord_848681) baseStart_848681 baseEnd_848681 := by
    simpa [prefixWord, tailWord_848681, baseEnd_848681] using wordTrace_append hprefix tailTrace_848681
  have hstable : (prefixWord ++ tailWord_848681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848681).length < 2 ^ (prefixWord ++ tailWord_848681).sum := by decide
  have hdescent : baseEnd_848681 < baseStart_848681 := by decide
  rcases family_descends (prefixWord ++ tailWord_848681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848684 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 8]
def baseStart_848684 : Nat := 118140960795 + 848684 * 2 ^ 59
def prefixEnd_848684 : Nat := 4983230072969 + 3 ^ 40 * 848684 * 2
def baseEnd_848684 : Nat := 48420312864495861516331

theorem tailTrace_848684 : CollatzResearch.WordTrace tailWord_848684 prefixEnd_848684 48420312864495861516331 := by
  unfold tailWord_848684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477024228685143266376553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20636032304913524355168737 15477024228685143266376553)
  ·
    refine ⟨11607768171513857449782415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15477024228685143266376553 11607768171513857449782415)
    ·
      refine ⟨17411652257270786174673623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11607768171513857449782415 17411652257270786174673623)
      ·
        refine ⟨26117478385906179262010435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17411652257270786174673623 26117478385906179262010435)
        ·
          refine ⟨39176217578859268893015653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26117478385906179262010435 39176217578859268893015653)
          ·
            refine ⟨7345540796036112917440435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39176217578859268893015653 7345540796036112917440435)
            ·
              refine ⟨11018311194054169376160653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345540796036112917440435 11018311194054169376160653)
              ·
                refine ⟨4131866697770313516060245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11018311194054169376160653 4131866697770313516060245)
                ·
                  refine ⟨48420312864495861516331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4131866697770313516060245 48420312864495861516331)
                  ·
                    rfl

theorem cell23_848684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_848684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848684 prefixEnd_848684 := by exact prefixLift 848684
  have htrace : WordTrace (prefixWord ++ tailWord_848684) baseStart_848684 baseEnd_848684 := by
    simpa [prefixWord, tailWord_848684, baseEnd_848684] using wordTrace_append hprefix tailTrace_848684
  have hstable : (prefixWord ++ tailWord_848684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848684).length < 2 ^ (prefixWord ++ tailWord_848684).sum := by decide
  have hdescent : baseEnd_848684 < baseStart_848684 := by decide
  rcases family_descends (prefixWord ++ tailWord_848684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848685 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_848685 : Nat := 118140960795 + 848685 * 2 ^ 59
def prefixEnd_848685 : Nat := 4983230072969 + 3 ^ 40 * 848685 * 2
def baseEnd_848685 : Nat := 435783329261117249734475

theorem tailTrace_848685 : CollatzResearch.WordTrace tailWord_848685 prefixEnd_848685 435783329261117249734475 := by
  unfold tailWord_848685
  simp only [CollatzResearch.WordTrace]
  refine ⟨30954084930366663703539509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20636056620244442469026339 30954084930366663703539509)
  ·
    refine ⟨2901945462221874722206829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30954084930366663703539509 2901945462221874722206829)
    ·
      refine ⟨1088229548333203020827561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2901945462221874722206829 1088229548333203020827561)
      ·
        refine ⟨816172161249902265620671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1088229548333203020827561 816172161249902265620671)
        ·
          refine ⟨1224258241874853398431007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816172161249902265620671 1224258241874853398431007)
          ·
            refine ⟨1836387362812280097646511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224258241874853398431007 1836387362812280097646511)
            ·
              refine ⟨2754581044218420146469767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836387362812280097646511 2754581044218420146469767)
              ·
                refine ⟨4131871566327630219704651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754581044218420146469767 4131871566327630219704651)
                ·
                  refine ⟨6197807349491445329556977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131871566327630219704651 6197807349491445329556977)
                  ·
                    refine ⟨4648355512118583997167733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6197807349491445329556977 4648355512118583997167733)
                    ·
                      refine ⟨435783329261117249734475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4648355512118583997167733 435783329261117249734475)
                      ·
                        rfl

theorem cell23_848685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_848685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848685 prefixEnd_848685 := by exact prefixLift 848685
  have htrace : WordTrace (prefixWord ++ tailWord_848685) baseStart_848685 baseEnd_848685 := by
    simpa [prefixWord, tailWord_848685, baseEnd_848685] using wordTrace_append hprefix tailTrace_848685
  have hstable : (prefixWord ++ tailWord_848685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848685).length < 2 ^ (prefixWord ++ tailWord_848685).sum := by decide
  have hdescent : baseEnd_848685 < baseStart_848685 := by decide
  rcases family_descends (prefixWord ++ tailWord_848685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848688 : List Nat := [2, 1, 1, 1, 2, 2, 1, 8, 1, 4]
def baseStart_848688 : Nat := 118140960795 + 848688 * 2 ^ 59
def prefixEnd_848688 : Nat := 4983230072969 + 3 ^ 40 * 848688 * 2
def baseEnd_848688 : Nat := 145261623234360245998987

theorem tailTrace_848688 : CollatzResearch.WordTrace tailWord_848688 prefixEnd_848688 145261623234360245998987 := by
  unfold tailWord_848688
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477097174677897607949359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20636129566237196810599145 15477097174677897607949359)
  ·
    refine ⟨23215645762016846411924039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15477097174677897607949359 23215645762016846411924039)
    ·
      refine ⟨34823468643025269617886059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23215645762016846411924039 34823468643025269617886059)
      ·
        refine ⟨52235202964537904426829089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34823468643025269617886059 52235202964537904426829089)
        ·
          refine ⟨39176402223403428320121817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52235202964537904426829089 39176402223403428320121817)
          ·
            refine ⟨29382301667552571240091363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39176402223403428320121817 29382301667552571240091363)
            ·
              refine ⟨44073452501328856860137045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29382301667552571240091363 44073452501328856860137045)
              ·
                refine ⟨516485771499947541329731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 44073452501328856860137045 516485771499947541329731)
                ·
                  refine ⟨774728657249921311994597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516485771499947541329731 774728657249921311994597)
                  ·
                    refine ⟨145261623234360245998987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774728657249921311994597 145261623234360245998987)
                    ·
                      rfl

theorem cell23_848688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 4].length) (baseStart_848688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848688 prefixEnd_848688 := by exact prefixLift 848688
  have htrace : WordTrace (prefixWord ++ tailWord_848688) baseStart_848688 baseEnd_848688 := by
    simpa [prefixWord, tailWord_848688, baseEnd_848688] using wordTrace_append hprefix tailTrace_848688
  have hstable : (prefixWord ++ tailWord_848688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848688).length < 2 ^ (prefixWord ++ tailWord_848688).sum := by decide
  have hdescent : baseEnd_848688 < baseStart_848688 := by decide
  rcases family_descends (prefixWord ++ tailWord_848688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848704 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_848704 : Nat := 118140960795 + 848704 * 2 ^ 59
def prefixEnd_848704 : Nat := 4983230072969 + 3 ^ 40 * 848704 * 2
def baseEnd_848704 : Nat := 435793085393552675396887

theorem tailTrace_848704 : CollatzResearch.WordTrace tailWord_848704 prefixEnd_848704 435793085393552675396887 := by
  unfold tailWord_848704
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477388958648914974240583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20636518611531886632320777 15477388958648914974240583)
  ·
    refine ⟨23216083437973372461360875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15477388958648914974240583 23216083437973372461360875)
    ·
      refine ⟨34824125156960058692041313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23216083437973372461360875 34824125156960058692041313)
      ·
        refine ⟨26118093867720044019030985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34824125156960058692041313 26118093867720044019030985)
        ·
          refine ⟨19588570400790033014273239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26118093867720044019030985 19588570400790033014273239)
          ·
            refine ⟨29382855601185049521409859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19588570400790033014273239 29382855601185049521409859)
            ·
              refine ⟨44074283401777574282114789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29382855601185049521409859 44074283401777574282114789)
              ·
                refine ⟨8263928137833295177896523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44074283401777574282114789 8263928137833295177896523)
                ·
                  refine ⟨12395892206749942766844785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8263928137833295177896523 12395892206749942766844785)
                  ·
                    refine ⟨9296919155062457075133589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12395892206749942766844785 9296919155062457075133589)
                    ·
                      refine ⟨435793085393552675396887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9296919155062457075133589 435793085393552675396887)
                      ·
                        rfl

theorem cell23_848704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_848704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848704 prefixEnd_848704 := by exact prefixLift 848704
  have htrace : WordTrace (prefixWord ++ tailWord_848704) baseStart_848704 baseEnd_848704 := by
    simpa [prefixWord, tailWord_848704, baseEnd_848704] using wordTrace_append hprefix tailTrace_848704
  have hstable : (prefixWord ++ tailWord_848704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848704).length < 2 ^ (prefixWord ++ tailWord_848704).sum := by decide
  have hdescent : baseEnd_848704 < baseStart_848704 := by decide
  rcases family_descends (prefixWord ++ tailWord_848704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848761 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 1, 6]
def baseStart_848761 : Nat := 118140960795 + 848761 * 2 ^ 59
def prefixEnd_848761 : Nat := 4983230072969 + 3 ^ 40 * 848761 * 2
def baseEnd_848761 : Nat := 145274117930286317461375

theorem tailTrace_848761 : CollatzResearch.WordTrace tailWord_848761 prefixEnd_848761 145274117930286317461375 := by
  unfold tailWord_848761
  simp only [CollatzResearch.WordTrace]
  refine ⟨30956856878091328683306137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20637904585394219122204091 30956856878091328683306137)
  ·
    refine ⟨23217642658568496512479603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30956856878091328683306137 23217642658568496512479603)
    ·
      refine ⟨34826463987852744768719405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23217642658568496512479603 34826463987852744768719405)
      ·
        refine ⟨13059923995444779288269777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34826463987852744768719405 13059923995444779288269777)
        ·
          refine ⟨9794942996583584466202333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13059923995444779288269777 9794942996583584466202333)
          ·
            refine ⟨3673103623718844174825875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9794942996583584466202333 3673103623718844174825875)
            ·
              refine ⟨5509655435578266262238813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673103623718844174825875 5509655435578266262238813)
              ·
                refine ⟨2066120788341849848339555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5509655435578266262238813 2066120788341849848339555)
                ·
                  refine ⟨3099181182512774772509333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066120788341849848339555 3099181182512774772509333)
                  ·
                    refine ⟨145274117930286317461375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3099181182512774772509333 145274117930286317461375)
                    ·
                      rfl

theorem cell23_848761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_848761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848761 prefixEnd_848761 := by exact prefixLift 848761
  have htrace : WordTrace (prefixWord ++ tailWord_848761) baseStart_848761 baseEnd_848761 := by
    simpa [prefixWord, tailWord_848761, baseEnd_848761] using wordTrace_append hprefix tailTrace_848761
  have hstable : (prefixWord ++ tailWord_848761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848761).length < 2 ^ (prefixWord ++ tailWord_848761).sum := by decide
  have hdescent : baseEnd_848761 < baseStart_848761 := by decide
  rcases family_descends (prefixWord ++ tailWord_848761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848778 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_848778 : Nat := 118140960795 + 848778 * 2 ^ 59
def prefixEnd_848778 : Nat := 4983230072969 + 3 ^ 40 * 848778 * 2
def baseEnd_848778 : Nat := 145277027653995128623849

theorem tailTrace_848778 : CollatzResearch.WordTrace tailWord_848778 prefixEnd_848778 145277027653995128623849 := by
  unfold tailWord_848778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739369229757435146668747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20638317946019827057783325 7739369229757435146668747)
  ·
    refine ⟨11609053844636152720003121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7739369229757435146668747 11609053844636152720003121)
    ·
      refine ⟨8706790383477114540002341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11609053844636152720003121 8706790383477114540002341)
      ·
        refine ⟨1632523196901958976250439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8706790383477114540002341 1632523196901958976250439)
        ·
          refine ⟨2448784795352938464375659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632523196901958976250439 2448784795352938464375659)
          ·
            refine ⟨3673177193029407696563489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448784795352938464375659 3673177193029407696563489)
            ·
              refine ⟨2754882894772055772422617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3673177193029407696563489 2754882894772055772422617)
              ·
                refine ⟨2066162171079041829316963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2754882894772055772422617 2066162171079041829316963)
                ·
                  refine ⟨3099243256618562743975445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066162171079041829316963 3099243256618562743975445)
                  ·
                    refine ⟨145277027653995128623849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3099243256618562743975445 145277027653995128623849)
                    ·
                      rfl

theorem cell23_848778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_848778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848778 prefixEnd_848778 := by exact prefixLift 848778
  have htrace : WordTrace (prefixWord ++ tailWord_848778) baseStart_848778 baseEnd_848778 := by
    simpa [prefixWord, tailWord_848778, baseEnd_848778] using wordTrace_append hprefix tailTrace_848778
  have hstable : (prefixWord ++ tailWord_848778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848778).length < 2 ^ (prefixWord ++ tailWord_848778).sum := by decide
  have hdescent : baseEnd_848778 < baseStart_848778 := by decide
  rcases family_descends (prefixWord ++ tailWord_848778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848788 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_848788 : Nat := 118140960795 + 848788 * 2 ^ 59
def prefixEnd_848788 : Nat := 4983230072969 + 3 ^ 40 * 848788 * 2
def baseEnd_848788 : Nat := 435836217768530346746501

theorem tailTrace_848788 : CollatzResearch.WordTrace tailWord_848788 prefixEnd_848788 435836217768530346746501 := by
  unfold tailWord_848788
  simp only [CollatzResearch.WordTrace]
  refine ⟨15478920824496756147269509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20638561099329008196359345 15478920824496756147269509)
  ·
    refine ⟨2902297654593141777613033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15478920824496756147269509 2902297654593141777613033)
    ·
      refine ⟨2176723240944856333209775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2902297654593141777613033 2176723240944856333209775)
      ·
        refine ⟨3265084861417284499814663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176723240944856333209775 3265084861417284499814663)
        ·
          refine ⟨4897627292125926749721995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265084861417284499814663 4897627292125926749721995)
          ·
            refine ⟨7346440938188890124582993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897627292125926749721995 7346440938188890124582993)
            ·
              refine ⟨5509830703641667593437245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7346440938188890124582993 5509830703641667593437245)
              ·
                refine ⟨2066186513865625347538967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5509830703641667593437245 2066186513865625347538967)
                ·
                  refine ⟨3099279770798438021308451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066186513865625347538967 3099279770798438021308451)
                  ·
                    refine ⟨4648919656197657031962677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3099279770798438021308451 4648919656197657031962677)
                    ·
                      refine ⟨435836217768530346746501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4648919656197657031962677 435836217768530346746501)
                      ·
                        rfl

theorem cell23_848788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_848788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848788 prefixEnd_848788 := by exact prefixLift 848788
  have htrace : WordTrace (prefixWord ++ tailWord_848788) baseStart_848788 baseEnd_848788 := by
    simpa [prefixWord, tailWord_848788, baseEnd_848788] using wordTrace_append hprefix tailTrace_848788
  have hstable : (prefixWord ++ tailWord_848788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848788).length < 2 ^ (prefixWord ++ tailWord_848788).sum := by decide
  have hdescent : baseEnd_848788 < baseStart_848788 := by decide
  rcases family_descends (prefixWord ++ tailWord_848788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848802 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_848802 : Nat := 118140960795 + 848802 * 2 ^ 59
def prefixEnd_848802 : Nat := 4983230072969 + 3 ^ 40 * 848802 * 2
def baseEnd_848802 : Nat := 435843406497693291971437

theorem tailTrace_848802 : CollatzResearch.WordTrace tailWord_848802 prefixEnd_848802 435843406497693291971437 := by
  unfold tailWord_848802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739588067735698171387165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20638901513961861790365773 7739588067735698171387165)
  ·
    refine ⟨2902345525400886814270187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7739588067735698171387165 2902345525400886814270187)
    ·
      refine ⟨4353518288101330221405281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902345525400886814270187 4353518288101330221405281)
      ·
        refine ⟨3265138716075997666053961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4353518288101330221405281 3265138716075997666053961)
        ·
          refine ⟨2448854037056998249540471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3265138716075997666053961 2448854037056998249540471)
          ·
            refine ⟨3673281055585497374310707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448854037056998249540471 3673281055585497374310707)
            ·
              refine ⟨5509921583378246061466061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673281055585497374310707 5509921583378246061466061)
              ·
                refine ⟨2066220593766842273049773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5509921583378246061466061 2066220593766842273049773)
                ·
                  refine ⟨774832722662565852393665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2066220593766842273049773 774832722662565852393665)
                  ·
                    refine ⟨581124541996924389295249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 774832722662565852393665 581124541996924389295249)
                    ·
                      refine ⟨435843406497693291971437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581124541996924389295249 435843406497693291971437)
                      ·
                        rfl

theorem cell23_848802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_848802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848802 prefixEnd_848802 := by exact prefixLift 848802
  have htrace : WordTrace (prefixWord ++ tailWord_848802) baseStart_848802 baseEnd_848802 := by
    simpa [prefixWord, tailWord_848802, baseEnd_848802] using wordTrace_append hprefix tailTrace_848802
  have hstable : (prefixWord ++ tailWord_848802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848802).length < 2 ^ (prefixWord ++ tailWord_848802).sum := by decide
  have hdescent : baseEnd_848802 < baseStart_848802 := by decide
  rcases family_descends (prefixWord ++ tailWord_848802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848869 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_848869 : Nat := 118140960795 + 848869 * 2 ^ 59
def prefixEnd_848869 : Nat := 4983230072969 + 3 ^ 40 * 848869 * 2
def baseEnd_848869 : Nat := 435877809701544529833629

theorem tailTrace_848869 : CollatzResearch.WordTrace tailWord_848869 prefixEnd_848869 435877809701544529833629 := by
  unfold tailWord_848869
  simp only [CollatzResearch.WordTrace]
  refine ⟨30960795961700063128237661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20640530641133375418825107 30960795961700063128237661)
  ·
    refine ⟨11610298485637523673089123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30960795961700063128237661 11610298485637523673089123)
    ·
      refine ⟨17415447728456285509633685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11610298485637523673089123 17415447728456285509633685)
      ·
        refine ⟨816349112271388383264079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17415447728456285509633685 816349112271388383264079)
        ·
          refine ⟨1224523668407082574896119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816349112271388383264079 1224523668407082574896119)
          ·
            refine ⟨1836785502610623862344179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224523668407082574896119 1836785502610623862344179)
            ·
              refine ⟨2755178253915935793516269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836785502610623862344179 2755178253915935793516269)
              ·
                refine ⟨1033191845218475922568601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2755178253915935793516269 1033191845218475922568601)
                ·
                  refine ⟨774893883913856941926451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1033191845218475922568601 774893883913856941926451)
                  ·
                    refine ⟨1162340825870785412889677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 774893883913856941926451 1162340825870785412889677)
                    ·
                      refine ⟨435877809701544529833629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1162340825870785412889677 435877809701544529833629)
                      ·
                        rfl

theorem cell23_848869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_848869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848869 prefixEnd_848869 := by exact prefixLift 848869
  have htrace : WordTrace (prefixWord ++ tailWord_848869) baseStart_848869 baseEnd_848869 := by
    simpa [prefixWord, tailWord_848869, baseEnd_848869] using wordTrace_append hprefix tailTrace_848869
  have hstable : (prefixWord ++ tailWord_848869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848869).length < 2 ^ (prefixWord ++ tailWord_848869).sum := by decide
  have hdescent : baseEnd_848869 < baseStart_848869 := by decide
  rcases family_descends (prefixWord ++ tailWord_848869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848965 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 2, 4, 2]
def baseStart_848965 : Nat := 118140960795 + 848965 * 2 ^ 59
def prefixEnd_848965 : Nat := 4983230072969 + 3 ^ 40 * 848965 * 2
def baseEnd_848965 : Nat := 435927103844376154233187

theorem tailTrace_848965 : CollatzResearch.WordTrace tailWord_848965 prefixEnd_848965 435927103844376154233187 := by
  unfold tailWord_848965
  simp only [CollatzResearch.WordTrace]
  refine ⟨30964297369352271523732349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20642864912901514349154899 30964297369352271523732349)
  ·
    refine ⟨11611611513507101821399631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30964297369352271523732349 11611611513507101821399631)
    ·
      refine ⟨17417417270260652732099447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11611611513507101821399631 17417417270260652732099447)
      ·
        refine ⟨26126125905390979098149171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17417417270260652732099447 26126125905390979098149171)
        ·
          refine ⟨39189188858086468647223757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126125905390979098149171 39189188858086468647223757)
          ·
            refine ⟨14695945821782425742708909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39189188858086468647223757 14695945821782425742708909)
            ·
              refine ⟨5510979683168409653515841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14695945821782425742708909 5510979683168409653515841)
              ·
                refine ⟨4133234762376307240136881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5510979683168409653515841 4133234762376307240136881)
                ·
                  refine ⟨3099926071782230430102661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4133234762376307240136881 3099926071782230430102661)
                  ·
                    refine ⟨581236138459168205644249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3099926071782230430102661 581236138459168205644249)
                    ·
                      refine ⟨435927103844376154233187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581236138459168205644249 435927103844376154233187)
                      ·
                        rfl

theorem cell23_848965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_848965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_848965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_848965 prefixEnd_848965 := by exact prefixLift 848965
  have htrace : WordTrace (prefixWord ++ tailWord_848965) baseStart_848965 baseEnd_848965 := by
    simpa [prefixWord, tailWord_848965, baseEnd_848965] using wordTrace_append hprefix tailTrace_848965
  have hstable : (prefixWord ++ tailWord_848965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848965).length < 2 ^ (prefixWord ++ tailWord_848965).sum := by decide
  have hdescent : baseEnd_848965 < baseStart_848965 := by decide
  rcases family_descends (prefixWord ++ tailWord_848965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849052 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_849052 : Nat := 118140960795 + 849052 * 2 ^ 59
def prefixEnd_849052 : Nat := 4983230072969 + 3 ^ 40 * 849052 * 2
def baseEnd_849052 : Nat := 145323925553772437948429

theorem tailTrace_849052 : CollatzResearch.WordTrace tailWord_849052 prefixEnd_849052 145323925553772437948429 := by
  unfold tailWord_849052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15483735260018542691074705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20644980346691390254766273 15483735260018542691074705)
  ·
    refine ⟨11612801445013907018306029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15483735260018542691074705 11612801445013907018306029)
    ·
      refine ⟨4354800541880215131864761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11612801445013907018306029 4354800541880215131864761)
      ·
        refine ⟨3266100406410161348898571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4354800541880215131864761 3266100406410161348898571)
        ·
          refine ⟨4899150609615242023347857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266100406410161348898571 4899150609615242023347857)
          ·
            refine ⟨3674362957211431517510893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899150609615242023347857 3674362957211431517510893)
            ·
              refine ⟨1377886108954286819066585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3674362957211431517510893 1377886108954286819066585)
              ·
                refine ⟨1033414581715715114299939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377886108954286819066585 1033414581715715114299939)
                ·
                  refine ⟨1550121872573572671449909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033414581715715114299939 1550121872573572671449909)
                  ·
                    refine ⟨145323925553772437948429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1550121872573572671449909 145323925553772437948429)
                    ·
                      rfl

theorem cell23_849052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_849052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849052 prefixEnd_849052 := by exact prefixLift 849052
  have htrace : WordTrace (prefixWord ++ tailWord_849052) baseStart_849052 baseEnd_849052 := by
    simpa [prefixWord, tailWord_849052, baseEnd_849052] using wordTrace_append hprefix tailTrace_849052
  have hstable : (prefixWord ++ tailWord_849052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849052).length < 2 ^ (prefixWord ++ tailWord_849052).sum := by decide
  have hdescent : baseEnd_849052 < baseStart_849052 := by decide
  rcases family_descends (prefixWord ++ tailWord_849052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849068 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_849068 : Nat := 118140960795 + 849068 * 2 ^ 59
def prefixEnd_849068 : Nat := 4983230072969 + 3 ^ 40 * 849068 * 2
def baseEnd_849068 : Nat := 435979992351789251245213

theorem tailTrace_849068 : CollatzResearch.WordTrace tailWord_849068 prefixEnd_849068 435979992351789251245213 := by
  unfold tailWord_849068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15484027043989560057365929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20645369391986080076487905 15484027043989560057365929)
  ·
    refine ⟨11613020282992170043024447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15484027043989560057365929 11613020282992170043024447)
    ·
      refine ⟨17419530424488255064536671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11613020282992170043024447 17419530424488255064536671)
      ·
        refine ⟨26129295636732382596805007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17419530424488255064536671 26129295636732382596805007)
        ·
          refine ⟨39193943455098573895207511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26129295636732382596805007 39193943455098573895207511)
          ·
            refine ⟨58790915182647860842811267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39193943455098573895207511 58790915182647860842811267)
            ·
              refine ⟨88186372773971791264216901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58790915182647860842811267 88186372773971791264216901)
              ·
                refine ⟨16534944895119710862040669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88186372773971791264216901 16534944895119710862040669)
                ·
                  refine ⟨6200604335669891573265251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16534944895119710862040669 6200604335669891573265251)
                  ·
                    refine ⟨9300906503504837359897877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6200604335669891573265251 9300906503504837359897877)
                    ·
                      refine ⟨435979992351789251245213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9300906503504837359897877 435979992351789251245213)
                      ·
                        rfl

theorem cell23_849068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_849068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849068 prefixEnd_849068 := by exact prefixLift 849068
  have htrace : WordTrace (prefixWord ++ tailWord_849068) baseStart_849068 baseEnd_849068 := by
    simpa [prefixWord, tailWord_849068, baseEnd_849068] using wordTrace_append hprefix tailTrace_849068
  have hstable : (prefixWord ++ tailWord_849068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849068).length < 2 ^ (prefixWord ++ tailWord_849068).sum := by decide
  have hdescent : baseEnd_849068 < baseStart_849068 := by decide
  rcases family_descends (prefixWord ++ tailWord_849068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849072 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 5, 2, 2]
def baseStart_849072 : Nat := 118140960795 + 849072 * 2 ^ 59
def prefixEnd_849072 : Nat := 4983230072969 + 3 ^ 40 * 849072 * 2
def baseEnd_849072 : Nat := 435982046274407235595195

theorem tailTrace_849072 : CollatzResearch.WordTrace tailWord_849072 prefixEnd_849072 435982046274407235595195 := by
  unfold tailWord_849072
  simp only [CollatzResearch.WordTrace]
  refine ⟨15484099989982314398938735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20645466653309752531918313 15484099989982314398938735)
  ·
    refine ⟨23226149984973471598408103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15484099989982314398938735 23226149984973471598408103)
    ·
      refine ⟨34839224977460207397612155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23226149984973471598408103 34839224977460207397612155)
      ·
        refine ⟨52258837466190311096418233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34839224977460207397612155 52258837466190311096418233)
        ·
          refine ⟨39194128099642733322313675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52258837466190311096418233 39194128099642733322313675)
          ·
            refine ⟨58791192149464099983470513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39194128099642733322313675 58791192149464099983470513)
            ·
              refine ⟨44093394112098074987602885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58791192149464099983470513 44093394112098074987602885)
              ·
                refine ⟨8267511396018389060175541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44093394112098074987602885 8267511396018389060175541)
                ·
                  refine ⟨775079193376723974391457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8267511396018389060175541 775079193376723974391457)
                  ·
                    refine ⟨581309395032542980793593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 775079193376723974391457 581309395032542980793593)
                    ·
                      refine ⟨435982046274407235595195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581309395032542980793593 435982046274407235595195)
                      ·
                        rfl

theorem cell23_849072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 2, 2].length) (baseStart_849072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849072 prefixEnd_849072 := by exact prefixLift 849072
  have htrace : WordTrace (prefixWord ++ tailWord_849072) baseStart_849072 baseEnd_849072 := by
    simpa [prefixWord, tailWord_849072, baseEnd_849072] using wordTrace_append hprefix tailTrace_849072
  have hstable : (prefixWord ++ tailWord_849072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849072).length < 2 ^ (prefixWord ++ tailWord_849072).sum := by decide
  have hdescent : baseEnd_849072 < baseStart_849072 := by decide
  rcases family_descends (prefixWord ++ tailWord_849072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849075 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 5]
def baseStart_849075 : Nat := 118140960795 + 849075 * 2 ^ 59
def prefixEnd_849075 : Nat := 4983230072969 + 3 ^ 40 * 849075 * 2
def baseEnd_849075 : Nat := 435983586716370723857681

theorem tailTrace_849075 : CollatzResearch.WordTrace tailWord_849075 prefixEnd_849075 435983586716370723857681 := by
  unfold tailWord_849075
  simp only [CollatzResearch.WordTrace]
  refine ⟨30968309398953760310236679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20645539599302506873491119 30968309398953760310236679)
  ·
    refine ⟨46452464098430640465355019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30968309398953760310236679 46452464098430640465355019)
    ·
      refine ⟨69678696147645960698032529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46452464098430640465355019 69678696147645960698032529)
      ·
        refine ⟨52259022110734470523524397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69678696147645960698032529 52259022110734470523524397)
        ·
          refine ⟨19597133291525426446321649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52259022110734470523524397 19597133291525426446321649)
          ·
            refine ⟨14697849968644069834741237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19597133291525426446321649 14697849968644069834741237)
            ·
              refine ⟨1377923434560381547006991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14697849968644069834741237 1377923434560381547006991)
              ·
                refine ⟨2066885151840572320510487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377923434560381547006991 2066885151840572320510487)
                ·
                  refine ⟨3100327727760858480765731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066885151840572320510487 3100327727760858480765731)
                  ·
                    refine ⟨4650491591641287721148597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3100327727760858480765731 4650491591641287721148597)
                    ·
                      refine ⟨435983586716370723857681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4650491591641287721148597 435983586716370723857681)
                      ·
                        rfl

theorem cell23_849075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_849075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849075 prefixEnd_849075 := by exact prefixLift 849075
  have htrace : WordTrace (prefixWord ++ tailWord_849075) baseStart_849075 baseEnd_849075 := by
    simpa [prefixWord, tailWord_849075, baseEnd_849075] using wordTrace_append hprefix tailTrace_849075
  have hstable : (prefixWord ++ tailWord_849075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849075).length < 2 ^ (prefixWord ++ tailWord_849075).sum := by decide
  have hdescent : baseEnd_849075 < baseStart_849075 := by decide
  rcases family_descends (prefixWord ++ tailWord_849075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849110 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_849110 : Nat := 118140960795 + 849110 * 2 ^ 59
def prefixEnd_849110 : Nat := 4983230072969 + 3 ^ 40 * 849110 * 2
def baseEnd_849110 : Nat := 436001558539278086920021

theorem tailTrace_849110 : CollatzResearch.WordTrace tailWord_849110 prefixEnd_849110 436001558539278086920021 := by
  unfold tailWord_849110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935599122114185080485049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20646390635884640858507189 1935599122114185080485049)
  ·
    refine ⟨1451699341585638810363787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1935599122114185080485049 1451699341585638810363787)
    ·
      refine ⟨2177549012378458215545681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451699341585638810363787 2177549012378458215545681)
      ·
        refine ⟨1633161759283843661659261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2177549012378458215545681 1633161759283843661659261)
        ·
          refine ⟨612435659731441373122223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1633161759283843661659261 612435659731441373122223)
          ·
            refine ⟨918653489597162059683335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612435659731441373122223 918653489597162059683335)
            ·
              refine ⟨1377980234395743089525003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918653489597162059683335 1377980234395743089525003)
              ·
                refine ⟨2066970351593614634287505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377980234395743089525003 2066970351593614634287505)
                ·
                  refine ⟨1550227763695210975715629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2066970351593614634287505 1550227763695210975715629)
                  ·
                    refine ⟨581335411385704115893361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550227763695210975715629 581335411385704115893361)
                    ·
                      refine ⟨436001558539278086920021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581335411385704115893361 436001558539278086920021)
                      ·
                        rfl

theorem cell23_849110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_849110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849110 prefixEnd_849110 := by exact prefixLift 849110
  have htrace : WordTrace (prefixWord ++ tailWord_849110) baseStart_849110 baseEnd_849110 := by
    simpa [prefixWord, tailWord_849110, baseEnd_849110] using wordTrace_append hprefix tailTrace_849110
  have hstable : (prefixWord ++ tailWord_849110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849110).length < 2 ^ (prefixWord ++ tailWord_849110).sum := by decide
  have hdescent : baseEnd_849110 < baseStart_849110 := by decide
  rcases family_descends (prefixWord ++ tailWord_849110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849112 : List Nat := [2, 1, 2, 2, 5, 1, 3, 7]
def baseStart_849112 : Nat := 118140960795 + 849112 * 2 ^ 59
def prefixEnd_849112 : Nat := 4983230072969 + 3 ^ 40 * 849112 * 2
def baseEnd_849112 : Nat := 16148243907429151077593

theorem tailTrace_849112 : CollatzResearch.WordTrace tailWord_849112 prefixEnd_849112 16148243907429151077593 := by
  unfold tailWord_849112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15484829449909857814666795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20646439266546477086222393 15484829449909857814666795)
  ·
    refine ⟨23227244174864786722000193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15484829449909857814666795 23227244174864786722000193)
    ·
      refine ⟨17420433131148590041500145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23227244174864786722000193 17420433131148590041500145)
      ·
        refine ⟨13065324848361442531125109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17420433131148590041500145 13065324848361442531125109)
        ·
          refine ⟨1224874204533885237292979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13065324848361442531125109 1224874204533885237292979)
          ·
            refine ⟨1837311306800827855939469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224874204533885237292979 1837311306800827855939469)
            ·
              refine ⟨688991740050310445977301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1837311306800827855939469 688991740050310445977301)
              ·
                refine ⟨16148243907429151077593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 688991740050310445977301 16148243907429151077593)
                ·
                  rfl

theorem cell23_849112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 7].length) (baseStart_849112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849112 prefixEnd_849112 := by exact prefixLift 849112
  have htrace : WordTrace (prefixWord ++ tailWord_849112) baseStart_849112 baseEnd_849112 := by
    simpa [prefixWord, tailWord_849112, baseEnd_849112] using wordTrace_append hprefix tailTrace_849112
  have hstable : (prefixWord ++ tailWord_849112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849112).length < 2 ^ (prefixWord ++ tailWord_849112).sum := by decide
  have hdescent : baseEnd_849112 < baseStart_849112 := by decide
  rcases family_descends (prefixWord ++ tailWord_849112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849139 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 3]
def baseStart_849139 : Nat := 118140960795 + 849139 * 2 ^ 59
def prefixEnd_849139 : Nat := 4983230072969 + 3 ^ 40 * 849139 * 2
def baseEnd_849139 : Nat := 436016449478258473457387

theorem tailTrace_849139 : CollatzResearch.WordTrace tailWord_849139 prefixEnd_849139 436016449478258473457387 := by
  unfold tailWord_849139
  simp only [CollatzResearch.WordTrace]
  refine ⟨30970643670721899240566471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20647095780481266160377647 30970643670721899240566471)
  ·
    refine ⟨46455965506082848860849707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30970643670721899240566471 46455965506082848860849707)
    ·
      refine ⟨69683948259124273291274561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46455965506082848860849707 69683948259124273291274561)
      ·
        refine ⟨52262961194343204968455921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69683948259124273291274561 52262961194343204968455921)
        ·
          refine ⟨39197220895757403726341941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52262961194343204968455921 39197220895757403726341941)
          ·
            refine ⟨3674739458977256599344557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39197220895757403726341941 3674739458977256599344557)
            ·
              refine ⟨1378027297116471224754209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3674739458977256599344557 1378027297116471224754209)
              ·
                refine ⟨1033520472837353418565657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378027297116471224754209 1033520472837353418565657)
                ·
                  refine ⟨775140354628015063924243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1033520472837353418565657 775140354628015063924243)
                  ·
                    refine ⟨1162710531942022595886365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 775140354628015063924243 1162710531942022595886365)
                    ·
                      refine ⟨436016449478258473457387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1162710531942022595886365 436016449478258473457387)
                      ·
                        rfl

theorem cell23_849139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 3].length) (baseStart_849139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849139 prefixEnd_849139 := by exact prefixLift 849139
  have htrace : WordTrace (prefixWord ++ tailWord_849139) baseStart_849139 baseEnd_849139 := by
    simpa [prefixWord, tailWord_849139, baseEnd_849139] using wordTrace_append hprefix tailTrace_849139
  have hstable : (prefixWord ++ tailWord_849139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849139).length < 2 ^ (prefixWord ++ tailWord_849139).sum := by decide
  have hdescent : baseEnd_849139 < baseStart_849139 := by decide
  rcases family_descends (prefixWord ++ tailWord_849139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849155 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 2, 6]
def baseStart_849155 : Nat := 118140960795 + 849155 * 2 ^ 59
def prefixEnd_849155 : Nat := 4983230072969 + 3 ^ 40 * 849155 * 2
def baseEnd_849155 : Nat := 145341555056243470285771

theorem tailTrace_849155 : CollatzResearch.WordTrace tailWord_849155 prefixEnd_849155 145341555056243470285771 := by
  unfold tailWord_849155
  simp only [CollatzResearch.WordTrace]
  refine ⟨30971227238663933973148919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20647484825775955982099279 30971227238663933973148919)
  ·
    refine ⟨46456840857995900959723379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30971227238663933973148919 46456840857995900959723379)
    ·
      refine ⟨69685261286993851439585069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46456840857995900959723379 69685261286993851439585069)
      ·
        refine ⟨26131972982622694289844401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69685261286993851439585069 26131972982622694289844401)
        ·
          refine ⟨19598979736967020717383301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26131972982622694289844401 19598979736967020717383301)
          ·
            refine ⟨3674808700681316384509369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19598979736967020717383301 3674808700681316384509369)
            ·
              refine ⟨2756106525510987288382027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3674808700681316384509369 2756106525510987288382027)
              ·
                refine ⟨4134159788266480932573041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756106525510987288382027 4134159788266480932573041)
                ·
                  refine ⟨3100619841199860699429781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134159788266480932573041 3100619841199860699429781)
                  ·
                    refine ⟨145341555056243470285771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3100619841199860699429781 145341555056243470285771)
                    ·
                      rfl

theorem cell23_849155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 6].length) (baseStart_849155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849155 prefixEnd_849155 := by exact prefixLift 849155
  have htrace : WordTrace (prefixWord ++ tailWord_849155) baseStart_849155 baseEnd_849155 := by
    simpa [prefixWord, tailWord_849155, baseEnd_849155] using wordTrace_append hprefix tailTrace_849155
  have hstable : (prefixWord ++ tailWord_849155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849155).length < 2 ^ (prefixWord ++ tailWord_849155).sum := by decide
  have hdescent : baseEnd_849155 < baseStart_849155 := by decide
  rcases family_descends (prefixWord ++ tailWord_849155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849166 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_849166 : Nat := 118140960795 + 849166 * 2 ^ 59
def prefixEnd_849166 : Nat := 4983230072969 + 3 ^ 40 * 849166 * 2
def baseEnd_849166 : Nat := 436030313455929867819763

theorem tailTrace_849166 : CollatzResearch.WordTrace tailWord_849166 prefixEnd_849166 436030313455929867819763 := by
  unfold tailWord_849166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871453555203010356474919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20647752294416055234532901 3871453555203010356474919)
  ·
    refine ⟨5807180332804515534712379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3871453555203010356474919 5807180332804515534712379)
    ·
      refine ⟨8710770499206773302068569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807180332804515534712379 8710770499206773302068569)
      ·
        refine ⟨6533077874405079976551427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8710770499206773302068569 6533077874405079976551427)
        ·
          refine ⟨9799616811607619964827141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533077874405079976551427 9799616811607619964827141)
          ·
            refine ⟨1837428152176428743405089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9799616811607619964827141 1837428152176428743405089)
            ·
              refine ⟨1378071114132321557553817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837428152176428743405089 1378071114132321557553817)
              ·
                refine ⟨1033553335599241168165363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378071114132321557553817 1033553335599241168165363)
                ·
                  refine ⟨1550330003398861752248045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033553335599241168165363 1550330003398861752248045)
                  ·
                    refine ⟨581373751274573157093017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550330003398861752248045 581373751274573157093017)
                    ·
                      refine ⟨436030313455929867819763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581373751274573157093017 436030313455929867819763)
                      ·
                        rfl

theorem cell23_849166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_849166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849166 prefixEnd_849166 := by exact prefixLift 849166
  have htrace : WordTrace (prefixWord ++ tailWord_849166) baseStart_849166 baseEnd_849166 := by
    simpa [prefixWord, tailWord_849166, baseEnd_849166] using wordTrace_append hprefix tailTrace_849166
  have hstable : (prefixWord ++ tailWord_849166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849166).length < 2 ^ (prefixWord ++ tailWord_849166).sum := by decide
  have hdescent : baseEnd_849166 < baseStart_849166 := by decide
  rcases family_descends (prefixWord ++ tailWord_849166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849195 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 3]
def baseStart_849195 : Nat := 118140960795 + 849195 * 2 ^ 59
def prefixEnd_849195 : Nat := 4983230072969 + 3 ^ 40 * 849195 * 2
def baseEnd_849195 : Nat := 436045204394910254357129

theorem tailTrace_849195 : CollatzResearch.WordTrace tailWord_849195 prefixEnd_849195 436045204394910254357129 := by
  unfold tailWord_849195
  simp only [CollatzResearch.WordTrace]
  refine ⟨30972686158519020804605039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20648457439012680536403359 30972686158519020804605039)
  ·
    refine ⟨46459029237778531206907559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30972686158519020804605039 46459029237778531206907559)
    ·
      refine ⟨69688543856667796810361339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46459029237778531206907559 69688543856667796810361339)
      ·
        refine ⟨104532815785001695215542009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69688543856667796810361339 104532815785001695215542009)
        ·
          refine ⟨78399611838751271411656507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104532815785001695215542009 78399611838751271411656507)
          ·
            refine ⟨117599417758126907117484761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78399611838751271411656507 117599417758126907117484761)
            ·
              refine ⟨88199563318595180338113571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117599417758126907117484761 88199563318595180338113571)
              ·
                refine ⟨132299344977892770507170357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88199563318595180338113571 132299344977892770507170357)
                ·
                  refine ⟨12403063591677447235047221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132299344977892770507170357 12403063591677447235047221)
                  ·
                    refine ⟨1162787211719760678285677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12403063591677447235047221 1162787211719760678285677)
                    ·
                      refine ⟨436045204394910254357129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1162787211719760678285677 436045204394910254357129)
                      ·
                        rfl

theorem cell23_849195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 3].length) (baseStart_849195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849195 prefixEnd_849195 := by exact prefixLift 849195
  have htrace : WordTrace (prefixWord ++ tailWord_849195) baseStart_849195 baseEnd_849195 := by
    simpa [prefixWord, tailWord_849195, baseEnd_849195] using wordTrace_append hprefix tailTrace_849195
  have hstable : (prefixWord ++ tailWord_849195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849195).length < 2 ^ (prefixWord ++ tailWord_849195).sum := by decide
  have hdescent : baseEnd_849195 < baseStart_849195 := by decide
  rcases family_descends (prefixWord ++ tailWord_849195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849202 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 7]
def baseStart_849202 : Nat := 118140960795 + 849202 * 2 ^ 59
def prefixEnd_849202 : Nat := 4983230072969 + 3 ^ 40 * 849202 * 2
def baseEnd_849202 : Nat := 48449866528832414107733

theorem tailTrace_849202 : CollatzResearch.WordTrace tailWord_849202 prefixEnd_849202 48449866528832414107733 := by
  unfold tailWord_849202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7743235367373415250027465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20648627646329107333406573 7743235367373415250027465)
  ·
    refine ⟨5807426525530061437520599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7743235367373415250027465 5807426525530061437520599)
    ·
      refine ⟨8711139788295092156280899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807426525530061437520599 8711139788295092156280899)
      ·
        refine ⟨13066709682442638234421349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8711139788295092156280899 13066709682442638234421349)
        ·
          refine ⟨2450008065457994668954003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13066709682442638234421349 2450008065457994668954003)
          ·
            refine ⟨3675012098186992003431005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450008065457994668954003 3675012098186992003431005)
            ·
              refine ⟨1378129536820122001286627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3675012098186992003431005 1378129536820122001286627)
              ·
                refine ⟨2067194305230183001929941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378129536820122001286627 2067194305230183001929941)
                ·
                  refine ⟨48449866528832414107733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2067194305230183001929941 48449866528832414107733)
                  ·
                    rfl

theorem cell23_849202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_849202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849202 prefixEnd_849202 := by exact prefixLift 849202
  have htrace : WordTrace (prefixWord ++ tailWord_849202) baseStart_849202 baseEnd_849202 := by
    simpa [prefixWord, tailWord_849202, baseEnd_849202] using wordTrace_append hprefix tailTrace_849202
  have hstable : (prefixWord ++ tailWord_849202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849202).length < 2 ^ (prefixWord ++ tailWord_849202).sum := by decide
  have hdescent : baseEnd_849202 < baseStart_849202 := by decide
  rcases family_descends (prefixWord ++ tailWord_849202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849232 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 2, 5]
def baseStart_849232 : Nat := 118140960795 + 849232 * 2 ^ 59
def prefixEnd_849232 : Nat := 4983230072969 + 3 ^ 40 * 849232 * 2
def baseEnd_849232 : Nat := 145354734393042203198153

theorem tailTrace_849232 : CollatzResearch.WordTrace tailWord_849232 prefixEnd_849232 145354734393042203198153 := by
  unfold tailWord_849232
  simp only [CollatzResearch.WordTrace]
  refine ⟨15487017829692488061850975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20649357106256650749134633 15487017829692488061850975)
  ·
    refine ⟨23230526744538732092776463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15487017829692488061850975 23230526744538732092776463)
    ·
      refine ⟨34845790116808098139164695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23230526744538732092776463 34845790116808098139164695)
      ·
        refine ⟨52268685175212147208747043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34845790116808098139164695 52268685175212147208747043)
        ·
          refine ⟨78403027762818220813120565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52268685175212147208747043 78403027762818220813120565)
          ·
            refine ⟨7350283852764208201230053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78403027762818220813120565 7350283852764208201230053)
            ·
              refine ⟨1378178222393289037730635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7350283852764208201230053 1378178222393289037730635)
              ·
                refine ⟨2067267333589933556595953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378178222393289037730635 2067267333589933556595953)
                ·
                  refine ⟨1550450500192450167446965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2067267333589933556595953 1550450500192450167446965)
                  ·
                    refine ⟨145354734393042203198153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1550450500192450167446965 145354734393042203198153)
                    ·
                      rfl

theorem cell23_849232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_849232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849232 prefixEnd_849232 := by exact prefixLift 849232
  have htrace : WordTrace (prefixWord ++ tailWord_849232) baseStart_849232 baseEnd_849232 := by
    simpa [prefixWord, tailWord_849232, baseEnd_849232] using wordTrace_append hprefix tailTrace_849232
  have hstable : (prefixWord ++ tailWord_849232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849232).length < 2 ^ (prefixWord ++ tailWord_849232).sum := by decide
  have hdescent : baseEnd_849232 < baseStart_849232 := by decide
  rcases family_descends (prefixWord ++ tailWord_849232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849289 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 3]
def baseStart_849289 : Nat := 118140960795 + 849289 * 2 ^ 59
def prefixEnd_849289 : Nat := 4983230072969 + 3 ^ 40 * 849289 * 2
def baseEnd_849289 : Nat := 436093471576432886581697

theorem tailTrace_849289 : CollatzResearch.WordTrace tailWord_849289 prefixEnd_849289 436093471576432886581697 := by
  unfold tailWord_849289
  simp only [CollatzResearch.WordTrace]
  refine ⟨30976114620178474858526921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20650743080118983239017947 30976114620178474858526921)
  ·
    refine ⟨23232085965133856143895191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30976114620178474858526921 23232085965133856143895191)
    ·
      refine ⟨34848128947700784215842787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23232085965133856143895191 34848128947700784215842787)
      ·
        refine ⟨52272193421551176323764181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34848128947700784215842787 52272193421551176323764181)
        ·
          refine ⟨1225129533317605695088223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52272193421551176323764181 1225129533317605695088223)
          ·
            refine ⟨1837694299976408542632335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225129533317605695088223 1837694299976408542632335)
            ·
              refine ⟨2756541449964612813948503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837694299976408542632335 2756541449964612813948503)
              ·
                refine ⟨4134812174946919220922755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756541449964612813948503 4134812174946919220922755)
                ·
                  refine ⟨6202218262420378831384133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134812174946919220922755 6202218262420378831384133)
                  ·
                    refine ⟨1162915924203821030884525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6202218262420378831384133 1162915924203821030884525)
                    ·
                      refine ⟨436093471576432886581697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1162915924203821030884525 436093471576432886581697)
                      ·
                        rfl

theorem cell23_849289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_849289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849289 prefixEnd_849289 := by exact prefixLift 849289
  have htrace : WordTrace (prefixWord ++ tailWord_849289) baseStart_849289 baseEnd_849289 := by
    simpa [prefixWord, tailWord_849289, baseEnd_849289] using wordTrace_append hprefix tailTrace_849289
  have hstable : (prefixWord ++ tailWord_849289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849289).length < 2 ^ (prefixWord ++ tailWord_849289).sum := by decide
  have hdescent : baseEnd_849289 < baseStart_849289 := by decide
  rcases family_descends (prefixWord ++ tailWord_849289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849309 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 6]
def baseStart_849309 : Nat := 118140960795 + 849309 * 2 ^ 59
def prefixEnd_849309 : Nat := 4983230072969 + 3 ^ 40 * 849309 * 2
def baseEnd_849309 : Nat := 48455971243280312036845

theorem tailTrace_849309 : CollatzResearch.WordTrace tailWord_849309 prefixEnd_849309 48455971243280312036845 := by
  unfold tailWord_849309
  simp only [CollatzResearch.WordTrace]
  refine ⟨30976844080106018274254981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20651229386737345516169987 30976844080106018274254981)
  ·
    refine ⟨5808158265019878426422809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30976844080106018274254981 5808158265019878426422809)
    ·
      refine ⟨4356118698764908819817107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5808158265019878426422809 4356118698764908819817107)
      ·
        refine ⟨6534178048147363229725661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356118698764908819817107 6534178048147363229725661)
        ·
          refine ⟨2450316768055261211147123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6534178048147363229725661 2450316768055261211147123)
          ·
            refine ⟨3675475152082891816720685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450316768055261211147123 3675475152082891816720685)
            ·
              refine ⟨1378303182031084431270257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3675475152082891816720685 1378303182031084431270257)
              ·
                refine ⟨1033727386523313323452693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378303182031084431270257 1033727386523313323452693)
                ·
                  refine ⟨48455971243280312036845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1033727386523313323452693 48455971243280312036845)
                  ·
                    rfl

theorem cell23_849309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_849309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849309 prefixEnd_849309 := by exact prefixLift 849309
  have htrace : WordTrace (prefixWord ++ tailWord_849309) baseStart_849309 baseEnd_849309 := by
    simpa [prefixWord, tailWord_849309, baseEnd_849309] using wordTrace_append hprefix tailTrace_849309
  have hstable : (prefixWord ++ tailWord_849309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849309).length < 2 ^ (prefixWord ++ tailWord_849309).sum := by decide
  have hdescent : baseEnd_849309 < baseStart_849309 := by decide
  rcases family_descends (prefixWord ++ tailWord_849309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849329 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 3, 5, 2]
def baseStart_849329 : Nat := 118140960795 + 849329 * 2 ^ 59
def prefixEnd_849329 : Nat := 4983230072969 + 3 ^ 40 * 849329 * 2
def baseEnd_849329 : Nat := 436114010802612730081513

theorem tailTrace_849329 : CollatzResearch.WordTrace tailWord_849329 prefixEnd_849329 436114010802612730081513 := by
  unfold tailWord_849329
  simp only [CollatzResearch.WordTrace]
  refine ⟨30977573540033561689983041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20651715693355707793322027 30977573540033561689983041)
  ·
    refine ⟨23233180155025171267487281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30977573540033561689983041 23233180155025171267487281)
    ·
      refine ⟨17424885116268878450615461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23233180155025171267487281 17424885116268878450615461)
      ·
        refine ⟨3267165959300414709490399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17424885116268878450615461 3267165959300414709490399)
        ·
          refine ⟨4900748938950622064235599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267165959300414709490399 4900748938950622064235599)
          ·
            refine ⟨7351123408425933096353399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900748938950622064235599 7351123408425933096353399)
            ·
              refine ⟨11026685112638899644530099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351123408425933096353399 11026685112638899644530099)
              ·
                refine ⟨16540027668958349466795149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026685112638899644530099 16540027668958349466795149)
                ·
                  refine ⟨6202510375859381050048181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16540027668958349466795149 6202510375859381050048181)
                  ·
                    refine ⟨581485347736816973442017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6202510375859381050048181 581485347736816973442017)
                    ·
                      refine ⟨436114010802612730081513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581485347736816973442017 436114010802612730081513)
                      ·
                        rfl

theorem cell23_849329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_849329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849329 prefixEnd_849329 := by exact prefixLift 849329
  have htrace : WordTrace (prefixWord ++ tailWord_849329) baseStart_849329 baseEnd_849329 := by
    simpa [prefixWord, tailWord_849329, baseEnd_849329] using wordTrace_append hprefix tailTrace_849329
  have hstable : (prefixWord ++ tailWord_849329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849329).length < 2 ^ (prefixWord ++ tailWord_849329).sum := by decide
  have hdescent : baseEnd_849329 < baseStart_849329 := by decide
  rcases family_descends (prefixWord ++ tailWord_849329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849352 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 3, 6]
def baseStart_849352 : Nat := 118140960795 + 849352 * 2 ^ 59
def prefixEnd_849352 : Nat := 4983230072969 + 3 ^ 40 * 849352 * 2
def baseEnd_849352 : Nat := 145375273619222046697969

theorem tailTrace_849352 : CollatzResearch.WordTrace tailWord_849352 prefixEnd_849352 145375273619222046697969 := by
  unfold tailWord_849352
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489206209475118309035155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20652274945966824412046873 15489206209475118309035155)
  ·
    refine ⟨23233809314212677463552733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15489206209475118309035155 23233809314212677463552733)
    ·
      refine ⟨8712678492829754048832275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23233809314212677463552733 8712678492829754048832275)
      ·
        refine ⟨13069017739244631073248413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712678492829754048832275 13069017739244631073248413)
        ·
          refine ⟨4900881652216736652468155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13069017739244631073248413 4900881652216736652468155)
          ·
            refine ⟨7351322478325104978702233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900881652216736652468155 7351322478325104978702233)
            ·
              refine ⟨5513491858743828734026675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7351322478325104978702233 5513491858743828734026675)
              ·
                refine ⟨8270237788115743101040013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513491858743828734026675 8270237788115743101040013)
                ·
                  refine ⟨3101339170543403662890005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8270237788115743101040013 3101339170543403662890005)
                  ·
                    refine ⟨145375273619222046697969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3101339170543403662890005 145375273619222046697969)
                    ·
                      rfl

theorem cell23_849352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_849352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849352 prefixEnd_849352 := by exact prefixLift 849352
  have htrace : WordTrace (prefixWord ++ tailWord_849352) baseStart_849352 baseEnd_849352 := by
    simpa [prefixWord, tailWord_849352, baseEnd_849352] using wordTrace_append hprefix tailTrace_849352
  have hstable : (prefixWord ++ tailWord_849352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849352).length < 2 ^ (prefixWord ++ tailWord_849352).sum := by decide
  have hdescent : baseEnd_849352 < baseStart_849352 := by decide
  rcases family_descends (prefixWord ++ tailWord_849352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849359 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 4]
def baseStart_849359 : Nat := 118140960795 + 849359 * 2 ^ 59
def prefixEnd_849359 : Nat := 4983230072969 + 3 ^ 40 * 849359 * 2
def baseEnd_849359 : Nat := 436129415222247612706375

theorem tailTrace_849359 : CollatzResearch.WordTrace tailWord_849359 prefixEnd_849359 436129415222247612706375 := by
  unfold tailWord_849359
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978667729924876813575131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20652445153283251209050087 30978667729924876813575131)
  ·
    refine ⟨46468001594887315220362697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30978667729924876813575131 46468001594887315220362697)
    ·
      refine ⟨34851001196165486415272023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46468001594887315220362697 34851001196165486415272023)
      ·
        refine ⟨52276501794248229622908035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34851001196165486415272023 52276501794248229622908035)
        ·
          refine ⟨78414752691372344434362053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52276501794248229622908035 78414752691372344434362053)
          ·
            refine ⟨14702766129632314581442885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78414752691372344434362053 14702766129632314581442885)
            ·
              refine ⟨2756768649306058984020541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14702766129632314581442885 2756768649306058984020541)
              ·
                refine ⟨1033788243489772119007703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2756768649306058984020541 1033788243489772119007703)
                ·
                  refine ⟨1550682365234658178511555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033788243489772119007703 1550682365234658178511555)
                  ·
                    refine ⟨2326023547851987267767333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1550682365234658178511555 2326023547851987267767333)
                    ·
                      refine ⟨436129415222247612706375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2326023547851987267767333 436129415222247612706375)
                      ·
                        rfl

theorem cell23_849359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 4].length) (baseStart_849359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849359 prefixEnd_849359 := by exact prefixLift 849359
  have htrace : WordTrace (prefixWord ++ tailWord_849359) baseStart_849359 baseEnd_849359 := by
    simpa [prefixWord, tailWord_849359, baseEnd_849359] using wordTrace_append hprefix tailTrace_849359
  have hstable : (prefixWord ++ tailWord_849359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849359).length < 2 ^ (prefixWord ++ tailWord_849359).sum := by decide
  have hdescent : baseEnd_849359 < baseStart_849359 := by decide
  rcases family_descends (prefixWord ++ tailWord_849359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849369 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 4, 4]
def baseStart_849369 : Nat := 118140960795 + 849369 * 2 ^ 59
def prefixEnd_849369 : Nat := 4983230072969 + 3 ^ 40 * 849369 * 2
def baseEnd_849369 : Nat := 145378183342930857860443

theorem tailTrace_849369 : CollatzResearch.WordTrace tailWord_849369 prefixEnd_849369 145378183342930857860443 := by
  unfold tailWord_849369
  simp only [CollatzResearch.WordTrace]
  refine ⟨30979032459888648521439161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20652688306592432347626107 30979032459888648521439161)
  ·
    refine ⟨23234274344916486391079371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30979032459888648521439161 23234274344916486391079371)
    ·
      refine ⟨34851411517374729586619057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23234274344916486391079371 34851411517374729586619057)
      ·
        refine ⟨26138558638031047189964293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34851411517374729586619057 26138558638031047189964293)
        ·
          refine ⟨4900979744630821348118305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26138558638031047189964293 4900979744630821348118305)
          ·
            refine ⟨3675734808473116011088729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900979744630821348118305 3675734808473116011088729)
            ·
              refine ⟨2756801106354837008316547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675734808473116011088729 2756801106354837008316547)
              ·
                refine ⟨4135201659532255512474821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756801106354837008316547 4135201659532255512474821)
                ·
                  refine ⟨775350311162297908589029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4135201659532255512474821 775350311162297908589029)
                  ·
                    refine ⟨145378183342930857860443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 775350311162297908589029 145378183342930857860443)
                    ·
                      rfl

theorem cell23_849369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 4].length) (baseStart_849369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849369 prefixEnd_849369 := by exact prefixLift 849369
  have htrace : WordTrace (prefixWord ++ tailWord_849369) baseStart_849369 baseEnd_849369 := by
    simpa [prefixWord, tailWord_849369, baseEnd_849369] using wordTrace_append hprefix tailTrace_849369
  have hstable : (prefixWord ++ tailWord_849369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849369).length < 2 ^ (prefixWord ++ tailWord_849369).sum := by decide
  have hdescent : baseEnd_849369 < baseStart_849369 := by decide
  rcases family_descends (prefixWord ++ tailWord_849369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849370 : List Nat := [3, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3]
def baseStart_849370 : Nat := 118140960795 + 849370 * 2 ^ 59
def prefixEnd_849370 : Nat := 4983230072969 + 3 ^ 40 * 849370 * 2
def baseEnd_849370 : Nat := 436135063509447069668825

theorem tailTrace_849370 : CollatzResearch.WordTrace tailWord_849370 prefixEnd_849370 436135063509447069668825 := by
  unfold tailWord_849370
  simp only [CollatzResearch.WordTrace]
  refine ⟨7744767233221256423056391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20652712621923350461483709 7744767233221256423056391)
  ·
    refine ⟨11617150849831884634584587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7744767233221256423056391 11617150849831884634584587)
    ·
      refine ⟨17425726274747826951876881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11617150849831884634584587 17425726274747826951876881)
      ·
        refine ⟨13069294706060870213907661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17425726274747826951876881 13069294706060870213907661)
        ·
          refine ⟨4900985514772826330215373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13069294706060870213907661 4900985514772826330215373)
          ·
            refine ⟨1837869568039809873830765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4900985514772826330215373 1837869568039809873830765)
            ·
              refine ⟨689201088014928702686537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1837869568039809873830765 689201088014928702686537)
              ·
                refine ⟨516900816011196527014903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689201088014928702686537 516900816011196527014903)
                ·
                  refine ⟨775351224016794790522355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516900816011196527014903 775351224016794790522355)
                  ·
                    refine ⟨1163026836025192185783533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 775351224016794790522355 1163026836025192185783533)
                    ·
                      refine ⟨436135063509447069668825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163026836025192185783533 436135063509447069668825)
                      ·
                        rfl

theorem cell23_849370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_849370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849370 prefixEnd_849370 := by exact prefixLift 849370
  have htrace : WordTrace (prefixWord ++ tailWord_849370) baseStart_849370 baseEnd_849370 := by
    simpa [prefixWord, tailWord_849370, baseEnd_849370] using wordTrace_append hprefix tailTrace_849370
  have hstable : (prefixWord ++ tailWord_849370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849370).length < 2 ^ (prefixWord ++ tailWord_849370).sum := by decide
  have hdescent : baseEnd_849370 < baseStart_849370 := by decide
  rcases family_descends (prefixWord ++ tailWord_849370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849376 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 3, 2, 2]
def baseStart_849376 : Nat := 118140960795 + 849376 * 2 ^ 59
def prefixEnd_849376 : Nat := 4983230072969 + 3 ^ 40 * 849376 * 2
def baseEnd_849376 : Nat := 436138144393374046193797

theorem tailTrace_849376 : CollatzResearch.WordTrace tailWord_849376 prefixEnd_849376 436138144393374046193797 := by
  unfold tailWord_849376
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489643885431644358471991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20652858513908859144629321 15489643885431644358471991)
  ·
    refine ⟨23234465828147466537707987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15489643885431644358471991 23234465828147466537707987)
    ·
      refine ⟨34851698742221199806561981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23234465828147466537707987 34851698742221199806561981)
      ·
        refine ⟨13069387028332949927460743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34851698742221199806561981 13069387028332949927460743)
        ·
          refine ⟨19604080542499424891191115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13069387028332949927460743 19604080542499424891191115)
          ·
            refine ⟨29406120813749137336786673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19604080542499424891191115 29406120813749137336786673)
            ·
              refine ⟨22054590610311853002590005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29406120813749137336786673 22054590610311853002590005)
              ·
                refine ⟨2067617869716736218992813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22054590610311853002590005 2067617869716736218992813)
                ·
                  refine ⟨775356701143776082122305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2067617869716736218992813 775356701143776082122305)
                  ·
                    refine ⟨581517525857832061591729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 775356701143776082122305 581517525857832061591729)
                    ·
                      refine ⟨436138144393374046193797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581517525857832061591729 436138144393374046193797)
                      ·
                        rfl

theorem cell23_849376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_849376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849376 prefixEnd_849376 := by exact prefixLift 849376
  have htrace : WordTrace (prefixWord ++ tailWord_849376) baseStart_849376 baseEnd_849376 := by
    simpa [prefixWord, tailWord_849376, baseEnd_849376] using wordTrace_append hprefix tailTrace_849376
  have hstable : (prefixWord ++ tailWord_849376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849376).length < 2 ^ (prefixWord ++ tailWord_849376).sum := by decide
  have hdescent : baseEnd_849376 < baseStart_849376 := by decide
  rcases family_descends (prefixWord ++ tailWord_849376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849379 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 5]
def baseStart_849379 : Nat := 118140960795 + 849379 * 2 ^ 59
def prefixEnd_849379 : Nat := 4983230072969 + 3 ^ 40 * 849379 * 2
def baseEnd_849379 : Nat := 436139684835337534456283

theorem tailTrace_849379 : CollatzResearch.WordTrace tailWord_849379 prefixEnd_849379 436139684835337534456283 := by
  unfold tailWord_849379
  simp only [CollatzResearch.WordTrace]
  refine ⟨30979397189852420229303191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20652931459901613486202127 30979397189852420229303191)
  ·
    refine ⟨46469095784778630343954787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30979397189852420229303191 46469095784778630343954787)
    ·
      refine ⟨69703643677167945515932181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46469095784778630343954787 69703643677167945515932181)
      ·
        refine ⟨3267358297367247446059321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69703643677167945515932181 3267358297367247446059321)
        ·
          refine ⟨2450518723025435584544491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3267358297367247446059321 2450518723025435584544491)
          ·
            refine ⟨3675778084538153376816737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450518723025435584544491 3675778084538153376816737)
            ·
              refine ⟨2756833563403615032612553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675778084538153376816737 2756833563403615032612553)
              ·
                refine ⟨2067625172552711274459415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2756833563403615032612553 2067625172552711274459415)
                ·
                  refine ⟨3101437758829066911689123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067625172552711274459415 3101437758829066911689123)
                  ·
                    refine ⟨4652156638243600367533685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3101437758829066911689123 4652156638243600367533685)
                    ·
                      refine ⟨436139684835337534456283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4652156638243600367533685 436139684835337534456283)
                      ·
                        rfl

theorem cell23_849379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_849379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849379 prefixEnd_849379 := by exact prefixLift 849379
  have htrace : WordTrace (prefixWord ++ tailWord_849379) baseStart_849379 baseEnd_849379 := by
    simpa [prefixWord, tailWord_849379, baseEnd_849379] using wordTrace_append hprefix tailTrace_849379
  have hstable : (prefixWord ++ tailWord_849379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849379).length < 2 ^ (prefixWord ++ tailWord_849379).sum := by decide
  have hdescent : baseEnd_849379 < baseStart_849379 := by decide
  rcases family_descends (prefixWord ++ tailWord_849379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849410 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_849410 : Nat := 118140960795 + 849410 * 2 ^ 59
def prefixEnd_849410 : Nat := 4983230072969 + 3 ^ 40 * 849410 * 2
def baseEnd_849410 : Nat := 436155602735626913168641

theorem tailTrace_849410 : CollatzResearch.WordTrace tailWord_849410 prefixEnd_849410 436155602735626913168641 := by
  unfold tailWord_849410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7745131963185028130920421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20653685235160075015787789 7745131963185028130920421)
  ·
    refine ⟨1452212243097192774547579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7745131963185028130920421 1452212243097192774547579)
    ·
      refine ⟨2178318364645789161821369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452212243097192774547579 2178318364645789161821369)
      ·
        refine ⟨1633738773484341871366027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2178318364645789161821369 1633738773484341871366027)
        ·
          refine ⟨2450608160226512807049041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633738773484341871366027 2450608160226512807049041)
          ·
            refine ⟨1837956120169884605286781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2450608160226512807049041 1837956120169884605286781)
            ·
              refine ⟨689233545063706726982543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1837956120169884605286781 689233545063706726982543)
              ·
                refine ⟨1033850317595560090473815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689233545063706726982543 1033850317595560090473815)
                ·
                  refine ⟨1550775476393340135710723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033850317595560090473815 1550775476393340135710723)
                  ·
                    refine ⟨2326163214590010203566085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1550775476393340135710723 2326163214590010203566085)
                    ·
                      refine ⟨436155602735626913168641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2326163214590010203566085 436155602735626913168641)
                      ·
                        rfl

theorem cell23_849410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_849410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849410 prefixEnd_849410 := by exact prefixLift 849410
  have htrace : WordTrace (prefixWord ++ tailWord_849410) baseStart_849410 baseEnd_849410 := by
    simpa [prefixWord, tailWord_849410, baseEnd_849410] using wordTrace_append hprefix tailTrace_849410
  have hstable : (prefixWord ++ tailWord_849410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849410).length < 2 ^ (prefixWord ++ tailWord_849410).sum := by decide
  have hdescent : baseEnd_849410 < baseStart_849410 := by decide
  rcases family_descends (prefixWord ++ tailWord_849410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849421 : List Nat := [1, 7, 1, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_849421 : Nat := 118140960795 + 849421 * 2 ^ 59
def prefixEnd_849421 : Nat := 4983230072969 + 3 ^ 40 * 849421 * 2
def baseEnd_849421 : Nat := 436161251022826370131091

theorem tailTrace_849421 : CollatzResearch.WordTrace tailWord_849421 prefixEnd_849421 436161251022826370131091 := by
  unfold tailWord_849421
  simp only [CollatzResearch.WordTrace]
  refine ⟨30980929055700261402332117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20653952703800174268221411 30980929055700261402332117)
  ·
    refine ⟨726115524742974876617159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30980929055700261402332117 726115524742974876617159)
    ·
      refine ⟨1089173287114462314925739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726115524742974876617159 1089173287114462314925739)
      ·
        refine ⟨1633759930671693472388609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089173287114462314925739 1633759930671693472388609)
        ·
          refine ⟨1225319948003770104291457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633759930671693472388609 1225319948003770104291457)
          ·
            refine ⟨918989961002827578218593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225319948003770104291457 918989961002827578218593)
            ·
              refine ⟨689242470752120683663945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918989961002827578218593 689242470752120683663945)
              ·
                refine ⟨516931853064090512747959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689242470752120683663945 516931853064090512747959)
                ·
                  refine ⟨775397779596135769121939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516931853064090512747959 775397779596135769121939)
                  ·
                    refine ⟨1163096669394203653682909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 775397779596135769121939 1163096669394203653682909)
                    ·
                      refine ⟨436161251022826370131091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163096669394203653682909 436161251022826370131091)
                      ·
                        rfl

theorem cell23_849421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_849421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849421 prefixEnd_849421 := by exact prefixLift 849421
  have htrace : WordTrace (prefixWord ++ tailWord_849421) baseStart_849421 baseEnd_849421 := by
    simpa [prefixWord, tailWord_849421, baseEnd_849421] using wordTrace_append hprefix tailTrace_849421
  have hstable : (prefixWord ++ tailWord_849421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849421).length < 2 ^ (prefixWord ++ tailWord_849421).sum := by decide
  have hdescent : baseEnd_849421 < baseStart_849421 := by decide
  rcases family_descends (prefixWord ++ tailWord_849421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849427 : List Nat := [1, 1, 1, 2, 1, 8, 2, 2, 1, 2, 2]
def baseStart_849427 : Nat := 118140960795 + 849427 * 2 ^ 59
def prefixEnd_849427 : Nat := 4983230072969 + 3 ^ 40 * 849427 * 2
def baseEnd_849427 : Nat := 436164331906753346656063

theorem tailTrace_849427 : CollatzResearch.WordTrace tailWord_849427 prefixEnd_849427 436164331906753346656063 := by
  unfold tailWord_849427
  simp only [CollatzResearch.WordTrace]
  refine ⟨30981147893678524427050535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20654098595785682951367023 30981147893678524427050535)
  ·
    refine ⟨46471721840517786640575803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30981147893678524427050535 46471721840517786640575803)
    ·
      refine ⟨69707582760776679960863705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46471721840517786640575803 69707582760776679960863705)
      ·
        refine ⟨52280687070582509970647779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69707582760776679960863705 52280687070582509970647779)
        ·
          refine ⟨78421030605873764955971669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52280687070582509970647779 78421030605873764955971669)
          ·
            refine ⟨918996452412583183077793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 78421030605873764955971669 918996452412583183077793)
            ·
              refine ⟨689247339309437387308345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918996452412583183077793 689247339309437387308345)
              ·
                refine ⟨516935504482078040481259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689247339309437387308345 516935504482078040481259)
                ·
                  refine ⟨775403256723117060721889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516935504482078040481259 775403256723117060721889)
                  ·
                    refine ⟨581552442542337795541417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 775403256723117060721889 581552442542337795541417)
                    ·
                      refine ⟨436164331906753346656063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581552442542337795541417 436164331906753346656063)
                      ·
                        rfl

theorem cell23_849427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 2, 2].length) (baseStart_849427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849427 prefixEnd_849427 := by exact prefixLift 849427
  have htrace : WordTrace (prefixWord ++ tailWord_849427) baseStart_849427 baseEnd_849427 := by
    simpa [prefixWord, tailWord_849427, baseEnd_849427] using wordTrace_append hprefix tailTrace_849427
  have hstable : (prefixWord ++ tailWord_849427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849427).length < 2 ^ (prefixWord ++ tailWord_849427).sum := by decide
  have hdescent : baseEnd_849427 < baseStart_849427 := by decide
  rcases family_descends (prefixWord ++ tailWord_849427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849436 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_849436 : Nat := 118140960795 + 849436 * 2 ^ 59
def prefixEnd_849436 : Nat := 4983230072969 + 3 ^ 40 * 849436 * 2
def baseEnd_849436 : Nat := 436168953232643811443521

theorem tailTrace_849436 : CollatzResearch.WordTrace tailWord_849436 prefixEnd_849436 436168953232643811443521 := by
  unfold tailWord_849436
  simp only [CollatzResearch.WordTrace]
  refine ⟨15490738075322959482064081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20654317433763945976085441 15490738075322959482064081)
  ·
    refine ⟨11618053556492219611548061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15490738075322959482064081 11618053556492219611548061)
    ·
      refine ⟨4356770083684582354330523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11618053556492219611548061 4356770083684582354330523)
      ·
        refine ⟨6535155125526873531495785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356770083684582354330523 6535155125526873531495785)
        ·
          refine ⟨4901366344145155148621839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6535155125526873531495785 4901366344145155148621839)
          ·
            refine ⟨7352049516217732722932759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901366344145155148621839 7352049516217732722932759)
            ·
              refine ⟨11028074274326599084399139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352049516217732722932759 11028074274326599084399139)
              ·
                refine ⟨16542111411489898626598709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11028074274326599084399139 16542111411489898626598709)
                ·
                  refine ⟨1550822944827177996243629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16542111411489898626598709 1550822944827177996243629)
                  ·
                    refine ⟨581558604310191748591361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550822944827177996243629 581558604310191748591361)
                    ·
                      refine ⟨436168953232643811443521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581558604310191748591361 436168953232643811443521)
                      ·
                        rfl

theorem cell23_849436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_849436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849436 prefixEnd_849436 := by exact prefixLift 849436
  have htrace : WordTrace (prefixWord ++ tailWord_849436) baseStart_849436 baseEnd_849436 := by
    simpa [prefixWord, tailWord_849436, baseEnd_849436] using wordTrace_append hprefix tailTrace_849436
  have hstable : (prefixWord ++ tailWord_849436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849436).length < 2 ^ (prefixWord ++ tailWord_849436).sum := by decide
  have hdescent : baseEnd_849436 < baseStart_849436 := by decide
  rcases family_descends (prefixWord ++ tailWord_849436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849466 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2]
def baseStart_849466 : Nat := 118140960795 + 849466 * 2 ^ 59
def prefixEnd_849466 : Nat := 4983230072969 + 3 ^ 40 * 849466 * 2
def baseEnd_849466 : Nat := 436184357652278694068383

theorem tailTrace_849466 : CollatzResearch.WordTrace tailWord_849466 prefixEnd_849466 436184357652278694068383 := by
  unfold tailWord_849466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7745642585134308521930063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20655046893691489391813501 7745642585134308521930063)
  ·
    refine ⟨11618463877701462782895095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7745642585134308521930063 11618463877701462782895095)
    ·
      refine ⟨17427695816552194174342643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11618463877701462782895095 17427695816552194174342643)
      ·
        refine ⟨26141543724828291261513965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17427695816552194174342643 26141543724828291261513965)
        ·
          refine ⟨9803078896810609223067737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26141543724828291261513965 9803078896810609223067737)
          ·
            refine ⟨7352309172607956917300803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9803078896810609223067737 7352309172607956917300803)
            ·
              refine ⟨11028463758911935375951205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352309172607956917300803 11028463758911935375951205)
              ·
                refine ⟨2067836954795987882990851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11028463758911935375951205 2067836954795987882990851)
                ·
                  refine ⟨3101755432193981824486277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067836954795987882990851 3101755432193981824486277)
                  ·
                    refine ⟨581579143536371592091177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3101755432193981824486277 581579143536371592091177)
                    ·
                      refine ⟨436184357652278694068383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581579143536371592091177 436184357652278694068383)
                      ·
                        rfl

theorem cell23_849466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_849466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849466 prefixEnd_849466 := by exact prefixLift 849466
  have htrace : WordTrace (prefixWord ++ tailWord_849466) baseStart_849466 baseEnd_849466 := by
    simpa [prefixWord, tailWord_849466, baseEnd_849466] using wordTrace_append hprefix tailTrace_849466
  have hstable : (prefixWord ++ tailWord_849466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849466).length < 2 ^ (prefixWord ++ tailWord_849466).sum := by decide
  have hdescent : baseEnd_849466 < baseStart_849466 := by decide
  rcases family_descends (prefixWord ++ tailWord_849466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849472 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 11]
def baseStart_849472 : Nat := 118140960795 + 849472 * 2 ^ 59
def prefixEnd_849472 : Nat := 4983230072969 + 3 ^ 40 * 849472 * 2
def baseEnd_849472 : Nat := 48465270948467296732595

theorem tailTrace_849472 : CollatzResearch.WordTrace tailWord_849472 prefixEnd_849472 48465270948467296732595 := by
  unfold tailWord_849472
  simp only [CollatzResearch.WordTrace]
  refine ⟨15491394589257748556219335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20655192785676998074959113 15491394589257748556219335)
  ·
    refine ⟨23237091883886622834329003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15491394589257748556219335 23237091883886622834329003)
    ·
      refine ⟨34855637825829934251493505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23237091883886622834329003 34855637825829934251493505)
      ·
        refine ⟨26141728369372450688620129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34855637825829934251493505 26141728369372450688620129)
        ·
          refine ⟨19606296277029338016465097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26141728369372450688620129 19606296277029338016465097)
          ·
            refine ⟨14704722207772003512348823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19606296277029338016465097 14704722207772003512348823)
            ·
              refine ⟨22057083311658005268523235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14704722207772003512348823 22057083311658005268523235)
              ·
                refine ⟨33085624967487007902784853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22057083311658005268523235 33085624967487007902784853)
                ·
                  refine ⟨48465270948467296732595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 33085624967487007902784853 48465270948467296732595)
                  ·
                    rfl

theorem cell23_849472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 11].length) (baseStart_849472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849472 prefixEnd_849472 := by exact prefixLift 849472
  have htrace : WordTrace (prefixWord ++ tailWord_849472) baseStart_849472 baseEnd_849472 := by
    simpa [prefixWord, tailWord_849472, baseEnd_849472] using wordTrace_append hprefix tailTrace_849472
  have hstable : (prefixWord ++ tailWord_849472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849472).length < 2 ^ (prefixWord ++ tailWord_849472).sum := by decide
  have hdescent : baseEnd_849472 < baseStart_849472 := by decide
  rcases family_descends (prefixWord ++ tailWord_849472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849489 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 7]
def baseStart_849489 : Nat := 118140960795 + 849489 * 2 ^ 59
def prefixEnd_849489 : Nat := 4983230072969 + 3 ^ 40 * 849489 * 2
def baseEnd_849489 : Nat := 48466240856370233786753

theorem tailTrace_849489 : CollatzResearch.WordTrace tailWord_849489 prefixEnd_849489 48466240856370233786753 := by
  unfold tailWord_849489
  simp only [CollatzResearch.WordTrace]
  refine ⟨30983409219453909015807521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20655606146302606010538347 30983409219453909015807521)
  ·
    refine ⟨23237556914590431761855641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30983409219453909015807521 23237556914590431761855641)
    ·
      refine ⟨17428167685942823821391731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23237556914590431761855641 17428167685942823821391731)
      ·
        refine ⟨26142251528914235732087597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17428167685942823821391731 26142251528914235732087597)
        ·
          refine ⟨9803344323342838399532849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26142251528914235732087597 9803344323342838399532849)
          ·
            refine ⟨7352508242507128799649637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9803344323342838399532849 7352508242507128799649637)
            ·
              refine ⟨1378595295470086649934307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7352508242507128799649637 1378595295470086649934307)
              ·
                refine ⟨2067892943205129974901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378595295470086649934307 2067892943205129974901461)
                ·
                  refine ⟨48466240856370233786753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2067892943205129974901461 48466240856370233786753)
                  ·
                    rfl

theorem cell23_849489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 7].length) (baseStart_849489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849489 prefixEnd_849489 := by exact prefixLift 849489
  have htrace : WordTrace (prefixWord ++ tailWord_849489) baseStart_849489 baseEnd_849489 := by
    simpa [prefixWord, tailWord_849489, baseEnd_849489] using wordTrace_append hprefix tailTrace_849489
  have hstable : (prefixWord ++ tailWord_849489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849489).length < 2 ^ (prefixWord ++ tailWord_849489).sum := by decide
  have hdescent : baseEnd_849489 < baseStart_849489 := by decide
  rcases family_descends (prefixWord ++ tailWord_849489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849494 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_849494 : Nat := 118140960795 + 849494 * 2 ^ 59
def prefixEnd_849494 : Nat := 4983230072969 + 3 ^ 40 * 849494 * 2
def baseEnd_849494 : Nat := 436198735110604584518255

theorem tailTrace_849494 : CollatzResearch.WordTrace tailWord_849494 prefixEnd_849494 436198735110604584518255 := by
  unfold tailWord_849494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936474474027237179358721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20655727722957196579826357 1936474474027237179358721)
  ·
    refine ⟨1452355855520427884519041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1936474474027237179358721 1452355855520427884519041)
    ·
      refine ⟨1089266891640320913389281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1452355855520427884519041 1089266891640320913389281)
      ·
        refine ⟨816950168730240685041961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089266891640320913389281 816950168730240685041961)
        ·
          refine ⟨612712626547680513781471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816950168730240685041961 612712626547680513781471)
          ·
            refine ⟨919068939821520770672207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612712626547680513781471 919068939821520770672207)
            ·
              refine ⟨1378603409732281156008311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919068939821520770672207 1378603409732281156008311)
              ·
                refine ⟨2067905114598421734012467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378603409732281156008311 2067905114598421734012467)
                ·
                  refine ⟨3101857671897632601018701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067905114598421734012467 3101857671897632601018701)
                  ·
                    refine ⟨1163196626961612225382013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101857671897632601018701 1163196626961612225382013)
                    ·
                      refine ⟨436198735110604584518255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163196626961612225382013 436198735110604584518255)
                      ·
                        rfl

theorem cell23_849494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_849494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849494 prefixEnd_849494 := by exact prefixLift 849494
  have htrace : WordTrace (prefixWord ++ tailWord_849494) baseStart_849494 baseEnd_849494 := by
    simpa [prefixWord, tailWord_849494, baseEnd_849494] using wordTrace_append hprefix tailTrace_849494
  have hstable : (prefixWord ++ tailWord_849494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849494).length < 2 ^ (prefixWord ++ tailWord_849494).sum := by decide
  have hdescent : baseEnd_849494 < baseStart_849494 := by decide
  rcases family_descends (prefixWord ++ tailWord_849494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849500 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_849500 : Nat := 118140960795 + 849500 * 2 ^ 59
def prefixEnd_849500 : Nat := 4983230072969 + 3 ^ 40 * 849500 * 2
def baseEnd_849500 : Nat := 436201815994531561043227

theorem tailTrace_849500 : CollatzResearch.WordTrace tailWord_849500 prefixEnd_849500 436201815994531561043227 := by
  unfold tailWord_849500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15491905211207028947228977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20655873614942705262971969 15491905211207028947228977)
  ·
    refine ⟨11618928908405271710421733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15491905211207028947228977 11618928908405271710421733)
    ·
      refine ⟨2178549170325988445704075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11618928908405271710421733 2178549170325988445704075)
      ·
        refine ⟨3267823755488982668556113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178549170325988445704075 3267823755488982668556113)
        ·
          refine ⟨2450867816616737001417085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3267823755488982668556113 2450867816616737001417085)
          ·
            refine ⟨919075431231276375531407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2450867816616737001417085 919075431231276375531407)
            ·
              refine ⟨1378613146846914563297111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919075431231276375531407 1378613146846914563297111)
              ·
                refine ⟨2067919720270371844945667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378613146846914563297111 2067919720270371844945667)
                ·
                  refine ⟨3101879580405557767418501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067919720270371844945667 3101879580405557767418501)
                  ·
                    refine ⟨581602421326042081390969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3101879580405557767418501 581602421326042081390969)
                    ·
                      refine ⟨436201815994531561043227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581602421326042081390969 436201815994531561043227)
                      ·
                        rfl

theorem cell23_849500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_849500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849500 prefixEnd_849500 := by exact prefixLift 849500
  have htrace : WordTrace (prefixWord ++ tailWord_849500) baseStart_849500 baseEnd_849500 := by
    simpa [prefixWord, tailWord_849500, baseEnd_849500] using wordTrace_append hprefix tailTrace_849500
  have hstable : (prefixWord ++ tailWord_849500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849500).length < 2 ^ (prefixWord ++ tailWord_849500).sum := by decide
  have hdescent : baseEnd_849500 < baseStart_849500 := by decide
  rcases family_descends (prefixWord ++ tailWord_849500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849519 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 2, 5]
def baseStart_849519 : Nat := 118140960795 + 849519 * 2 ^ 59
def prefixEnd_849519 : Nat := 4983230072969 + 3 ^ 40 * 849519 * 2
def baseEnd_849519 : Nat := 145403857375655662235213

theorem tailTrace_849519 : CollatzResearch.WordTrace tailWord_849519 prefixEnd_849519 145403857375655662235213 := by
  unfold tailWord_849519
  simp only [CollatzResearch.WordTrace]
  refine ⟨30984503409345224139399611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20656335606230149426266407 30984503409345224139399611)
  ·
    refine ⟨46476755114017836209099417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30984503409345224139399611 46476755114017836209099417)
    ·
      refine ⟨34857566335513377156824563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46476755114017836209099417 34857566335513377156824563)
      ·
        refine ⟨52286349503270065735236845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34857566335513377156824563 52286349503270065735236845)
        ·
          refine ⟨19607381063726274650713817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52286349503270065735236845 19607381063726274650713817)
          ·
            refine ⟨14705535797794705988035363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19607381063726274650713817 14705535797794705988035363)
            ·
              refine ⟨22058303696692058982053045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14705535797794705988035363 22058303696692058982053045)
              ·
                refine ⟨2067965971564880529567473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22058303696692058982053045 2067965971564880529567473)
                ·
                  refine ⟨1550974478673660397175605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2067965971564880529567473 1550974478673660397175605)
                  ·
                    refine ⟨145403857375655662235213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1550974478673660397175605 145403857375655662235213)
                    ·
                      rfl

theorem cell23_849519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_849519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849519 prefixEnd_849519 := by exact prefixLift 849519
  have htrace : WordTrace (prefixWord ++ tailWord_849519) baseStart_849519 baseEnd_849519 := by
    simpa [prefixWord, tailWord_849519, baseEnd_849519] using wordTrace_append hprefix tailTrace_849519
  have hstable : (prefixWord ++ tailWord_849519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849519).length < 2 ^ (prefixWord ++ tailWord_849519).sum := by decide
  have hdescent : baseEnd_849519 < baseStart_849519 := by decide
  rcases family_descends (prefixWord ++ tailWord_849519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849529 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_849529 : Nat := 118140960795 + 849529 * 2 ^ 59
def prefixEnd_849529 : Nat := 4983230072969 + 3 ^ 40 * 849529 * 2
def baseEnd_849529 : Nat := 436216706933511947580593

theorem tailTrace_849529 : CollatzResearch.WordTrace tailWord_849529 prefixEnd_849529 436216706933511947580593 := by
  unfold tailWord_849529
  simp only [CollatzResearch.WordTrace]
  refine ⟨30984868139308995847263641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20656578759539330564842427 30984868139308995847263641)
  ·
    refine ⟨23238651104481746885447731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30984868139308995847263641 23238651104481746885447731)
    ·
      refine ⟨34857976656722620328171597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23238651104481746885447731 34857976656722620328171597)
      ·
        refine ⟨13071741246270982623064349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34857976656722620328171597 13071741246270982623064349)
        ·
          refine ⟨4901902967351618483649131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13071741246270982623064349 4901902967351618483649131)
          ·
            refine ⟨7352854451027427725473697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901902967351618483649131 7352854451027427725473697)
            ·
              refine ⟨5514640838270570794105273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7352854451027427725473697 5514640838270570794105273)
              ·
                refine ⟨4135980628702928095578955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5514640838270570794105273 4135980628702928095578955)
                ·
                  refine ⟨6203970943054392143368433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135980628702928095578955 6203970943054392143368433)
                  ·
                    refine ⟨4652978207290794107526325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203970943054392143368433 4652978207290794107526325)
                    ·
                      refine ⟨436216706933511947580593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4652978207290794107526325 436216706933511947580593)
                      ·
                        rfl

theorem cell23_849529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_849529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849529 prefixEnd_849529 := by exact prefixLift 849529
  have htrace : WordTrace (prefixWord ++ tailWord_849529) baseStart_849529 baseEnd_849529 := by
    simpa [prefixWord, tailWord_849529, baseEnd_849529] using wordTrace_append hprefix tailTrace_849529
  have hstable : (prefixWord ++ tailWord_849529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849529).length < 2 ^ (prefixWord ++ tailWord_849529).sum := by decide
  have hdescent : baseEnd_849529 < baseStart_849529 := by decide
  rcases family_descends (prefixWord ++ tailWord_849529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849540 : List Nat := [2, 3, 2, 1, 4, 1, 3, 2, 5]
def baseStart_849540 : Nat := 118140960795 + 849540 * 2 ^ 59
def prefixEnd_849540 : Nat := 4983230072969 + 3 ^ 40 * 849540 * 2
def baseEnd_849540 : Nat := 48469150580079044949227

theorem tailTrace_849540 : CollatzResearch.WordTrace tailWord_849540 prefixEnd_849540 48469150580079044949227 := by
  unfold tailWord_849540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15492634671134572362957037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20656846228179429817276049 15492634671134572362957037)
  ·
    refine ⟨5809738001675464636108889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15492634671134572362957037 5809738001675464636108889)
    ·
      refine ⟨4357303501256598477081667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5809738001675464636108889 4357303501256598477081667)
      ·
        refine ⟨6535955251884897715622501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4357303501256598477081667 6535955251884897715622501)
        ·
          refine ⟨1225491609728418321679219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6535955251884897715622501 1225491609728418321679219)
          ·
            refine ⟨1838237414592627482518829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225491609728418321679219 1838237414592627482518829)
            ·
              refine ⟨689339030472235305944561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1838237414592627482518829 689339030472235305944561)
              ·
                refine ⟨517004272854176479458421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689339030472235305944561 517004272854176479458421)
                ·
                  refine ⟨48469150580079044949227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517004272854176479458421 48469150580079044949227)
                  ·
                    rfl

theorem cell23_849540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_849540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849540 prefixEnd_849540 := by exact prefixLift 849540
  have htrace : WordTrace (prefixWord ++ tailWord_849540) baseStart_849540 baseEnd_849540 := by
    simpa [prefixWord, tailWord_849540, baseEnd_849540] using wordTrace_append hprefix tailTrace_849540
  have hstable : (prefixWord ++ tailWord_849540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849540).length < 2 ^ (prefixWord ++ tailWord_849540).sum := by decide
  have hdescent : baseEnd_849540 < baseStart_849540 := by decide
  rcases family_descends (prefixWord ++ tailWord_849540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849546 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_849546 : Nat := 118140960795 + 849546 * 2 ^ 59
def prefixEnd_849546 : Nat := 4983230072969 + 3 ^ 40 * 849546 * 2
def baseEnd_849546 : Nat := 436225436104638381068015

theorem tailTrace_849546 : CollatzResearch.WordTrace tailWord_849546 prefixEnd_849546 436225436104638381068015 := by
  unfold tailWord_849546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7746372045061851937658123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20656992120164938500421661 7746372045061851937658123)
  ·
    refine ⟨11619558067592777906487185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7746372045061851937658123 11619558067592777906487185)
    ·
      refine ⟨8714668550694583429865389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11619558067592777906487185 8714668550694583429865389)
      ·
        refine ⟨3268000706510468786199521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8714668550694583429865389 3268000706510468786199521)
        ·
          refine ⟨2451000529882851589649641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3268000706510468786199521 2451000529882851589649641)
          ·
            refine ⟨1838250397412138692237231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451000529882851589649641 1838250397412138692237231)
            ·
              refine ⟨2757375596118208038355847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838250397412138692237231 2757375596118208038355847)
              ·
                refine ⟨4136063394177312057533771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757375596118208038355847 4136063394177312057533771)
                ·
                  refine ⟨6204095091265968086300657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136063394177312057533771 6204095091265968086300657)
                  ·
                    refine ⟨4653071318449476064725493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204095091265968086300657 4653071318449476064725493)
                    ·
                      refine ⟨436225436104638381068015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4653071318449476064725493 436225436104638381068015)
                      ·
                        rfl

theorem cell23_849546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_849546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849546 prefixEnd_849546 := by exact prefixLift 849546
  have htrace : WordTrace (prefixWord ++ tailWord_849546) baseStart_849546 baseEnd_849546 := by
    simpa [prefixWord, tailWord_849546, baseEnd_849546] using wordTrace_append hprefix tailTrace_849546
  have hstable : (prefixWord ++ tailWord_849546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849546).length < 2 ^ (prefixWord ++ tailWord_849546).sum := by decide
  have hdescent : baseEnd_849546 < baseStart_849546 := by decide
  rcases family_descends (prefixWord ++ tailWord_849546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849570 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_849570 : Nat := 118140960795 + 849570 * 2 ^ 59
def prefixEnd_849570 : Nat := 4983230072969 + 3 ^ 40 * 849570 * 2
def baseEnd_849570 : Nat := 145412586546782095722635

theorem tailTrace_849570 : CollatzResearch.WordTrace tailWord_849570 prefixEnd_849570 145412586546782095722635 := by
  unfold tailWord_849570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7746590883040114962376541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20657575688106973233004109 7746590883040114962376541)
  ·
    refine ⟨2904971581140043110891203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7746590883040114962376541 2904971581140043110891203)
    ·
      refine ⟨4357457371710064666336805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904971581140043110891203 4357457371710064666336805)
      ·
        refine ⟨817023257195637124938151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4357457371710064666336805 817023257195637124938151)
        ·
          refine ⟨1225534885793455687407227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817023257195637124938151 1225534885793455687407227)
          ·
            refine ⟨1838302328690183531110841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225534885793455687407227 1838302328690183531110841)
            ·
              refine ⟨1378726746517637648333131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838302328690183531110841 1378726746517637648333131)
              ·
                refine ⟨2068090119776456472499697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378726746517637648333131 2068090119776456472499697)
                ·
                  refine ⟨1551067589832342354374773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2068090119776456472499697 1551067589832342354374773)
                  ·
                    refine ⟨145412586546782095722635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1551067589832342354374773 145412586546782095722635)
                    ·
                      rfl

theorem cell23_849570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_849570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849570 prefixEnd_849570 := by exact prefixLift 849570
  have htrace : WordTrace (prefixWord ++ tailWord_849570) baseStart_849570 baseEnd_849570 := by
    simpa [prefixWord, tailWord_849570, baseEnd_849570] using wordTrace_append hprefix tailTrace_849570
  have hstable : (prefixWord ++ tailWord_849570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849570).length < 2 ^ (prefixWord ++ tailWord_849570).sum := by decide
  have hdescent : baseEnd_849570 < baseStart_849570 := by decide
  rcases family_descends (prefixWord ++ tailWord_849570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849583 : List Nat := [1, 1, 2, 1, 2, 4, 2, 5, 1, 4]
def baseStart_849583 : Nat := 118140960795 + 849583 * 2 ^ 59
def prefixEnd_849583 : Nat := 4983230072969 + 3 ^ 40 * 849583 * 2
def baseEnd_849583 : Nat := 145414811629618245435115

theorem tailTrace_849583 : CollatzResearch.WordTrace tailWord_849583 prefixEnd_849583 145414811629618245435115 := by
  unfold tailWord_849583
  simp only [CollatzResearch.WordTrace]
  refine ⟨30986837681113363069729403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20657891787408908713152935 30986837681113363069729403)
  ·
    refine ⟨46480256521670044604594105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30986837681113363069729403 46480256521670044604594105)
    ·
      refine ⟨34860192391252533453445579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46480256521670044604594105 34860192391252533453445579)
      ·
        refine ⟨52290288586878800180168369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34860192391252533453445579 52290288586878800180168369)
        ·
          refine ⟨39217716440159100135126277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52290288586878800180168369 39217716440159100135126277)
          ·
            refine ⟨7353321832529831275336177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39217716440159100135126277 7353321832529831275336177)
            ·
              refine ⟨5514991374397373456502133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7353321832529831275336177 5514991374397373456502133)
              ·
                refine ⟨517030441349753761547075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5514991374397373456502133 517030441349753761547075)
                ·
                  refine ⟨775545662024630642320613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517030441349753761547075 775545662024630642320613)
                  ·
                    refine ⟨145414811629618245435115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 775545662024630642320613 145414811629618245435115)
                    ·
                      rfl

theorem cell23_849583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 1, 4].length) (baseStart_849583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849583 prefixEnd_849583 := by exact prefixLift 849583
  have htrace : WordTrace (prefixWord ++ tailWord_849583) baseStart_849583 baseEnd_849583 := by
    simpa [prefixWord, tailWord_849583, baseEnd_849583] using wordTrace_append hprefix tailTrace_849583
  have hstable : (prefixWord ++ tailWord_849583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849583).length < 2 ^ (prefixWord ++ tailWord_849583).sum := by decide
  have hdescent : baseEnd_849583 < baseStart_849583 := by decide
  rcases family_descends (prefixWord ++ tailWord_849583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849590 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_849590 : Nat := 118140960795 + 849590 * 2 ^ 59
def prefixEnd_849590 : Nat := 4983230072969 + 3 ^ 40 * 849590 * 2
def baseEnd_849590 : Nat := 436248029253436208917813

theorem tailTrace_849590 : CollatzResearch.WordTrace tailWord_849590 prefixEnd_849590 436248029253436208917813 := by
  unfold tailWord_849590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936693312005500204077139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20658061994725335510156149 1936693312005500204077139)
  ·
    refine ⟨2905039968008250306115709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1936693312005500204077139 2905039968008250306115709)
    ·
      refine ⟨1089389988003093864793391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2905039968008250306115709 1089389988003093864793391)
      ·
        refine ⟨1634084982004640797190087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089389988003093864793391 1634084982004640797190087)
        ·
          refine ⟨2451127473006961195785131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634084982004640797190087 2451127473006961195785131)
          ·
            refine ⟨3676691209510441793677697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451127473006961195785131 3676691209510441793677697)
            ·
              refine ⟨2757518407132831345258273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676691209510441793677697 2757518407132831345258273)
              ·
                refine ⟨2068138805349623508943705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757518407132831345258273 2068138805349623508943705)
                ·
                  refine ⟨1551104104012217631707779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2068138805349623508943705 1551104104012217631707779)
                  ·
                    refine ⟨2326656156018326447561669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1551104104012217631707779 2326656156018326447561669)
                    ·
                      refine ⟨436248029253436208917813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2326656156018326447561669 436248029253436208917813)
                      ·
                        rfl

theorem cell23_849590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_849590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849590 prefixEnd_849590 := by exact prefixLift 849590
  have htrace : WordTrace (prefixWord ++ tailWord_849590) baseStart_849590 baseEnd_849590 := by
    simpa [prefixWord, tailWord_849590, baseEnd_849590] using wordTrace_append hprefix tailTrace_849590
  have hstable : (prefixWord ++ tailWord_849590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849590).length < 2 ^ (prefixWord ++ tailWord_849590).sum := by decide
  have hdescent : baseEnd_849590 < baseStart_849590 := by decide
  rcases family_descends (prefixWord ++ tailWord_849590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849596 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 6]
def baseStart_849596 : Nat := 118140960795 + 849596 * 2 ^ 59
def prefixEnd_849596 : Nat := 4983230072969 + 3 ^ 40 * 849596 * 2
def baseEnd_849596 : Nat := 48472345570818131715865

theorem tailTrace_849596 : CollatzResearch.WordTrace tailWord_849596 prefixEnd_849596 48472345570818131715865 := by
  unfold tailWord_849596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493655915033133144976321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20658207886710844193301761 15493655915033133144976321)
  ·
    refine ⟨11620241936274849858732241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15493655915033133144976321 11620241936274849858732241)
    ·
      refine ⟨8715181452206137394049181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11620241936274849858732241 8715181452206137394049181)
      ·
        refine ⟨3268193044577301522768443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8715181452206137394049181 3268193044577301522768443)
        ·
          refine ⟨4902289566865952284152665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268193044577301522768443 4902289566865952284152665)
          ·
            refine ⟨3676717175149464213114499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4902289566865952284152665 3676717175149464213114499)
            ·
              refine ⟨5515075762724196319671749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3676717175149464213114499 5515075762724196319671749)
              ·
                refine ⟨1034076705510786809938453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5515075762724196319671749 1034076705510786809938453)
                ·
                  refine ⟨48472345570818131715865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1034076705510786809938453 48472345570818131715865)
                  ·
                    rfl

theorem cell23_849596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_849596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849596 prefixEnd_849596 := by exact prefixLift 849596
  have htrace : WordTrace (prefixWord ++ tailWord_849596) baseStart_849596 baseEnd_849596 := by
    simpa [prefixWord, tailWord_849596, baseEnd_849596] using wordTrace_append hprefix tailTrace_849596
  have hstable : (prefixWord ++ tailWord_849596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849596).length < 2 ^ (prefixWord ++ tailWord_849596).sum := by decide
  have hdescent : baseEnd_849596 < baseStart_849596 := by decide
  rcases family_descends (prefixWord ++ tailWord_849596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849599 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_849599 : Nat := 118140960795 + 849599 * 2 ^ 59
def prefixEnd_849599 : Nat := 4983230072969 + 3 ^ 40 * 849599 * 2
def baseEnd_849599 : Nat := 436252650579326673705271

theorem tailTrace_849599 : CollatzResearch.WordTrace tailWord_849599 prefixEnd_849599 436252650579326673705271 := by
  unfold tailWord_849599
  simp only [CollatzResearch.WordTrace]
  refine ⟨30987421249055397802311851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20658280832703598534874567 30987421249055397802311851)
  ·
    refine ⟨46481131873583096703467777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30987421249055397802311851 46481131873583096703467777)
    ·
      refine ⟨34860848905187322527600833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46481131873583096703467777 34860848905187322527600833)
      ·
        refine ⟨26145636678890491895700625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34860848905187322527600833 26145636678890491895700625)
        ·
          refine ⟨19609227509167868921775469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26145636678890491895700625 19609227509167868921775469)
          ·
            refine ⟨7353460315937950845665801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19609227509167868921775469 7353460315937950845665801)
            ·
              refine ⟨5515095236953463134249351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7353460315937950845665801 5515095236953463134249351)
              ·
                refine ⟨8272642855430194701374027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5515095236953463134249351 8272642855430194701374027)
                ·
                  refine ⟨12408964283145292052061041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8272642855430194701374027 12408964283145292052061041)
                  ·
                    refine ⟨9306723212358969039045781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12408964283145292052061041 9306723212358969039045781)
                    ·
                      refine ⟨436252650579326673705271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9306723212358969039045781 436252650579326673705271)
                      ·
                        rfl

theorem cell23_849599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_849599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849599 prefixEnd_849599 := by exact prefixLift 849599
  have htrace : WordTrace (prefixWord ++ tailWord_849599) baseStart_849599 baseEnd_849599 := by
    simpa [prefixWord, tailWord_849599, baseEnd_849599] using wordTrace_append hprefix tailTrace_849599
  have hstable : (prefixWord ++ tailWord_849599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849599).length < 2 ^ (prefixWord ++ tailWord_849599).sum := by decide
  have hdescent : baseEnd_849599 < baseStart_849599 := by decide
  rcases family_descends (prefixWord ++ tailWord_849599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849623 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_849623 : Nat := 118140960795 + 849623 * 2 ^ 59
def prefixEnd_849623 : Nat := 4983230072969 + 3 ^ 40 * 849623 * 2
def baseEnd_849623 : Nat := 436264974115034579805161

theorem tailTrace_849623 : CollatzResearch.WordTrace tailWord_849623 prefixEnd_849623 436264974115034579805161 := by
  unfold tailWord_849623
  simp only [CollatzResearch.WordTrace]
  refine ⟨30988296600968449901185523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20658864400645633267457015 30988296600968449901185523)
  ·
    refine ⟨46482444901452674851778285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30988296600968449901185523 46482444901452674851778285)
    ·
      refine ⟨17430916838044753069416857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46482444901452674851778285 17430916838044753069416857)
      ·
        refine ⟨13073187628533564802062643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17430916838044753069416857 13073187628533564802062643)
        ·
          refine ⟨19609781442800347203093965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13073187628533564802062643 19609781442800347203093965)
          ·
            refine ⟨7353668041050130201160237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19609781442800347203093965 7353668041050130201160237)
            ·
              refine ⟨2757625515393798825435089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7353668041050130201160237 2757625515393798825435089)
              ·
                refine ⟨2068219136545349119076317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757625515393798825435089 2068219136545349119076317)
                ·
                  refine ⟨775582176204505919653619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2068219136545349119076317 775582176204505919653619)
                  ·
                    refine ⟨1163373264306758879480429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 775582176204505919653619 1163373264306758879480429)
                    ·
                      refine ⟨436264974115034579805161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163373264306758879480429 436264974115034579805161)
                      ·
                        rfl

theorem cell23_849623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_849623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849623 prefixEnd_849623 := by exact prefixLift 849623
  have htrace : WordTrace (prefixWord ++ tailWord_849623) baseStart_849623 baseEnd_849623 := by
    simpa [prefixWord, tailWord_849623, baseEnd_849623] using wordTrace_append hprefix tailTrace_849623
  have hstable : (prefixWord ++ tailWord_849623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849623).length < 2 ^ (prefixWord ++ tailWord_849623).sum := by decide
  have hdescent : baseEnd_849623 < baseStart_849623 := by decide
  rcases family_descends (prefixWord ++ tailWord_849623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849626 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_849626 : Nat := 118140960795 + 849626 * 2 ^ 59
def prefixEnd_849626 : Nat := 4983230072969 + 3 ^ 40 * 849626 * 2
def baseEnd_849626 : Nat := 145422171518999356022549

theorem tailTrace_849626 : CollatzResearch.WordTrace tailWord_849626 prefixEnd_849626 145422171518999356022549 := by
  unfold tailWord_849626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7747101504989395353386183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20658937346638387609029821 7747101504989395353386183)
  ·
    refine ⟨11620652257484093030079275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7747101504989395353386183 11620652257484093030079275)
    ·
      refine ⟨17430978386226139545118913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11620652257484093030079275 17430978386226139545118913)
      ·
        refine ⟨13073233789669604658839185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17430978386226139545118913 13073233789669604658839185)
        ·
          refine ⟨9804925342252203494129389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13073233789669604658839185 9804925342252203494129389)
          ·
            refine ⟨3676847003344576310298521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9804925342252203494129389 3676847003344576310298521)
            ·
              refine ⟨2757635252508432232723891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676847003344576310298521 2757635252508432232723891)
              ·
                refine ⟨4136452878762648349085837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757635252508432232723891 4136452878762648349085837)
                ·
                  refine ⟨1551169829535993130907189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4136452878762648349085837 1551169829535993130907189)
                  ·
                    refine ⟨145422171518999356022549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1551169829535993130907189 145422171518999356022549)
                    ·
                      rfl

theorem cell23_849626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_849626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849626 prefixEnd_849626 := by exact prefixLift 849626
  have htrace : WordTrace (prefixWord ++ tailWord_849626) baseStart_849626 baseEnd_849626 := by
    simpa [prefixWord, tailWord_849626, baseEnd_849626] using wordTrace_append hprefix tailTrace_849626
  have hstable : (prefixWord ++ tailWord_849626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849626).length < 2 ^ (prefixWord ++ tailWord_849626).sum := by decide
  have hdescent : baseEnd_849626 < baseStart_849626 := by decide
  rcases family_descends (prefixWord ++ tailWord_849626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849643 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 1, 5]
def baseStart_849643 : Nat := 118140960795 + 849643 * 2 ^ 59
def prefixEnd_849643 : Nat := 4983230072969 + 3 ^ 40 * 849643 * 2
def baseEnd_849643 : Nat := 145425081242708167185023

theorem tailTrace_849643 : CollatzResearch.WordTrace tailWord_849643 prefixEnd_849643 145425081242708167185023 := by
  unfold tailWord_849643
  simp only [CollatzResearch.WordTrace]
  refine ⟨30989026060895993316913583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20659350707263995544609055 30989026060895993316913583)
  ·
    refine ⟨46483539091343989975370375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30989026060895993316913583 46483539091343989975370375)
    ·
      refine ⟨69725308637015984963055563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46483539091343989975370375 69725308637015984963055563)
      ·
        refine ⟨104587962955523977444583345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69725308637015984963055563 104587962955523977444583345)
        ·
          refine ⟨78440972216642983083437509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104587962955523977444583345 78440972216642983083437509)
          ·
            refine ⟨14707682290620559328144533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78440972216642983083437509 14707682290620559328144533)
            ·
              refine ⟨689422607372838718506775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14707682290620559328144533 689422607372838718506775)
              ·
                refine ⟨1034133911059258077760163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689422607372838718506775 1034133911059258077760163)
                ·
                  refine ⟨1551200866588887116640245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034133911059258077760163 1551200866588887116640245)
                  ·
                    refine ⟨145425081242708167185023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1551200866588887116640245 145425081242708167185023)
                    ·
                      rfl

theorem cell23_849643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 5].length) (baseStart_849643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849643 prefixEnd_849643 := by exact prefixLift 849643
  have htrace : WordTrace (prefixWord ++ tailWord_849643) baseStart_849643 baseEnd_849643 := by
    simpa [prefixWord, tailWord_849643, baseEnd_849643] using wordTrace_append hprefix tailTrace_849643
  have hstable : (prefixWord ++ tailWord_849643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849643).length < 2 ^ (prefixWord ++ tailWord_849643).sum := by decide
  have hdescent : baseEnd_849643 < baseStart_849643 := by decide
  rcases family_descends (prefixWord ++ tailWord_849643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849700 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_849700 : Nat := 118140960795 + 849700 * 2 ^ 59
def prefixEnd_849700 : Nat := 4983230072969 + 3 ^ 40 * 849700 * 2
def baseEnd_849700 : Nat := 436304512125430778542307

theorem tailTrace_849700 : CollatzResearch.WordTrace tailWord_849700 prefixEnd_849700 436304512125430778542307 := by
  unfold tailWord_849700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15495552510844746025869277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20660736681126328034492369 15495552510844746025869277)
  ·
    refine ⟨5810832191566779759700979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15495552510844746025869277 5810832191566779759700979)
    ·
      refine ⟨8716248287350169639551469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810832191566779759700979 8716248287350169639551469)
      ·
        refine ⟨3268593107756313614831801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8716248287350169639551469 3268593107756313614831801)
        ·
          refine ⟨2451444830817235211123851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3268593107756313614831801 2451444830817235211123851)
          ·
            refine ⟨3677167246225852816685777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451444830817235211123851 3677167246225852816685777)
            ·
              refine ⟨2757875434669389612514333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677167246225852816685777 2757875434669389612514333)
              ·
                refine ⟨1034203288001021104692875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2757875434669389612514333 1034203288001021104692875)
                ·
                  refine ⟨1551304932001531657039313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034203288001021104692875 1551304932001531657039313)
                  ·
                    refine ⟨1163478699001148742779485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1551304932001531657039313 1163478699001148742779485)
                    ·
                      refine ⟨436304512125430778542307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163478699001148742779485 436304512125430778542307)
                      ·
                        rfl

theorem cell23_849700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_849700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849700 prefixEnd_849700 := by exact prefixLift 849700
  have htrace : WordTrace (prefixWord ++ tailWord_849700) baseStart_849700 baseEnd_849700 := by
    simpa [prefixWord, tailWord_849700, baseEnd_849700] using wordTrace_append hprefix tailTrace_849700
  have hstable : (prefixWord ++ tailWord_849700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849700).length < 2 ^ (prefixWord ++ tailWord_849700).sum := by decide
  have hdescent : baseEnd_849700 < baseStart_849700 := by decide
  rcases family_descends (prefixWord ++ tailWord_849700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849734 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_849734 : Nat := 118140960795 + 849734 * 2 ^ 59
def prefixEnd_849734 : Nat := 4983230072969 + 3 ^ 40 * 849734 * 2
def baseEnd_849734 : Nat := 436321970467683645517151

theorem tailTrace_849734 : CollatzResearch.WordTrace tailWord_849734 prefixEnd_849734 436321970467683645517151 := by
  unfold tailWord_849734
  simp only [CollatzResearch.WordTrace]
  refine ⟨968510784486447370577383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20661563402377543905650837 968510784486447370577383)
  ·
    refine ⟨1452766176729671055866075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 968510784486447370577383 1452766176729671055866075)
    ·
      refine ⟨2179149265094506583799113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452766176729671055866075 2179149265094506583799113)
      ·
        refine ⟨1634361948820879937849335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2179149265094506583799113 1634361948820879937849335)
        ·
          refine ⟨2451542923231319906774003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634361948820879937849335 2451542923231319906774003)
          ·
            refine ⟨3677314384846979860161005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451542923231319906774003 3677314384846979860161005)
            ·
              refine ⟨1378992894317617447560377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3677314384846979860161005 1378992894317617447560377)
              ·
                refine ⟨1034244670738213085670283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378992894317617447560377 1034244670738213085670283)
                ·
                  refine ⟨1551367006107319628505425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034244670738213085670283 1551367006107319628505425)
                  ·
                    refine ⟨1163525254580489721379069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1551367006107319628505425 1163525254580489721379069)
                    ·
                      refine ⟨436321970467683645517151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163525254580489721379069 436321970467683645517151)
                      ·
                        rfl

theorem cell23_849734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_849734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849734 prefixEnd_849734 := by exact prefixLift 849734
  have htrace : WordTrace (prefixWord ++ tailWord_849734) baseStart_849734 baseEnd_849734 := by
    simpa [prefixWord, tailWord_849734, baseEnd_849734] using wordTrace_append hprefix tailTrace_849734
  have hstable : (prefixWord ++ tailWord_849734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849734).length < 2 ^ (prefixWord ++ tailWord_849734).sum := by decide
  have hdescent : baseEnd_849734 < baseStart_849734 := by decide
  rcases family_descends (prefixWord ++ tailWord_849734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849773 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_849773 : Nat := 118140960795 + 849773 * 2 ^ 59
def prefixEnd_849773 : Nat := 4983230072969 + 3 ^ 40 * 849773 * 2
def baseEnd_849773 : Nat := 436341996213208992929471

theorem tailTrace_849773 : CollatzResearch.WordTrace tailWord_849773 prefixEnd_849773 436341996213208992929471 := by
  unfold tailWord_849773
  simp only [CollatzResearch.WordTrace]
  refine ⟨30993767550425025519145973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20662511700283350346097315 30993767550425025519145973)
  ·
    refine ⟨2905665707852346142419935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30993767550425025519145973 2905665707852346142419935)
    ·
      refine ⟨4358498561778519213629903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2905665707852346142419935 4358498561778519213629903)
      ·
        refine ⟨6537747842667778820444855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4358498561778519213629903 6537747842667778820444855)
        ·
          refine ⟨9806621764001668230667283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537747842667778820444855 9806621764001668230667283)
          ·
            refine ⟨14709932646002502346000925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806621764001668230667283 14709932646002502346000925)
            ·
              refine ⟨5516224742250938379750347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14709932646002502346000925 5516224742250938379750347)
              ·
                refine ⟨8274337113376407569625521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516224742250938379750347 8274337113376407569625521)
                ·
                  refine ⟨6205752835032305677219141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8274337113376407569625521 6205752835032305677219141)
                  ·
                    refine ⟨1163578656568557314478589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205752835032305677219141 1163578656568557314478589)
                    ·
                      refine ⟨436341996213208992929471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163578656568557314478589 436341996213208992929471)
                      ·
                        rfl

theorem cell23_849773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_849773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849773 prefixEnd_849773 := by exact prefixLift 849773
  have htrace : WordTrace (prefixWord ++ tailWord_849773) baseStart_849773 baseEnd_849773 := by
    simpa [prefixWord, tailWord_849773, baseEnd_849773] using wordTrace_append hprefix tailTrace_849773
  have hstable : (prefixWord ++ tailWord_849773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849773).length < 2 ^ (prefixWord ++ tailWord_849773).sum := by decide
  have hdescent : baseEnd_849773 < baseStart_849773 := by decide
  rcases family_descends (prefixWord ++ tailWord_849773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849776 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 7]
def baseStart_849776 : Nat := 118140960795 + 849776 * 2 ^ 59
def prefixEnd_849776 : Nat := 4983230072969 + 3 ^ 40 * 849776 * 2
def baseEnd_849776 : Nat := 48482615183908053465773

theorem tailTrace_849776 : CollatzResearch.WordTrace tailWord_849776 prefixEnd_849776 48482615183908053465773 := by
  unfold tailWord_849776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15496938484707078515752591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20662584646276104687670121 15496938484707078515752591)
  ·
    refine ⟨23245407727060617773628887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15496938484707078515752591 23245407727060617773628887)
    ·
      refine ⟨34868111590590926660443331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23245407727060617773628887 34868111590590926660443331)
      ·
        refine ⟨52302167385886389990664997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34868111590590926660443331 52302167385886389990664997)
        ·
          refine ⟨9806656384853698123249687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52302167385886389990664997 9806656384853698123249687)
          ·
            refine ⟨14709984577280547184874531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806656384853698123249687 14709984577280547184874531)
            ·
              refine ⟨22064976865920820777311797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14709984577280547184874531 22064976865920820777311797)
              ·
                refine ⟨2068591581180076947872981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22064976865920820777311797 2068591581180076947872981)
                ·
                  refine ⟨48482615183908053465773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2068591581180076947872981 48482615183908053465773)
                  ·
                    rfl

theorem cell23_849776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 7].length) (baseStart_849776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849776 prefixEnd_849776 := by exact prefixLift 849776
  have htrace : WordTrace (prefixWord ++ tailWord_849776) baseStart_849776 baseEnd_849776 := by
    simpa [prefixWord, tailWord_849776, baseEnd_849776] using wordTrace_append hprefix tailTrace_849776
  have hstable : (prefixWord ++ tailWord_849776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849776).length < 2 ^ (prefixWord ++ tailWord_849776).sum := by decide
  have hdescent : baseEnd_849776 < baseStart_849776 := by decide
  rcases family_descends (prefixWord ++ tailWord_849776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849820 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_849820 : Nat := 118140960795 + 849820 * 2 ^ 59
def prefixEnd_849820 : Nat := 4983230072969 + 3 ^ 40 * 849820 * 2
def baseEnd_849820 : Nat := 436366129803970309041755

theorem tailTrace_849820 : CollatzResearch.WordTrace tailWord_849820 prefixEnd_849820 436366129803970309041755 := by
  unfold tailWord_849820
  simp only [CollatzResearch.WordTrace]
  refine ⟨15497740890627376273053457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20663654520836501697404609 15497740890627376273053457)
  ·
    refine ⟨11623305667970532204790093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15497740890627376273053457 11623305667970532204790093)
    ·
      refine ⟨4358739625488949576796285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11623305667970532204790093 4358739625488949576796285)
      ·
        refine ⟨1634527359558356091298607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4358739625488949576796285 1634527359558356091298607)
        ·
          refine ⟨2451791039337534136947911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634527359558356091298607 2451791039337534136947911)
          ·
            refine ⟨3677686559006301205421867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451791039337534136947911 3677686559006301205421867)
            ·
              refine ⟨5516529838509451808132801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677686559006301205421867 5516529838509451808132801)
              ·
                refine ⟨4137397378882088856099601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516529838509451808132801 4137397378882088856099601)
                ·
                  refine ⟨3103048034161566642074701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137397378882088856099601 3103048034161566642074701)
                  ·
                    refine ⟨1163643012810587490778013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3103048034161566642074701 1163643012810587490778013)
                    ·
                      refine ⟨436366129803970309041755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163643012810587490778013 436366129803970309041755)
                      ·
                        rfl

theorem cell23_849820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_849820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849820 prefixEnd_849820 := by exact prefixLift 849820
  have htrace : WordTrace (prefixWord ++ tailWord_849820) baseStart_849820 baseEnd_849820 := by
    simpa [prefixWord, tailWord_849820, baseEnd_849820] using wordTrace_append hprefix tailTrace_849820
  have hstable : (prefixWord ++ tailWord_849820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849820).length < 2 ^ (prefixWord ++ tailWord_849820).sum := by decide
  have hdescent : baseEnd_849820 < baseStart_849820 := by decide
  rcases family_descends (prefixWord ++ tailWord_849820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849836 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_849836 : Nat := 118140960795 + 849836 * 2 ^ 59
def prefixEnd_849836 : Nat := 4983230072969 + 3 ^ 40 * 849836 * 2
def baseEnd_849836 : Nat := 145458115164814082147227

theorem tailTrace_849836 : CollatzResearch.WordTrace tailWord_849836 prefixEnd_849836 145458115164814082147227 := by
  unfold tailWord_849836
  simp only [CollatzResearch.WordTrace]
  refine ⟨15498032674598393639344681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20664043566131191519126241 15498032674598393639344681)
  ·
    refine ⟨11623524505948795229508511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15498032674598393639344681 11623524505948795229508511)
    ·
      refine ⟨17435286758923192844262767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11623524505948795229508511 17435286758923192844262767)
      ·
        refine ⟨26152930138384789266394151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17435286758923192844262767 26152930138384789266394151)
        ·
          refine ⟨39229395207577183899591227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26152930138384789266394151 39229395207577183899591227)
          ·
            refine ⟨58844092811365775849386841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39229395207577183899591227 58844092811365775849386841)
            ·
              refine ⟨44133069608524331887040131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58844092811365775849386841 44133069608524331887040131)
              ·
                refine ⟨66199604412786497830560197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44133069608524331887040131 66199604412786497830560197)
                ·
                  refine ⟨12412425827397468343230037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66199604412786497830560197 12412425827397468343230037)
                  ·
                    refine ⟨145458115164814082147227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12412425827397468343230037 145458115164814082147227)
                    ·
                      rfl

theorem cell23_849836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_849836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849836 prefixEnd_849836 := by exact prefixLift 849836
  have htrace : WordTrace (prefixWord ++ tailWord_849836) baseStart_849836 baseEnd_849836 := by
    simpa [prefixWord, tailWord_849836, baseEnd_849836] using wordTrace_append hprefix tailTrace_849836
  have hstable : (prefixWord ++ tailWord_849836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849836).length < 2 ^ (prefixWord ++ tailWord_849836).sum := by decide
  have hdescent : baseEnd_849836 < baseStart_849836 := by decide
  rcases family_descends (prefixWord ++ tailWord_849836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849838 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_849838 : Nat := 118140960795 + 849838 * 2 ^ 59
def prefixEnd_849838 : Nat := 4983230072969 + 3 ^ 40 * 849838 * 2
def baseEnd_849838 : Nat := 436375372455751238616673

theorem tailTrace_849838 : CollatzResearch.WordTrace tailWord_849838 prefixEnd_849838 436375372455751238616673 := by
  unfold tailWord_849838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874517286898692702532771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20664092196793027746841445 3874517286898692702532771)
  ·
    refine ⟨5811775930348039053799157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874517286898692702532771 5811775930348039053799157)
    ·
      refine ⟨544853993470128661293671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5811775930348039053799157 544853993470128661293671)
      ·
        refine ⟨817280990205192991940507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544853993470128661293671 817280990205192991940507)
        ·
          refine ⟨1225921485307789487910761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817280990205192991940507 1225921485307789487910761)
          ·
            refine ⟨919441113980842115933071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225921485307789487910761 919441113980842115933071)
            ·
              refine ⟨1379161670971263173899607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919441113980842115933071 1379161670971263173899607)
              ·
                refine ⟨2068742506456894760849411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379161670971263173899607 2068742506456894760849411)
                ·
                  refine ⟨3103113759685342141274117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068742506456894760849411 3103113759685342141274117)
                  ·
                    refine ⟨581833829941001651488897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3103113759685342141274117 581833829941001651488897)
                    ·
                      refine ⟨436375372455751238616673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581833829941001651488897 436375372455751238616673)
                      ·
                        rfl

theorem cell23_849838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_849838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849838 prefixEnd_849838 := by exact prefixLift 849838
  have htrace : WordTrace (prefixWord ++ tailWord_849838) baseStart_849838 baseEnd_849838 := by
    simpa [prefixWord, tailWord_849838, baseEnd_849838] using wordTrace_append hprefix tailTrace_849838
  have hstable : (prefixWord ++ tailWord_849838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849838).length < 2 ^ (prefixWord ++ tailWord_849838).sum := by decide
  have hdescent : baseEnd_849838 < baseStart_849838 := by decide
  rcases family_descends (prefixWord ++ tailWord_849838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849880 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_849880 : Nat := 118140960795 + 849880 * 2 ^ 59
def prefixEnd_849880 : Nat := 4983230072969 + 3 ^ 40 * 849880 * 2
def baseEnd_849880 : Nat := 436396938643240074291479

theorem tailTrace_849880 : CollatzResearch.WordTrace tailWord_849880 prefixEnd_849880 436396938643240074291479 := by
  unfold tailWord_849880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15498835080518691396645547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20665113440691588528860729 15498835080518691396645547)
  ·
    refine ⟨23248252620778037094968321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15498835080518691396645547 23248252620778037094968321)
    ·
      refine ⟨17436189465583527821226241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23248252620778037094968321 17436189465583527821226241)
      ·
        refine ⟨13077142099187645865919681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17436189465583527821226241 13077142099187645865919681)
        ·
          refine ⟨9807856574390734399439761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13077142099187645865919681 9807856574390734399439761)
          ·
            refine ⟨7355892430793050799579821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9807856574390734399439761 7355892430793050799579821)
            ·
              refine ⟨2758459661547394049842433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7355892430793050799579821 2758459661547394049842433)
              ·
                refine ⟨2068844746160545537381825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758459661547394049842433 2068844746160545537381825)
                ·
                  refine ⟨1551633559620409153036369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2068844746160545537381825 1551633559620409153036369)
                  ·
                    refine ⟨1163725169715306864777277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1551633559620409153036369 1163725169715306864777277)
                    ·
                      refine ⟨436396938643240074291479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163725169715306864777277 436396938643240074291479)
                      ·
                        rfl

theorem cell23_849880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_849880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849880 prefixEnd_849880 := by exact prefixLift 849880
  have htrace : WordTrace (prefixWord ++ tailWord_849880) baseStart_849880 baseEnd_849880 := by
    simpa [prefixWord, tailWord_849880, baseEnd_849880] using wordTrace_append hprefix tailTrace_849880
  have hstable : (prefixWord ++ tailWord_849880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849880).length < 2 ^ (prefixWord ++ tailWord_849880).sum := by decide
  have hdescent : baseEnd_849880 < baseStart_849880 := by decide
  rcases family_descends (prefixWord ++ tailWord_849880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849884 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_849884 : Nat := 118140960795 + 849884 * 2 ^ 59
def prefixEnd_849884 : Nat := 4983230072969 + 3 ^ 40 * 849884 * 2
def baseEnd_849884 : Nat := 436398992565858058641461

theorem tailTrace_849884 : CollatzResearch.WordTrace tailWord_849884 prefixEnd_849884 436398992565858058641461 := by
  unfold tailWord_849884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15498908026511445738218353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20665210702015260984291137 15498908026511445738218353)
  ·
    refine ⟨11624181019883584303663765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15498908026511445738218353 11624181019883584303663765)
    ·
      refine ⟨544883485307043014234239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11624181019883584303663765 544883485307043014234239)
      ·
        refine ⟨817325227960564521351359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544883485307043014234239 817325227960564521351359)
        ·
          refine ⟨1225987841940846782027039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817325227960564521351359 1225987841940846782027039)
          ·
            refine ⟨1838981762911270173040559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225987841940846782027039 1838981762911270173040559)
            ·
              refine ⟨2758472644366905259560839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838981762911270173040559 2758472644366905259560839)
              ·
                refine ⟨4137708966550357889341259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758472644366905259560839 4137708966550357889341259)
                ·
                  refine ⟨6206563449825536834011889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137708966550357889341259 6206563449825536834011889)
                  ·
                    refine ⟨4654922587369152625508917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6206563449825536834011889 4654922587369152625508917)
                    ·
                      refine ⟨436398992565858058641461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4654922587369152625508917 436398992565858058641461)
                      ·
                        rfl

theorem cell23_849884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_849884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849884 prefixEnd_849884 := by exact prefixLift 849884
  have htrace : WordTrace (prefixWord ++ tailWord_849884) baseStart_849884 baseEnd_849884 := by
    simpa [prefixWord, tailWord_849884, baseEnd_849884] using wordTrace_append hprefix tailTrace_849884
  have hstable : (prefixWord ++ tailWord_849884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849884).length < 2 ^ (prefixWord ++ tailWord_849884).sum := by decide
  have hdescent : baseEnd_849884 < baseStart_849884 := by decide
  rcases family_descends (prefixWord ++ tailWord_849884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849887 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 3, 4]
def baseStart_849887 : Nat := 118140960795 + 849887 * 2 ^ 59
def prefixEnd_849887 : Nat := 4983230072969 + 3 ^ 40 * 849887 * 2
def baseEnd_849887 : Nat := 145466844335940515634649

theorem tailTrace_849887 : CollatzResearch.WordTrace tailWord_849887 prefixEnd_849887 145466844335940515634649 := by
  unfold tailWord_849887
  simp only [CollatzResearch.WordTrace]
  refine ⟨30997925472012022988795915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20665283648008015325863943 30997925472012022988795915)
  ·
    refine ⟨46496888208018034483193873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30997925472012022988795915 46496888208018034483193873)
    ·
      refine ⟨34872666156013525862395405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46496888208018034483193873 34872666156013525862395405)
      ·
        refine ⟨13077249808505072198398277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34872666156013525862395405 13077249808505072198398277)
        ·
          refine ⟨2451984339094701037199677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13077249808505072198398277 2451984339094701037199677)
          ·
            refine ⟨919494127160512888949879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2451984339094701037199677 919494127160512888949879)
            ·
              refine ⟨1379241190740769333424819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919494127160512888949879 1379241190740769333424819)
              ·
                refine ⟨2068861786111154000137229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379241190740769333424819 2068861786111154000137229)
                ·
                  refine ⟨775823169791682750051461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2068861786111154000137229 775823169791682750051461)
                  ·
                    refine ⟨145466844335940515634649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 775823169791682750051461 145466844335940515634649)
                    ·
                      rfl

theorem cell23_849887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 4].length) (baseStart_849887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849887 prefixEnd_849887 := by exact prefixLift 849887
  have htrace : WordTrace (prefixWord ++ tailWord_849887) baseStart_849887 baseEnd_849887 := by
    simpa [prefixWord, tailWord_849887, baseEnd_849887] using wordTrace_append hprefix tailTrace_849887
  have hstable : (prefixWord ++ tailWord_849887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849887).length < 2 ^ (prefixWord ++ tailWord_849887).sum := by decide
  have hdescent : baseEnd_849887 < baseStart_849887 := by decide
  rcases family_descends (prefixWord ++ tailWord_849887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849944 : List Nat := [2, 1, 2, 3, 2, 1, 3, 4, 1, 1, 3]
def baseStart_849944 : Nat := 118140960795 + 849944 * 2 ^ 59
def prefixEnd_849944 : Nat := 4983230072969 + 3 ^ 40 * 849944 * 2
def baseEnd_849944 : Nat := 436429801405127823891185

theorem tailTrace_849944 : CollatzResearch.WordTrace tailWord_849944 prefixEnd_849944 436429801405127823891185 := by
  unfold tailWord_849944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15500002216402760861810443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20666669621870347815747257 15500002216402760861810443)
  ·
    refine ⟨23250003324604141292715665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15500002216402760861810443 23250003324604141292715665)
    ·
      refine ⟨17437502493453105969536749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23250003324604141292715665 17437502493453105969536749)
      ·
        refine ⟨6539063435044914738576281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17437502493453105969536749 6539063435044914738576281)
        ·
          refine ⟨4904297576283686053932211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6539063435044914738576281 4904297576283686053932211)
          ·
            refine ⟨7356446364425529080898317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904297576283686053932211 7356446364425529080898317)
            ·
              refine ⟨2758667386659573405336869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7356446364425529080898317 2758667386659573405336869)
              ·
                refine ⟨517250134998670013500663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2758667386659573405336869 517250134998670013500663)
                ·
                  refine ⟨775875202498005020250995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517250134998670013500663 775875202498005020250995)
                  ·
                    refine ⟨1163812803747007530376493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 775875202498005020250995 1163812803747007530376493)
                    ·
                      refine ⟨436429801405127823891185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163812803747007530376493 436429801405127823891185)
                      ·
                        rfl

theorem cell23_849944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_849944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849944 prefixEnd_849944 := by exact prefixLift 849944
  have htrace : WordTrace (prefixWord ++ tailWord_849944) baseStart_849944 baseEnd_849944 := by
    simpa [prefixWord, tailWord_849944, baseEnd_849944] using wordTrace_append hprefix tailTrace_849944
  have hstable : (prefixWord ++ tailWord_849944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849944).length < 2 ^ (prefixWord ++ tailWord_849944).sum := by decide
  have hdescent : baseEnd_849944 < baseStart_849944 := by decide
  rcases family_descends (prefixWord ++ tailWord_849944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849973 : List Nat := [1, 3, 3, 1, 1, 1, 2, 11]
def baseStart_849973 : Nat := 118140960795 + 849973 * 2 ^ 59
def prefixEnd_849973 : Nat := 4983230072969 + 3 ^ 40 * 849973 * 2
def baseEnd_849973 : Nat := 16164618234966970756613

theorem tailTrace_849973 : CollatzResearch.WordTrace tailWord_849973 prefixEnd_849973 16164618234966970756613 := by
  unfold tailWord_849973
  simp only [CollatzResearch.WordTrace]
  refine ⟨31001062149700459676426573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20667374766466973117617715 31001062149700459676426573)
  ·
    refine ⟨11625398306137672378659965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31001062149700459676426573 11625398306137672378659965)
    ·
      refine ⟨4359524364801627141997487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11625398306137672378659965 4359524364801627141997487)
      ·
        refine ⟨6539286547202440712996231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359524364801627141997487 6539286547202440712996231)
        ·
          refine ⟨9808929820803661069494347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6539286547202440712996231 9808929820803661069494347)
          ·
            refine ⟨14713394731205491604241521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808929820803661069494347 14713394731205491604241521)
            ·
              refine ⟨11035046048404118703181141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14713394731205491604241521 11035046048404118703181141)
              ·
                refine ⟨16164618234966970756613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 11035046048404118703181141 16164618234966970756613)
                ·
                  rfl

theorem cell23_849973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 11].length) (baseStart_849973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849973 prefixEnd_849973 := by exact prefixLift 849973
  have htrace : WordTrace (prefixWord ++ tailWord_849973) baseStart_849973 baseEnd_849973 := by
    simpa [prefixWord, tailWord_849973, baseEnd_849973] using wordTrace_append hprefix tailTrace_849973
  have hstable : (prefixWord ++ tailWord_849973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849973).length < 2 ^ (prefixWord ++ tailWord_849973).sum := by decide
  have hdescent : baseEnd_849973 < baseStart_849973 := by decide
  rcases family_descends (prefixWord ++ tailWord_849973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849980 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_849980 : Nat := 118140960795 + 849980 * 2 ^ 59
def prefixEnd_849980 : Nat := 4983230072969 + 3 ^ 40 * 849980 * 2
def baseEnd_849980 : Nat := 436448286708689683041019

theorem tailTrace_849980 : CollatzResearch.WordTrace tailWord_849980 prefixEnd_849980 436448286708689683041019 := by
  unfold tailWord_849980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15500658730337549935965697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20667544973783399914620929 15500658730337549935965697)
  ·
    refine ⟨11625494047753162451974273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15500658730337549935965697 11625494047753162451974273)
    ·
      refine ⟨8719120535814871838980705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11625494047753162451974273 8719120535814871838980705)
      ·
        refine ⟨6539340401861153879235529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8719120535814871838980705 6539340401861153879235529)
        ·
          refine ⟨4904505301395865409426647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6539340401861153879235529 4904505301395865409426647)
          ·
            refine ⟨7356757952093798114139971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904505301395865409426647 7356757952093798114139971)
            ·
              refine ⟨11035136928140697171209957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7356757952093798114139971 11035136928140697171209957)
              ·
                refine ⟨2069088174026380719601867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11035136928140697171209957 2069088174026380719601867)
                ·
                  refine ⟨3103632261039571079402801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069088174026380719601867 3103632261039571079402801)
                  ·
                    refine ⟨2327724195779678309552101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3103632261039571079402801 2327724195779678309552101)
                    ·
                      refine ⟨436448286708689683041019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2327724195779678309552101 436448286708689683041019)
                      ·
                        rfl

theorem cell23_849980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_849980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849980 prefixEnd_849980 := by exact prefixLift 849980
  have htrace : WordTrace (prefixWord ++ tailWord_849980) baseStart_849980 baseEnd_849980 := by
    simpa [prefixWord, tailWord_849980, baseEnd_849980] using wordTrace_append hprefix tailTrace_849980
  have hstable : (prefixWord ++ tailWord_849980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849980).length < 2 ^ (prefixWord ++ tailWord_849980).sum := by decide
  have hdescent : baseEnd_849980 < baseStart_849980 := by decide
  rcases family_descends (prefixWord ++ tailWord_849980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849984 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 1, 1, 4]
def baseStart_849984 : Nat := 118140960795 + 849984 * 2 ^ 59
def prefixEnd_849984 : Nat := 4983230072969 + 3 ^ 40 * 849984 * 2
def baseEnd_849984 : Nat := 436450340631307667391001

theorem tailTrace_849984 : CollatzResearch.WordTrace tailWord_849984 prefixEnd_849984 436450340631307667391001 := by
  unfold tailWord_849984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15500731676330304277538503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20667642235107072370051337 15500731676330304277538503)
  ·
    refine ⟨23251097514495456416307755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15500731676330304277538503 23251097514495456416307755)
    ·
      refine ⟨34876646271743184624461633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23251097514495456416307755 34876646271743184624461633)
      ·
        refine ⟨26157484703807388468346225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34876646271743184624461633 26157484703807388468346225)
        ·
          refine ⟨19618113527855541351259669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26157484703807388468346225 19618113527855541351259669)
          ·
            refine ⟨919599071618228500840297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19618113527855541351259669 919599071618228500840297)
            ·
              refine ⟨689699303713671375630223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919599071618228500840297 689699303713671375630223)
              ·
                refine ⟨1034548955570507063445335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689699303713671375630223 1034548955570507063445335)
                ·
                  refine ⟨1551823433355760595168003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034548955570507063445335 1551823433355760595168003)
                  ·
                    refine ⟨2327735150033640892752005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1551823433355760595168003 2327735150033640892752005)
                    ·
                      refine ⟨436450340631307667391001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2327735150033640892752005 436450340631307667391001)
                      ·
                        rfl

theorem cell23_849984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_849984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_849984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_849984 prefixEnd_849984 := by exact prefixLift 849984
  have htrace : WordTrace (prefixWord ++ tailWord_849984) baseStart_849984 baseEnd_849984 := by
    simpa [prefixWord, tailWord_849984, baseEnd_849984] using wordTrace_append hprefix tailTrace_849984
  have hstable : (prefixWord ++ tailWord_849984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849984).length < 2 ^ (prefixWord ++ tailWord_849984).sum := by decide
  have hdescent : baseEnd_849984 < baseStart_849984 := by decide
  rcases family_descends (prefixWord ++ tailWord_849984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850030 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_850030 : Nat := 118140960795 + 850030 * 2 ^ 59
def prefixEnd_850030 : Nat := 4983230072969 + 3 ^ 40 * 850030 * 2
def baseEnd_850030 : Nat := 436473960741414487415789

theorem tailTrace_850030 : CollatzResearch.WordTrace tailWord_850030 prefixEnd_850030 436473960741414487415789 := by
  unfold tailWord_850030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3875392638811744801406443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20668760740329305607501029 3875392638811744801406443)
  ·
    refine ⟨5813088958217617202109665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3875392638811744801406443 5813088958217617202109665)
    ·
      refine ⟨4359816718663212901582249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5813088958217617202109665 4359816718663212901582249)
      ·
        refine ⟨3269862538997409676186687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4359816718663212901582249 3269862538997409676186687)
        ·
          refine ⟨4904793808496114514280031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3269862538997409676186687 4904793808496114514280031)
          ·
            refine ⟨7357190712744171771420047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904793808496114514280031 7357190712744171771420047)
            ·
              refine ⟨11035786069116257657130071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357190712744171771420047 11035786069116257657130071)
              ·
                refine ⟨16553679103674386485695107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11035786069116257657130071 16553679103674386485695107)
                ·
                  refine ⟨24830518655511579728542661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16553679103674386485695107 24830518655511579728542661)
                  ·
                    refine ⟨4655722247908421199101749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24830518655511579728542661 4655722247908421199101749)
                    ·
                      refine ⟨436473960741414487415789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4655722247908421199101749 436473960741414487415789)
                      ·
                        rfl

theorem cell23_850030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_850030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850030 prefixEnd_850030 := by exact prefixLift 850030
  have htrace : WordTrace (prefixWord ++ tailWord_850030) baseStart_850030 baseEnd_850030 := by
    simpa [prefixWord, tailWord_850030, baseEnd_850030] using wordTrace_append hprefix tailTrace_850030
  have hstable : (prefixWord ++ tailWord_850030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850030).length < 2 ^ (prefixWord ++ tailWord_850030).sum := by decide
  have hdescent : baseEnd_850030 < baseStart_850030 := by decide
  rcases family_descends (prefixWord ++ tailWord_850030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850044 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_850044 : Nat := 118140960795 + 850044 * 2 ^ 59
def prefixEnd_850044 : Nat := 4983230072969 + 3 ^ 40 * 850044 * 2
def baseEnd_850044 : Nat := 436481149470577432640725

theorem tailTrace_850044 : CollatzResearch.WordTrace tailWord_850044 prefixEnd_850044 436481149470577432640725 := by
  unfold tailWord_850044
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501825866221619401130593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20669101154962159201507457 15501825866221619401130593)
  ·
    refine ⟨11626369399666214550847945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15501825866221619401130593 11626369399666214550847945)
    ·
      refine ⟨8719777049749660913135959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11626369399666214550847945 8719777049749660913135959)
      ·
        refine ⟨13079665574624491369703939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8719777049749660913135959 13079665574624491369703939)
        ·
          refine ⟨19619498361936737054555909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13079665574624491369703939 19619498361936737054555909)
          ·
            refine ⟨3678655942863138197729233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19619498361936737054555909 3678655942863138197729233)
            ·
              refine ⟨2758991957147353648296925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678655942863138197729233 2758991957147353648296925)
              ·
                refine ⟨1034621983930257618111347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2758991957147353648296925 1034621983930257618111347)
                ·
                  refine ⟨1551932975895386427167021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034621983930257618111347 1551932975895386427167021)
                  ·
                    refine ⟨581974865960769910187633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1551932975895386427167021 581974865960769910187633)
                    ·
                      refine ⟨436481149470577432640725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 581974865960769910187633 436481149470577432640725)
                      ·
                        rfl

theorem cell23_850044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_850044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850044 prefixEnd_850044 := by exact prefixLift 850044
  have htrace : WordTrace (prefixWord ++ tailWord_850044) baseStart_850044 baseEnd_850044 := by
    simpa [prefixWord, tailWord_850044, baseEnd_850044] using wordTrace_append hprefix tailTrace_850044
  have hstable : (prefixWord ++ tailWord_850044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850044).length < 2 ^ (prefixWord ++ tailWord_850044).sum := by decide
  have hdescent : baseEnd_850044 < baseStart_850044 := by decide
  rcases family_descends (prefixWord ++ tailWord_850044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850068 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_850068 : Nat := 118140960795 + 850068 * 2 ^ 59
def prefixEnd_850068 : Nat := 4983230072969 + 3 ^ 40 * 850068 * 2
def baseEnd_850068 : Nat := 436493473006285338740615

theorem tailTrace_850068 : CollatzResearch.WordTrace tailWord_850068 prefixEnd_850068 436493473006285338740615 := by
  unfold tailWord_850068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15502263542178145450567429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20669684722904193934089905 15502263542178145450567429)
  ·
    refine ⟨2906674414158402271981393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15502263542178145450567429 2906674414158402271981393)
    ·
      refine ⟨2180005810618801703986045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2906674414158402271981393 2180005810618801703986045)
      ·
        refine ⟨817502178982050638994767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2180005810618801703986045 817502178982050638994767)
        ·
          refine ⟨1226253268473075958492151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817502178982050638994767 1226253268473075958492151)
          ·
            refine ⟨1839379902709613937738227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226253268473075958492151 1839379902709613937738227)
            ·
              refine ⟨2759069854064420906607341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839379902709613937738227 2759069854064420906607341)
              ·
                refine ⟨1034651195274157839977753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2759069854064420906607341 1034651195274157839977753)
                ·
                  refine ⟨775988396455618379983315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1034651195274157839977753 775988396455618379983315)
                  ·
                    refine ⟨1163982594683427569974973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 775988396455618379983315 1163982594683427569974973)
                    ·
                      refine ⟨436493473006285338740615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1163982594683427569974973 436493473006285338740615)
                      ·
                        rfl

theorem cell23_850068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_850068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850068 prefixEnd_850068 := by exact prefixLift 850068
  have htrace : WordTrace (prefixWord ++ tailWord_850068) baseStart_850068 baseEnd_850068 := by
    simpa [prefixWord, tailWord_850068, baseEnd_850068] using wordTrace_append hprefix tailTrace_850068
  have hstable : (prefixWord ++ tailWord_850068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850068).length < 2 ^ (prefixWord ++ tailWord_850068).sum := by decide
  have hdescent : baseEnd_850068 < baseStart_850068 := by decide
  rcases family_descends (prefixWord ++ tailWord_850068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850108 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_850108 : Nat := 118140960795 + 850108 * 2 ^ 59
def prefixEnd_850108 : Nat := 4983230072969 + 3 ^ 40 * 850108 * 2
def baseEnd_850108 : Nat := 436514012232465182240431

theorem tailTrace_850108 : CollatzResearch.WordTrace tailWord_850108 prefixEnd_850108 436514012232465182240431 := by
  unfold tailWord_850108
  simp only [CollatzResearch.WordTrace]
  refine ⟨15502993002105688866295489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20670657336140918488393985 15502993002105688866295489)
  ·
    refine ⟨11627244751579266649721617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15502993002105688866295489 11627244751579266649721617)
    ·
      refine ⟨8720433563684449987291213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11627244751579266649721617 8720433563684449987291213)
      ·
        refine ⟨3270162586381668745234205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8720433563684449987291213 3270162586381668745234205)
        ·
          refine ⟨1226310969893125779462827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3270162586381668745234205 1226310969893125779462827)
          ·
            refine ⟨1839466454839688669194241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226310969893125779462827 1839466454839688669194241)
            ·
              refine ⟨1379599841129766501895681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839466454839688669194241 1379599841129766501895681)
              ·
                refine ⟨1034699880847324876421761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379599841129766501895681 1034699880847324876421761)
                ·
                  refine ⟨776024910635493657316321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1034699880847324876421761 776024910635493657316321)
                  ·
                    refine ⟨582018682976620242987241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 776024910635493657316321 582018682976620242987241)
                    ·
                      refine ⟨436514012232465182240431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582018682976620242987241 436514012232465182240431)
                      ·
                        rfl

theorem cell23_850108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_850108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850108 prefixEnd_850108 := by exact prefixLift 850108
  have htrace : WordTrace (prefixWord ++ tailWord_850108) baseStart_850108 baseEnd_850108 := by
    simpa [prefixWord, tailWord_850108, baseEnd_850108] using wordTrace_append hprefix tailTrace_850108
  have hstable : (prefixWord ++ tailWord_850108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850108).length < 2 ^ (prefixWord ++ tailWord_850108).sum := by decide
  have hdescent : baseEnd_850108 < baseStart_850108 := by decide
  rcases family_descends (prefixWord ++ tailWord_850108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850117 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 2, 5, 2]
def baseStart_850117 : Nat := 118140960795 + 850117 * 2 ^ 59
def prefixEnd_850117 : Nat := 4983230072969 + 3 ^ 40 * 850117 * 2
def baseEnd_850117 : Nat := 436518633558355647027889

theorem tailTrace_850117 : CollatzResearch.WordTrace tailWord_850117 prefixEnd_850117 436518633558355647027889 := by
  unfold tailWord_850117
  simp only [CollatzResearch.WordTrace]
  refine ⟨31006314261178772269668605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20670876174119181513112403 31006314261178772269668605)
  ·
    refine ⟨11627367847942039601125727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31006314261178772269668605 11627367847942039601125727)
    ·
      refine ⟨17441051771913059401688591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11627367847942039601125727 17441051771913059401688591)
      ·
        refine ⟨26161577657869589102532887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17441051771913059401688591 26161577657869589102532887)
        ·
          refine ⟨39242366486804383653799331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26161577657869589102532887 39242366486804383653799331)
          ·
            refine ⟨58863549730206575480698997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39242366486804383653799331 58863549730206575480698997)
            ·
              refine ⟨5518457787206866451315531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58863549730206575480698997 5518457787206866451315531)
              ·
                refine ⟨8277686680810299676973297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5518457787206866451315531 8277686680810299676973297)
                ·
                  refine ⟨6208265010607724757729973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8277686680810299676973297 6208265010607724757729973)
                  ·
                    refine ⟨582024844744474196037185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6208265010607724757729973 582024844744474196037185)
                    ·
                      refine ⟨436518633558355647027889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582024844744474196037185 436518633558355647027889)
                      ·
                        rfl

theorem cell23_850117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_850117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850117 prefixEnd_850117 := by exact prefixLift 850117
  have htrace : WordTrace (prefixWord ++ tailWord_850117) baseStart_850117 baseEnd_850117 := by
    simpa [prefixWord, tailWord_850117, baseEnd_850117] using wordTrace_append hprefix tailTrace_850117
  have hstable : (prefixWord ++ tailWord_850117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850117).length < 2 ^ (prefixWord ++ tailWord_850117).sum := by decide
  have hdescent : baseEnd_850117 < baseStart_850117 := by decide
  rcases family_descends (prefixWord ++ tailWord_850117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850160 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_850160 : Nat := 118140960795 + 850160 * 2 ^ 59
def prefixEnd_850160 : Nat := 4983230072969 + 3 ^ 40 * 850160 * 2
def baseEnd_850160 : Nat := 436540713226498978790191

theorem tailTrace_850160 : CollatzResearch.WordTrace tailWord_850160 prefixEnd_850160 436540713226498978790191 := by
  unfold tailWord_850160
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503941300011495306741967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20671921733348660408989289 15503941300011495306741967)
  ·
    refine ⟨23255911950017242960112951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15503941300011495306741967 23255911950017242960112951)
    ·
      refine ⟨34883867925025864440169427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23255911950017242960112951 34883867925025864440169427)
      ·
        refine ⟨52325801887538796660254141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34883867925025864440169427 52325801887538796660254141)
        ·
          refine ⟨19622175707827048747595303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52325801887538796660254141 19622175707827048747595303)
          ·
            refine ⟨29433263561740573121392955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19622175707827048747595303 29433263561740573121392955)
            ·
              refine ⟨44149895342610859682089433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29433263561740573121392955 44149895342610859682089433)
              ·
                refine ⟨33112421506958144761567075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44149895342610859682089433 33112421506958144761567075)
                ·
                  refine ⟨49668632260437217142350613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33112421506958144761567075 49668632260437217142350613)
                  ·
                    refine ⟨2328217137207994553547685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49668632260437217142350613 2328217137207994553547685)
                    ·
                      refine ⟨436540713226498978790191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2328217137207994553547685 436540713226498978790191)
                      ·
                        rfl

theorem cell23_850160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_850160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850160 prefixEnd_850160 := by exact prefixLift 850160
  have htrace : WordTrace (prefixWord ++ tailWord_850160) baseStart_850160 baseEnd_850160 := by
    simpa [prefixWord, tailWord_850160, baseEnd_850160] using wordTrace_append hprefix tailTrace_850160
  have hstable : (prefixWord ++ tailWord_850160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850160).length < 2 ^ (prefixWord ++ tailWord_850160).sum := by decide
  have hdescent : baseEnd_850160 < baseStart_850160 := by decide
  rcases family_descends (prefixWord ++ tailWord_850160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850208 : List Nat := [2, 1, 1, 5, 2, 3, 1, 3, 1, 4]
def baseStart_850208 : Nat := 118140960795 + 850208 * 2 ^ 59
def prefixEnd_850208 : Nat := 4983230072969 + 3 ^ 40 * 850208 * 2
def baseEnd_850208 : Nat := 145521786765971596996657

theorem tailTrace_850208 : CollatzResearch.WordTrace tailWord_850208 prefixEnd_850208 145521786765971596996657 := by
  unfold tailWord_850208
  simp only [CollatzResearch.WordTrace]
  refine ⟨15504816651924547405615639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20673088869232729874154185 15504816651924547405615639)
  ·
    refine ⟨23257224977886821108423459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15504816651924547405615639 23257224977886821108423459)
    ·
      refine ⟨34885837466830231662635189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23257224977886821108423459 34885837466830231662635189)
      ·
        refine ⟨3270547262515334218372049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34885837466830231662635189 3270547262515334218372049)
        ·
          refine ⟨2452910446886500663779037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3270547262515334218372049 2452910446886500663779037)
          ·
            refine ⟨919841417582437748917139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2452910446886500663779037 919841417582437748917139)
            ·
              refine ⟨1379762126373656623375709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919841417582437748917139 1379762126373656623375709)
              ·
                refine ⟨517410797390121233765891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1379762126373656623375709 517410797390121233765891)
                ·
                  refine ⟨776116196085181850648837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517410797390121233765891 776116196085181850648837)
                  ·
                    refine ⟨145521786765971596996657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 776116196085181850648837 145521786765971596996657)
                    ·
                      rfl

theorem cell23_850208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 4].length) (baseStart_850208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850208 prefixEnd_850208 := by exact prefixLift 850208
  have htrace : WordTrace (prefixWord ++ tailWord_850208) baseStart_850208 baseEnd_850208 := by
    simpa [prefixWord, tailWord_850208, baseEnd_850208] using wordTrace_append hprefix tailTrace_850208
  have hstable : (prefixWord ++ tailWord_850208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850208).length < 2 ^ (prefixWord ++ tailWord_850208).sum := by decide
  have hdescent : baseEnd_850208 < baseStart_850208 := by decide
  rcases family_descends (prefixWord ++ tailWord_850208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850231 : List Nat := [1, 1, 3, 1, 2, 1, 1, 8, 1, 1, 3]
def baseStart_850231 : Nat := 118140960795 + 850231 * 2 ^ 59
def prefixEnd_850231 : Nat := 4983230072969 + 3 ^ 40 * 850231 * 2
def baseEnd_850231 : Nat := 436577170352968201002365

theorem tailTrace_850231 : CollatzResearch.WordTrace tailWord_850231 prefixEnd_850231 436577170352968201002365 := by
  unfold tailWord_850231
  simp only [CollatzResearch.WordTrace]
  refine ⟨31010472182765769739318547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20673648121843846492879031 31010472182765769739318547)
  ·
    refine ⟨46515708274148654608977821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31010472182765769739318547 46515708274148654608977821)
    ·
      refine ⟨17443390602805745478366683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46515708274148654608977821 17443390602805745478366683)
      ·
        refine ⟨26165085904208618217550025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17443390602805745478366683 26165085904208618217550025)
        ·
          refine ⟨19623814428156463663162519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26165085904208618217550025 19623814428156463663162519)
          ·
            refine ⟨29435721642234695494743779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19623814428156463663162519 29435721642234695494743779)
            ·
              refine ⟨44153582463352043242115669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29435721642234695494743779 44153582463352043242115669)
              ·
                refine ⟨517424794492406756743543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 44153582463352043242115669 517424794492406756743543)
                ·
                  refine ⟨776137191738610135115315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517424794492406756743543 776137191738610135115315)
                  ·
                    refine ⟨1164205787607915202672973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 776137191738610135115315 1164205787607915202672973)
                    ·
                      refine ⟨436577170352968201002365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1164205787607915202672973 436577170352968201002365)
                      ·
                        rfl

theorem cell23_850231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_850231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850231 prefixEnd_850231 := by exact prefixLift 850231
  have htrace : WordTrace (prefixWord ++ tailWord_850231) baseStart_850231 baseEnd_850231 := by
    simpa [prefixWord, tailWord_850231, baseEnd_850231] using wordTrace_append hprefix tailTrace_850231
  have hstable : (prefixWord ++ tailWord_850231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850231).length < 2 ^ (prefixWord ++ tailWord_850231).sum := by decide
  have hdescent : baseEnd_850231 < baseStart_850231 := by decide
  rcases family_descends (prefixWord ++ tailWord_850231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850247 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 1, 6]
def baseStart_850247 : Nat := 118140960795 + 850247 * 2 ^ 59
def prefixEnd_850247 : Nat := 4983230072969 + 3 ^ 40 * 850247 * 2
def baseEnd_850247 : Nat := 145528462014480046134097

theorem tailTrace_850247 : CollatzResearch.WordTrace tailWord_850247 prefixEnd_850247 145528462014480046134097 := by
  unfold tailWord_850247
  simp only [CollatzResearch.WordTrace]
  refine ⟨31011055750707804471900995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20674037167138536314600663 31011055750707804471900995)
  ·
    refine ⟨46516583626061706707851493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31011055750707804471900995 46516583626061706707851493)
    ·
      refine ⟨8721859429886570007722155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46516583626061706707851493 8721859429886570007722155)
      ·
        refine ⟨13082789144829855011583233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8721859429886570007722155 13082789144829855011583233)
        ·
          refine ⟨9812091858622391258687425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13082789144829855011583233 9812091858622391258687425)
          ·
            refine ⟨7359068893966793444015569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9812091858622391258687425 7359068893966793444015569)
            ·
              refine ⟨5519301670475095083011677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7359068893966793444015569 5519301670475095083011677)
              ·
                refine ⟨2069738126428160656129379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5519301670475095083011677 2069738126428160656129379)
                ·
                  refine ⟨3104607189642240984194069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069738126428160656129379 3104607189642240984194069)
                  ·
                    refine ⟨145528462014480046134097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3104607189642240984194069 145528462014480046134097)
                    ·
                      rfl

theorem cell23_850247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_850247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850247 prefixEnd_850247 := by exact prefixLift 850247
  have htrace : WordTrace (prefixWord ++ tailWord_850247) baseStart_850247 baseEnd_850247 := by
    simpa [prefixWord, tailWord_850247, baseEnd_850247] using wordTrace_append hprefix tailTrace_850247
  have hstable : (prefixWord ++ tailWord_850247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850247).length < 2 ^ (prefixWord ++ tailWord_850247).sum := by decide
  have hdescent : baseEnd_850247 < baseStart_850247 := by decide
  rcases family_descends (prefixWord ++ tailWord_850247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850254 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_850254 : Nat := 118140960795 + 850254 * 2 ^ 59
def prefixEnd_850254 : Nat := 4983230072969 + 3 ^ 40 * 850254 * 2
def baseEnd_850254 : Nat := 436588980408021611014759

theorem tailTrace_850254 : CollatzResearch.WordTrace tailWord_850254 prefixEnd_850254 436588980408021611014759 := by
  unfold tailWord_850254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3876413882710305583425727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20674207374454963111603877 3876413882710305583425727)
  ·
    refine ⟨5814620824065458375138591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3876413882710305583425727 5814620824065458375138591)
    ·
      refine ⟨8721931236098187562707887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814620824065458375138591 8721931236098187562707887)
      ·
        refine ⟨13082896854147281344061831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8721931236098187562707887 13082896854147281344061831)
        ·
          refine ⟨19624345281220922016092747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082896854147281344061831 19624345281220922016092747)
          ·
            refine ⟨29436517921831383024139121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19624345281220922016092747 29436517921831383024139121)
            ·
              refine ⟨22077388441373537268104341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29436517921831383024139121 22077388441373537268104341)
              ·
                refine ⟨1034877583189384559442391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22077388441373537268104341 1034877583189384559442391)
                ·
                  refine ⟨1552316374784076839163587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034877583189384559442391 1552316374784076839163587)
                  ·
                    refine ⟨2328474562176115258745381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1552316374784076839163587 2328474562176115258745381)
                    ·
                      refine ⟨436588980408021611014759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2328474562176115258745381 436588980408021611014759)
                      ·
                        rfl

theorem cell23_850254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_850254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850254 prefixEnd_850254 := by exact prefixLift 850254
  have htrace : WordTrace (prefixWord ++ tailWord_850254) baseStart_850254 baseEnd_850254 := by
    simpa [prefixWord, tailWord_850254, baseEnd_850254] using wordTrace_append hprefix tailTrace_850254
  have hstable : (prefixWord ++ tailWord_850254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850254).length < 2 ^ (prefixWord ++ tailWord_850254).sum := by decide
  have hdescent : baseEnd_850254 < baseStart_850254 := by decide
  rcases family_descends (prefixWord ++ tailWord_850254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850282 : List Nat := [3, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_850282 : Nat := 118140960795 + 850282 * 2 ^ 59
def prefixEnd_850282 : Nat := 4983230072969 + 3 ^ 40 * 850282 * 2
def baseEnd_850282 : Nat := 436603357866347501464631

theorem tailTrace_850282 : CollatzResearch.WordTrace tailWord_850282 prefixEnd_850282 436603357866347501464631 := by
  unfold tailWord_850282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7753083076395251362356275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20674888203720670299616733 7753083076395251362356275)
  ·
    refine ⟨11629624614592877043534413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7753083076395251362356275 11629624614592877043534413)
    ·
      refine ⟨4361109230472328891325405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11629624614592877043534413 4361109230472328891325405)
      ·
        refine ⟨1635415961427123334247027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4361109230472328891325405 1635415961427123334247027)
        ·
          refine ⟨2453123942140685001370541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635415961427123334247027 2453123942140685001370541)
          ·
            refine ⟨919921478302756875513953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2453123942140685001370541 919921478302756875513953)
            ·
              refine ⟨689941108727067656635465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919921478302756875513953 689941108727067656635465)
              ·
                refine ⟨517455831545300742476599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689941108727067656635465 517455831545300742476599)
                ·
                  refine ⟨776183747317951113714899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517455831545300742476599 776183747317951113714899)
                  ·
                    refine ⟨1164275620976926670572349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 776183747317951113714899 1164275620976926670572349)
                    ·
                      refine ⟨436603357866347501464631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1164275620976926670572349 436603357866347501464631)
                      ·
                        rfl

theorem cell23_850282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_850282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850282 prefixEnd_850282 := by exact prefixLift 850282
  have htrace : WordTrace (prefixWord ++ tailWord_850282) baseStart_850282 baseEnd_850282 := by
    simpa [prefixWord, tailWord_850282, baseEnd_850282] using wordTrace_append hprefix tailTrace_850282
  have hstable : (prefixWord ++ tailWord_850282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850282).length < 2 ^ (prefixWord ++ tailWord_850282).sum := by decide
  have hdescent : baseEnd_850282 < baseStart_850282 := by decide
  rcases family_descends (prefixWord ++ tailWord_850282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850304 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 8, 1, 3]
def baseStart_850304 : Nat := 118140960795 + 850304 * 2 ^ 59
def prefixEnd_850304 : Nat := 4983230072969 + 3 ^ 40 * 850304 * 2
def baseEnd_850304 : Nat := 436614654440746415389529

theorem tailTrace_850304 : CollatzResearch.WordTrace tailWord_850304 prefixEnd_850304 436614654440746415389529 := by
  unfold tailWord_850304
  simp only [CollatzResearch.WordTrace]
  refine ⟨15506567355750651603362983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20675423141000868804483977 15506567355750651603362983)
  ·
    refine ⟨23259851033625977405044475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15506567355750651603362983 23259851033625977405044475)
    ·
      refine ⟨34889776550438966107566713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23259851033625977405044475 34889776550438966107566713)
      ·
        refine ⟨26167332412829224580675035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34889776550438966107566713 26167332412829224580675035)
        ·
          refine ⟨39250998619243836871012553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26167332412829224580675035 39250998619243836871012553)
          ·
            refine ⟨29438248964432877653259415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39250998619243836871012553 29438248964432877653259415)
            ·
              refine ⟨44157373446649316479889123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29438248964432877653259415 44157373446649316479889123)
              ·
                refine ⟨66236060169973974719833685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44157373446649316479889123 66236060169973974719833685)
                ·
                  refine ⟨776203830116882516248051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 66236060169973974719833685 776203830116882516248051)
                  ·
                    refine ⟨1164305745175323774372077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 776203830116882516248051 1164305745175323774372077)
                    ·
                      refine ⟨436614654440746415389529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1164305745175323774372077 436614654440746415389529)
                      ·
                        rfl

theorem cell23_850304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_850304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850304 prefixEnd_850304 := by exact prefixLift 850304
  have htrace : WordTrace (prefixWord ++ tailWord_850304) baseStart_850304 baseEnd_850304 := by
    simpa [prefixWord, tailWord_850304, baseEnd_850304] using wordTrace_append hprefix tailTrace_850304
  have hstable : (prefixWord ++ tailWord_850304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850304).length < 2 ^ (prefixWord ++ tailWord_850304).sum := by decide
  have hdescent : baseEnd_850304 < baseStart_850304 := by decide
  rcases family_descends (prefixWord ++ tailWord_850304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850451 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 2, 4, 2]
def baseStart_850451 : Nat := 118140960795 + 850451 * 2 ^ 59
def prefixEnd_850451 : Nat := 4983230072969 + 3 ^ 40 * 850451 * 2
def baseEnd_850451 : Nat := 436690136096957340251353

theorem tailTrace_850451 : CollatzResearch.WordTrace tailWord_850451 prefixEnd_850451 436690136096957340251353 := by
  unfold tailWord_850451
  simp only [CollatzResearch.WordTrace]
  refine ⟨31018496241968747312327207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20678997494645831541551471 31018496241968747312327207)
  ·
    refine ⟨46527744362953120968490811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31018496241968747312327207 46527744362953120968490811)
    ·
      refine ⟨69791616544429681452736217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46527744362953120968490811 69791616544429681452736217)
      ·
        refine ⟨52343712408322261089552163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69791616544429681452736217 52343712408322261089552163)
        ·
          refine ⟨78515568612483391634328245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52343712408322261089552163 78515568612483391634328245)
          ·
            refine ⟨7360834557420317965718273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78515568612483391634328245 7360834557420317965718273)
            ·
              refine ⟨5520625918065238474288705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7360834557420317965718273 5520625918065238474288705)
              ·
                refine ⟨4140469438548928855716529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5520625918065238474288705 4140469438548928855716529)
                ·
                  refine ⟨3105352078911696641787397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140469438548928855716529 3105352078911696641787397)
                  ·
                    refine ⟨582253514795943120335137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3105352078911696641787397 582253514795943120335137)
                    ·
                      refine ⟨436690136096957340251353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582253514795943120335137 436690136096957340251353)
                      ·
                        rfl

theorem cell23_850451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 4, 2].length) (baseStart_850451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850451 prefixEnd_850451 := by exact prefixLift 850451
  have htrace : WordTrace (prefixWord ++ tailWord_850451) baseStart_850451 baseEnd_850451 := by
    simpa [prefixWord, tailWord_850451, baseEnd_850451] using wordTrace_append hprefix tailTrace_850451
  have hstable : (prefixWord ++ tailWord_850451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850451).length < 2 ^ (prefixWord ++ tailWord_850451).sum := by decide
  have hdescent : baseEnd_850451 < baseStart_850451 := by decide
  rcases family_descends (prefixWord ++ tailWord_850451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850452 : List Nat := [2, 4, 3, 1, 1, 3, 2, 2, 5]
def baseStart_850452 : Nat := 118140960795 + 850452 * 2 ^ 59
def prefixEnd_850452 : Nat := 4983230072969 + 3 ^ 40 * 850452 * 2
def baseEnd_850452 : Nat := 48521183286401315148761

theorem tailTrace_850452 : CollatzResearch.WordTrace tailWord_850452 prefixEnd_850452 48521183286401315148761 := by
  unfold tailWord_850452
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509266357482562241556805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20679021809976749655409073 15509266357482562241556805)
  ·
    refine ⟨2907987442027980420291901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15509266357482562241556805 2907987442027980420291901)
    ·
      refine ⟨1090495290760492657609463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2907987442027980420291901 1090495290760492657609463)
      ·
        refine ⟨1635742936140738986414195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090495290760492657609463 1635742936140738986414195)
        ·
          refine ⟨2453614404211108479621293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635742936140738986414195 2453614404211108479621293)
          ·
            refine ⟨920105401579165679857985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2453614404211108479621293 920105401579165679857985)
            ·
              refine ⟨690079051184374259893489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920105401579165679857985 690079051184374259893489)
              ·
                refine ⟨517559288388280694920117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690079051184374259893489 517559288388280694920117)
                ·
                  refine ⟨48521183286401315148761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517559288388280694920117 48521183286401315148761)
                  ·
                    rfl

theorem cell23_850452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_850452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850452 prefixEnd_850452 := by exact prefixLift 850452
  have htrace : WordTrace (prefixWord ++ tailWord_850452) baseStart_850452 baseEnd_850452 := by
    simpa [prefixWord, tailWord_850452, baseEnd_850452] using wordTrace_append hprefix tailTrace_850452
  have hstable : (prefixWord ++ tailWord_850452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850452).length < 2 ^ (prefixWord ++ tailWord_850452).sum := by decide
  have hdescent : baseEnd_850452 < baseStart_850452 := by decide
  rcases family_descends (prefixWord ++ tailWord_850452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850538 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_850538 : Nat := 118140960795 + 850538 * 2 ^ 59
def prefixEnd_850538 : Nat := 4983230072969 + 3 ^ 40 * 850538 * 2
def baseEnd_850538 : Nat := 145578269637966166621151

theorem tailTrace_850538 : CollatzResearch.WordTrace tailWord_850538 prefixEnd_850538 145578269637966166621151 := by
  unfold tailWord_850538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7755417348163390292686067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20681112928435707447162845 7755417348163390292686067)
  ·
    refine ⟨11633126022245085439029101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7755417348163390292686067 11633126022245085439029101)
    ·
      refine ⟨4362422258341907039635913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11633126022245085439029101 4362422258341907039635913)
      ·
        refine ⟨3271816693756430279726935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4362422258341907039635913 3271816693756430279726935)
        ·
          refine ⟨4907725040634645419590403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271816693756430279726935 4907725040634645419590403)
          ·
            refine ⟨7361587560951968129385605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907725040634645419590403 7361587560951968129385605)
            ·
              refine ⟨1380297667678494024259801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7361587560951968129385605 1380297667678494024259801)
              ·
                refine ⟨1035223250758870518194851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380297667678494024259801 1035223250758870518194851)
                ·
                  refine ⟨1552834876138305777292277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035223250758870518194851 1552834876138305777292277)
                  ·
                    refine ⟨145578269637966166621151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1552834876138305777292277 145578269637966166621151)
                    ·
                      rfl

theorem cell23_850538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_850538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850538 prefixEnd_850538 := by exact prefixLift 850538
  have htrace : WordTrace (prefixWord ++ tailWord_850538) baseStart_850538 baseEnd_850538 := by
    simpa [prefixWord, tailWord_850538, baseEnd_850538] using wordTrace_append hprefix tailTrace_850538
  have hstable : (prefixWord ++ tailWord_850538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850538).length < 2 ^ (prefixWord ++ tailWord_850538).sum := by decide
  have hdescent : baseEnd_850538 < baseStart_850538 := by decide
  rcases family_descends (prefixWord ++ tailWord_850538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850551 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 4, 4]
def baseStart_850551 : Nat := 118140960795 + 850551 * 2 ^ 59
def prefixEnd_850551 : Nat := 4983230072969 + 3 ^ 40 * 850551 * 2
def baseEnd_850551 : Nat := 145580494720802316333631

theorem tailTrace_850551 : CollatzResearch.WordTrace tailWord_850551 prefixEnd_850551 145580494720802316333631 := by
  unfold tailWord_850551
  simp only [CollatzResearch.WordTrace]
  refine ⟨31022143541606464390967507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20681429027737642927311671 31022143541606464390967507)
  ·
    refine ⟨46533215312409696586451261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31022143541606464390967507 46533215312409696586451261)
    ·
      refine ⟨17449955742153636219919223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46533215312409696586451261 17449955742153636219919223)
      ·
        refine ⟨26174933613230454329878835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17449955742153636219919223 26174933613230454329878835)
        ·
          refine ⟨39262400419845681494818253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26174933613230454329878835 39262400419845681494818253)
          ·
            refine ⟨14723400157442130560556845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39262400419845681494818253 14723400157442130560556845)
            ·
              refine ⟨5521275059040798960208817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14723400157442130560556845 5521275059040798960208817)
              ·
                refine ⟨4140956294280599220156613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5521275059040798960208817 4140956294280599220156613)
                ·
                  refine ⟨776429305177612353779365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4140956294280599220156613 776429305177612353779365)
                  ·
                    refine ⟨145580494720802316333631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 776429305177612353779365 145580494720802316333631)
                    ·
                      rfl

theorem cell23_850551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_850551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850551 prefixEnd_850551 := by exact prefixLift 850551
  have htrace : WordTrace (prefixWord ++ tailWord_850551) baseStart_850551 baseEnd_850551 := by
    simpa [prefixWord, tailWord_850551, baseEnd_850551] using wordTrace_append hprefix tailTrace_850551
  have hstable : (prefixWord ++ tailWord_850551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850551).length < 2 ^ (prefixWord ++ tailWord_850551).sum := by decide
  have hdescent : baseEnd_850551 < baseStart_850551 := by decide
  rcases family_descends (prefixWord ++ tailWord_850551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850578 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_850578 : Nat := 118140960795 + 850578 * 2 ^ 59
def prefixEnd_850578 : Nat := 4983230072969 + 3 ^ 40 * 850578 * 2
def baseEnd_850578 : Nat := 436755348140078343363269

theorem tailTrace_850578 : CollatzResearch.WordTrace tailWord_850578 prefixEnd_850578 436755348140078343363269 := by
  unfold tailWord_850578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7755782078127162000550097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20682085541672432001466925 7755782078127162000550097)
  ·
    refine ⟨5816836558595371500412573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7755782078127162000550097 5816836558595371500412573)
    ·
      refine ⟨2181313709473264312654715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5816836558595371500412573 2181313709473264312654715)
      ·
        refine ⟨3271970564209896468982073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181313709473264312654715 3271970564209896468982073)
        ·
          refine ⟨2453977923157422351736555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3271970564209896468982073 2453977923157422351736555)
          ·
            refine ⟨3680966884736133527604833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453977923157422351736555 3680966884736133527604833)
            ·
              refine ⟨2760725163552100145703625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680966884736133527604833 2760725163552100145703625)
              ·
                refine ⟨2070543872664075109277719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760725163552100145703625 2070543872664075109277719)
                ·
                  refine ⟨3105815808996112663916579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070543872664075109277719 3105815808996112663916579)
                  ·
                    refine ⟨4658723713494168995874869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105815808996112663916579 4658723713494168995874869)
                    ·
                      refine ⟨436755348140078343363269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4658723713494168995874869 436755348140078343363269)
                      ·
                        rfl

theorem cell23_850578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_850578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850578 prefixEnd_850578 := by exact prefixLift 850578
  have htrace : WordTrace (prefixWord ++ tailWord_850578) baseStart_850578 baseEnd_850578 := by
    simpa [prefixWord, tailWord_850578, baseEnd_850578] using wordTrace_append hprefix tailTrace_850578
  have hstable : (prefixWord ++ tailWord_850578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850578).length < 2 ^ (prefixWord ++ tailWord_850578).sum := by decide
  have hdescent : baseEnd_850578 < baseStart_850578 := by decide
  rcases family_descends (prefixWord ++ tailWord_850578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850592 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 1, 1, 4]
def baseStart_850592 : Nat := 118140960795 + 850592 * 2 ^ 59
def prefixEnd_850592 : Nat := 4983230072969 + 3 ^ 40 * 850592 * 2
def baseEnd_850592 : Nat := 436762536869241288588205

theorem tailTrace_850592 : CollatzResearch.WordTrace tailWord_850592 prefixEnd_850592 436762536869241288588205 := by
  unfold tailWord_850592
  simp only [CollatzResearch.WordTrace]
  refine ⟨15511819467228964196605015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20682425956305285595473353 15511819467228964196605015)
  ·
    refine ⟨23267729200843446294907523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15511819467228964196605015 23267729200843446294907523)
    ·
      refine ⟨34901593801265169442361285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23267729200843446294907523 34901593801265169442361285)
      ·
        refine ⟨6544048837737219270442741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34901593801265169442361285 6544048837737219270442741)
        ·
          refine ⟨613504578537864306604007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6544048837737219270442741 613504578537864306604007)
          ·
            refine ⟨920256867806796459906011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613504578537864306604007 920256867806796459906011)
            ·
              refine ⟨1380385301710194689859017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920256867806796459906011 1380385301710194689859017)
              ·
                refine ⟨1035288976282646017394263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380385301710194689859017 1035288976282646017394263)
                ·
                  refine ⟨1552933464423969026091395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035288976282646017394263 1552933464423969026091395)
                  ·
                    refine ⟨2329400196635953539137093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1552933464423969026091395 2329400196635953539137093)
                    ·
                      refine ⟨436762536869241288588205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2329400196635953539137093 436762536869241288588205)
                      ·
                        rfl

theorem cell23_850592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_850592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850592 prefixEnd_850592 := by exact prefixLift 850592
  have htrace : WordTrace (prefixWord ++ tailWord_850592) baseStart_850592 baseEnd_850592 := by
    simpa [prefixWord, tailWord_850592, baseEnd_850592] using wordTrace_append hprefix tailTrace_850592
  have hstable : (prefixWord ++ tailWord_850592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850592).length < 2 ^ (prefixWord ++ tailWord_850592).sum := by decide
  have hdescent : baseEnd_850592 < baseStart_850592 := by decide
  rcases family_descends (prefixWord ++ tailWord_850592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850641 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 2, 6]
def baseStart_850641 : Nat := 118140960795 + 850641 * 2 ^ 59
def prefixEnd_850641 : Nat := 4983230072969 + 3 ^ 40 * 850641 * 2
def baseEnd_850641 : Nat := 145595899140437198958493

theorem tailTrace_850641 : CollatzResearch.WordTrace tailWord_850641 prefixEnd_850641 145595899140437198958493 := by
  unfold tailWord_850641
  simp only [CollatzResearch.WordTrace]
  refine ⟨31025426111280409761743777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20683617407520273174495851 31025426111280409761743777)
  ·
    refine ⟨23269069583460307321307833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31025426111280409761743777 23269069583460307321307833)
    ·
      refine ⟨17451802187595230490980875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23269069583460307321307833 17451802187595230490980875)
      ·
        refine ⟨26177703281392845736471313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17451802187595230490980875 26177703281392845736471313)
        ·
          refine ⟨19633277461044634302353485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26177703281392845736471313 19633277461044634302353485)
          ·
            refine ⟨7362479047891737863382557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19633277461044634302353485 7362479047891737863382557)
            ·
              refine ⟨2760929642959401698768459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7362479047891737863382557 2760929642959401698768459)
              ·
                refine ⟨4141394464439102548152689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760929642959401698768459 4141394464439102548152689)
                ·
                  refine ⟨3106045848329326911114517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4141394464439102548152689 3106045848329326911114517)
                  ·
                    refine ⟨145595899140437198958493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3106045848329326911114517 145595899140437198958493)
                    ·
                      rfl

theorem cell23_850641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_850641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850641 prefixEnd_850641 := by exact prefixLift 850641
  have htrace : WordTrace (prefixWord ++ tailWord_850641) baseStart_850641 baseEnd_850641 := by
    simpa [prefixWord, tailWord_850641, baseEnd_850641] using wordTrace_append hprefix tailTrace_850641
  have hstable : (prefixWord ++ tailWord_850641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850641).length < 2 ^ (prefixWord ++ tailWord_850641).sum := by decide
  have hdescent : baseEnd_850641 < baseStart_850641 := by decide
  rcases family_descends (prefixWord ++ tailWord_850641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850652 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_850652 : Nat := 118140960795 + 850652 * 2 ^ 59
def prefixEnd_850652 : Nat := 4983230072969 + 3 ^ 40 * 850652 * 2
def baseEnd_850652 : Nat := 436793345708511053837929

theorem tailTrace_850652 : CollatzResearch.WordTrace tailWord_850652 prefixEnd_850652 436793345708511053837929 := by
  unfold tailWord_850652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15512913657120279320197105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20683884876160372426929473 15512913657120279320197105)
  ·
    refine ⟨11634685242840209490147829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15512913657120279320197105 11634685242840209490147829)
    ·
      refine ⟨1090751741516269639701359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11634685242840209490147829 1090751741516269639701359)
      ·
        refine ⟨1636127612274404459552039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090751741516269639701359 1636127612274404459552039)
        ·
          refine ⟨2454191418411606689328059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636127612274404459552039 2454191418411606689328059)
          ·
            refine ⟨3681287127617410033992089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454191418411606689328059 3681287127617410033992089)
            ·
              refine ⟨2760965345713057525494067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3681287127617410033992089 2760965345713057525494067)
              ·
                refine ⟨4141448018569586288241101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760965345713057525494067 4141448018569586288241101)
                ·
                  refine ⟨1553043006963594858090413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4141448018569586288241101 1553043006963594858090413)
                  ·
                    refine ⟨582391127611348071783905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553043006963594858090413 582391127611348071783905)
                    ·
                      refine ⟨436793345708511053837929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582391127611348071783905 436793345708511053837929)
                      ·
                        rfl

theorem cell23_850652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_850652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850652 prefixEnd_850652 := by exact prefixLift 850652
  have htrace : WordTrace (prefixWord ++ tailWord_850652) baseStart_850652 baseEnd_850652 := by
    simpa [prefixWord, tailWord_850652, baseEnd_850652] using wordTrace_append hprefix tailTrace_850652
  have hstable : (prefixWord ++ tailWord_850652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850652).length < 2 ^ (prefixWord ++ tailWord_850652).sum := by decide
  have hdescent : baseEnd_850652 < baseStart_850652 := by decide
  rcases family_descends (prefixWord ++ tailWord_850652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850678 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_850678 : Nat := 118140960795 + 850678 * 2 ^ 59
def prefixEnd_850678 : Nat := 4983230072969 + 3 ^ 40 * 850678 * 2
def baseEnd_850678 : Nat := 436806696205527952112809

theorem tailTrace_850678 : CollatzResearch.WordTrace tailWord_850678 prefixEnd_850678 436806696205527952112809 := by
  unfold tailWord_850678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939173475759147817552543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20684517074764243387227125 1939173475759147817552543)
  ·
    refine ⟨2908760213638721726328815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1939173475759147817552543 2908760213638721726328815)
    ·
      refine ⟨4363140320458082589493223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908760213638721726328815 4363140320458082589493223)
      ·
        refine ⟨6544710480687123884239835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363140320458082589493223 6544710480687123884239835)
        ·
          refine ⟨9817065721030685826359753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544710480687123884239835 9817065721030685826359753)
          ·
            refine ⟨7362799290773014369769815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9817065721030685826359753 7362799290773014369769815)
            ·
              refine ⟨11044198936159521554654723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362799290773014369769815 11044198936159521554654723)
              ·
                refine ⟨16566298404239282331982085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11044198936159521554654723 16566298404239282331982085)
                ·
                  refine ⟨3106180950794865437246641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16566298404239282331982085 3106180950794865437246641)
                  ·
                    refine ⟨2329635713096149077934981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3106180950794865437246641 2329635713096149077934981)
                    ·
                      refine ⟨436806696205527952112809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2329635713096149077934981 436806696205527952112809)
                      ·
                        rfl

theorem cell23_850678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_850678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850678 prefixEnd_850678 := by exact prefixLift 850678
  have htrace : WordTrace (prefixWord ++ tailWord_850678) baseStart_850678 baseEnd_850678 := by
    simpa [prefixWord, tailWord_850678, baseEnd_850678] using wordTrace_append hprefix tailTrace_850678
  have hstable : (prefixWord ++ tailWord_850678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850678).length < 2 ^ (prefixWord ++ tailWord_850678).sum := by decide
  have hdescent : baseEnd_850678 < baseStart_850678 := by decide
  rcases family_descends (prefixWord ++ tailWord_850678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850682 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2]
def baseStart_850682 : Nat := 118140960795 + 850682 * 2 ^ 59
def prefixEnd_850682 : Nat := 4983230072969 + 3 ^ 40 * 850682 * 2
def baseEnd_850682 : Nat := 436808750128145936462791

theorem tailTrace_850682 : CollatzResearch.WordTrace tailWord_850682 prefixEnd_850682 436808750128145936462791 := by
  unfold tailWord_850682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7756730376032968440996575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20684614336087915842657533 7756730376032968440996575)
  ·
    refine ⟨11635095564049452661494863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7756730376032968440996575 11635095564049452661494863)
    ·
      refine ⟨17452643346074178992242295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11635095564049452661494863 17452643346074178992242295)
      ·
        refine ⟨26178965019111268488363443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17452643346074178992242295 26178965019111268488363443)
        ·
          refine ⟨39268447528666902732545165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26178965019111268488363443 39268447528666902732545165)
          ·
            refine ⟨14725667823250088524704437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39268447528666902732545165 14725667823250088524704437)
            ·
              refine ⟨1380531358429695799191041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14725667823250088524704437 1380531358429695799191041)
              ·
                refine ⟨1035398518822271849393281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380531358429695799191041 1035398518822271849393281)
                ·
                  refine ⟨776548889116703887044961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1035398518822271849393281 776548889116703887044961)
                  ·
                    refine ⟨582411666837527915283721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 776548889116703887044961 582411666837527915283721)
                    ·
                      refine ⟨436808750128145936462791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582411666837527915283721 436808750128145936462791)
                      ·
                        rfl

theorem cell23_850682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_850682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850682 prefixEnd_850682 := by exact prefixLift 850682
  have htrace : WordTrace (prefixWord ++ tailWord_850682) baseStart_850682 baseEnd_850682 := by
    simpa [prefixWord, tailWord_850682, baseEnd_850682] using wordTrace_append hprefix tailTrace_850682
  have hstable : (prefixWord ++ tailWord_850682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850682).length < 2 ^ (prefixWord ++ tailWord_850682).sum := by decide
  have hdescent : baseEnd_850682 < baseStart_850682 := by decide
  rcases family_descends (prefixWord ++ tailWord_850682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850698 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_850698 : Nat := 118140960795 + 850698 * 2 ^ 59
def prefixEnd_850698 : Nat := 4983230072969 + 3 ^ 40 * 850698 * 2
def baseEnd_850698 : Nat := 436816965818617873862717

theorem tailTrace_850698 : CollatzResearch.WordTrace tailWord_850698 prefixEnd_850698 436816965818617873862717 := by
  unfold tailWord_850698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7756876268018477124142187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20685003381382605664379165 7756876268018477124142187)
  ·
    refine ⟨11635314402027715686213281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7756876268018477124142187 11635314402027715686213281)
    ·
      refine ⟨8726485801520786764659961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11635314402027715686213281 8726485801520786764659961)
      ·
        refine ⟨6544864351140590073494971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8726485801520786764659961 6544864351140590073494971)
        ·
          refine ⟨9817296526710885110242457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544864351140590073494971 9817296526710885110242457)
          ·
            refine ⟨7362972395033163832681843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9817296526710885110242457 7362972395033163832681843)
            ·
              refine ⟨11044458592549745749022765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362972395033163832681843 11044458592549745749022765)
              ·
                refine ⟨4141671972206154655883537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11044458592549745749022765 4141671972206154655883537)
                ·
                  refine ⟨3106253979154615991912653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4141671972206154655883537 3106253979154615991912653)
                  ·
                    refine ⟨1164845242182980996967245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3106253979154615991912653 1164845242182980996967245)
                    ·
                      refine ⟨436816965818617873862717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1164845242182980996967245 436816965818617873862717)
                      ·
                        rfl

theorem cell23_850698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_850698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850698 prefixEnd_850698 := by exact prefixLift 850698
  have htrace : WordTrace (prefixWord ++ tailWord_850698) baseStart_850698 baseEnd_850698 := by
    simpa [prefixWord, tailWord_850698, baseEnd_850698] using wordTrace_append hprefix tailTrace_850698
  have hstable : (prefixWord ++ tailWord_850698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850698).length < 2 ^ (prefixWord ++ tailWord_850698).sum := by decide
  have hdescent : baseEnd_850698 < baseStart_850698 := by decide
  rcases family_descends (prefixWord ++ tailWord_850698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850722 : List Nat := [3, 3, 1, 1, 2, 4, 1, 3, 5]
def baseStart_850722 : Nat := 118140960795 + 850722 * 2 ^ 59
def prefixEnd_850722 : Nat := 4983230072969 + 3 ^ 40 * 850722 * 2
def baseEnd_850722 : Nat := 48536587706036197773623

theorem tailTrace_850722 : CollatzResearch.WordTrace tailWord_850722 prefixEnd_850722 48536587706036197773623 := by
  unfold tailWord_850722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7757095105996740148860605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20685586949324640396961613 7757095105996740148860605)
  ·
    refine ⟨2908910664748777555822727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7757095105996740148860605 2908910664748777555822727)
    ·
      refine ⟨4363365997123166333734091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908910664748777555822727 4363365997123166333734091)
      ·
        refine ⟨6545048995684749500601137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363365997123166333734091 6545048995684749500601137)
        ·
          refine ⟨4908786746763562125450853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6545048995684749500601137 4908786746763562125450853)
          ·
            refine ⟨920397515018167898522035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4908786746763562125450853 920397515018167898522035)
            ·
              refine ⟨1380596272527251847783053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920397515018167898522035 1380596272527251847783053)
              ·
                refine ⟨517723602197719442918645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1380596272527251847783053 517723602197719442918645)
                ·
                  refine ⟨48536587706036197773623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517723602197719442918645 48536587706036197773623)
                  ·
                    rfl

theorem cell23_850722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_850722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850722 prefixEnd_850722 := by exact prefixLift 850722
  have htrace : WordTrace (prefixWord ++ tailWord_850722) baseStart_850722 baseEnd_850722 := by
    simpa [prefixWord, tailWord_850722, baseEnd_850722] using wordTrace_append hprefix tailTrace_850722
  have hstable : (prefixWord ++ tailWord_850722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850722).length < 2 ^ (prefixWord ++ tailWord_850722).sum := by decide
  have hdescent : baseEnd_850722 < baseStart_850722 := by decide
  rcases family_descends (prefixWord ++ tailWord_850722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850728 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_850728 : Nat := 118140960795 + 850728 * 2 ^ 59
def prefixEnd_850728 : Nat := 4983230072969 + 3 ^ 40 * 850728 * 2
def baseEnd_850728 : Nat := 436832370238252756487579

theorem tailTrace_850728 : CollatzResearch.WordTrace tailWord_850728 prefixEnd_850728 436832370238252756487579 := by
  unfold tailWord_850728
  simp only [CollatzResearch.WordTrace]
  refine ⟨15514299630982611810080419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20685732841310149080107225 15514299630982611810080419)
  ·
    refine ⟨23271449446473917715120629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15514299630982611810080419 23271449446473917715120629)
    ·
      refine ⟨2181698385606929785792559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23271449446473917715120629 2181698385606929785792559)
      ·
        refine ⟨3272547578410394678688839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181698385606929785792559 3272547578410394678688839)
        ·
          refine ⟨4908821367615592018033259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272547578410394678688839 4908821367615592018033259)
          ·
            refine ⟨7363232051423388027049889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908821367615592018033259 7363232051423388027049889)
            ·
              refine ⟨5522424038567541020287417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7363232051423388027049889 5522424038567541020287417)
              ·
                refine ⟨4141818028925655765215563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522424038567541020287417 4141818028925655765215563)
                ·
                  refine ⟨6212727043388483647823345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141818028925655765215563 6212727043388483647823345)
                  ·
                    refine ⟨4659545282541362735867509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6212727043388483647823345 4659545282541362735867509)
                    ·
                      refine ⟨436832370238252756487579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4659545282541362735867509 436832370238252756487579)
                      ·
                        rfl

theorem cell23_850728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_850728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850728 prefixEnd_850728 := by exact prefixLift 850728
  have htrace : WordTrace (prefixWord ++ tailWord_850728) baseStart_850728 baseEnd_850728 := by
    simpa [prefixWord, tailWord_850728, baseEnd_850728] using wordTrace_append hprefix tailTrace_850728
  have hstable : (prefixWord ++ tailWord_850728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850728).length < 2 ^ (prefixWord ++ tailWord_850728).sum := by decide
  have hdescent : baseEnd_850728 < baseStart_850728 := by decide
  rcases family_descends (prefixWord ++ tailWord_850728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850772 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_850772 : Nat := 118140960795 + 850772 * 2 ^ 59
def prefixEnd_850772 : Nat := 4983230072969 + 3 ^ 40 * 850772 * 2
def baseEnd_850772 : Nat := 436854963387050584337377

theorem tailTrace_850772 : CollatzResearch.WordTrace tailWord_850772 prefixEnd_850772 436854963387050584337377 := by
  unfold tailWord_850772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15515102036902909567381285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20686802715870546089841713 15515102036902909567381285)
  ·
    refine ⟨2909081631919295543883991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15515102036902909567381285 2909081631919295543883991)
    ·
      refine ⟨4363622447878943315825987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2909081631919295543883991 4363622447878943315825987)
      ·
        refine ⟨6545433671818414973738981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363622447878943315825987 6545433671818414973738981)
        ·
          refine ⟨1227268813465952807576059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6545433671818414973738981 1227268813465952807576059)
          ·
            refine ⟨1840903220198929211364089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227268813465952807576059 1840903220198929211364089)
            ·
              refine ⟨1380677415149196908523067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1840903220198929211364089 1380677415149196908523067)
              ·
                refine ⟨2071016122723795362784601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380677415149196908523067 2071016122723795362784601)
                ·
                  refine ⟨1553262092042846522088451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2071016122723795362784601 1553262092042846522088451)
                  ·
                    refine ⟨2329893138064269783132677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1553262092042846522088451 2329893138064269783132677)
                    ·
                      refine ⟨436854963387050584337377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2329893138064269783132677 436854963387050584337377)
                      ·
                        rfl

theorem cell23_850772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_850772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850772 prefixEnd_850772 := by exact prefixLift 850772
  have htrace : WordTrace (prefixWord ++ tailWord_850772) baseStart_850772 baseEnd_850772 := by
    simpa [prefixWord, tailWord_850772, baseEnd_850772] using wordTrace_append hprefix tailTrace_850772
  have hstable : (prefixWord ++ tailWord_850772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850772).length < 2 ^ (prefixWord ++ tailWord_850772).sum := by decide
  have hdescent : baseEnd_850772 < baseStart_850772 := by decide
  rcases family_descends (prefixWord ++ tailWord_850772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850775 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_850775 : Nat := 118140960795 + 850775 * 2 ^ 59
def prefixEnd_850775 : Nat := 4983230072969 + 3 ^ 40 * 850775 * 2
def baseEnd_850775 : Nat := 436856503829014072599863

theorem tailTrace_850775 : CollatzResearch.WordTrace tailWord_850775 prefixEnd_850775 436856503829014072599863 := by
  unfold tailWord_850775
  simp only [CollatzResearch.WordTrace]
  refine ⟨31030313492794950647121779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20686875661863300431414519 31030313492794950647121779)
  ·
    refine ⟨46545470239192425970682669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31030313492794950647121779 46545470239192425970682669)
    ·
      refine ⟨17454551339697159739006001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46545470239192425970682669 17454551339697159739006001)
      ·
        refine ⟨13090913504772869804254501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17454551339697159739006001 13090913504772869804254501)
        ·
          refine ⟨2454546282144913088297719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13090913504772869804254501 2454546282144913088297719)
          ·
            refine ⟨3681819423217369632446579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454546282144913088297719 3681819423217369632446579)
            ·
              refine ⟨5522729134826054448669869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3681819423217369632446579 5522729134826054448669869)
              ·
                refine ⟨2071023425559770418251201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5522729134826054448669869 2071023425559770418251201)
                ·
                  refine ⟨1553267569169827813688401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2071023425559770418251201 1553267569169827813688401)
                  ·
                    refine ⟨1164950676877370860266301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1553267569169827813688401 1164950676877370860266301)
                    ·
                      refine ⟨436856503829014072599863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1164950676877370860266301 436856503829014072599863)
                      ·
                        rfl

theorem cell23_850775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_850775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850775 prefixEnd_850775 := by exact prefixLift 850775
  have htrace : WordTrace (prefixWord ++ tailWord_850775) baseStart_850775 baseEnd_850775 := by
    simpa [prefixWord, tailWord_850775, baseEnd_850775] using wordTrace_append hprefix tailTrace_850775
  have hstable : (prefixWord ++ tailWord_850775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850775).length < 2 ^ (prefixWord ++ tailWord_850775).sum := by decide
  have hdescent : baseEnd_850775 < baseStart_850775 := by decide
  rcases family_descends (prefixWord ++ tailWord_850775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850815 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 4, 3, 2]
def baseStart_850815 : Nat := 118140960795 + 850815 * 2 ^ 59
def prefixEnd_850815 : Nat := 4983230072969 + 3 ^ 40 * 850815 * 2
def baseEnd_850815 : Nat := 436877043055193916099679

theorem tailTrace_850815 : CollatzResearch.WordTrace tailWord_850815 prefixEnd_850815 436877043055193916099679 := by
  unfold tailWord_850815
  simp only [CollatzResearch.WordTrace]
  refine ⟨31031772412650037478577899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20687848275100024985718599 31031772412650037478577899)
  ·
    refine ⟨46547658618975056217866849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31031772412650037478577899 46547658618975056217866849)
    ·
      refine ⟨34910743964231292163400137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46547658618975056217866849 34910743964231292163400137)
      ·
        refine ⟨26183057973173469122550103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34910743964231292163400137 26183057973173469122550103)
        ·
          refine ⟨39274586959760203683825155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26183057973173469122550103 39274586959760203683825155)
          ·
            refine ⟨58911880439640305525737733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39274586959760203683825155 58911880439640305525737733)
            ·
              refine ⟨11045977582432557286075825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58911880439640305525737733 11045977582432557286075825)
              ·
                refine ⟨8284483186824417964556869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11045977582432557286075825 8284483186824417964556869)
                ·
                  refine ⟨1553340597529578368354413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8284483186824417964556869 1553340597529578368354413)
                  ·
                    refine ⟨582502724073591888132905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553340597529578368354413 582502724073591888132905)
                    ·
                      refine ⟨436877043055193916099679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582502724073591888132905 436877043055193916099679)
                      ·
                        rfl

theorem cell23_850815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_850815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850815 prefixEnd_850815 := by exact prefixLift 850815
  have htrace : WordTrace (prefixWord ++ tailWord_850815) baseStart_850815 baseEnd_850815 := by
    simpa [prefixWord, tailWord_850815, baseEnd_850815] using wordTrace_append hprefix tailTrace_850815
  have hstable : (prefixWord ++ tailWord_850815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850815).length < 2 ^ (prefixWord ++ tailWord_850815).sum := by decide
  have hdescent : baseEnd_850815 < baseStart_850815 := by decide
  rcases family_descends (prefixWord ++ tailWord_850815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850839 : List Nat := [1, 1, 3, 3, 1, 2, 4, 3, 1, 1, 3]
def baseStart_850839 : Nat := 118140960795 + 850839 * 2 ^ 59
def prefixEnd_850839 : Nat := 4983230072969 + 3 ^ 40 * 850839 * 2
def baseEnd_850839 : Nat := 436889366590901822199569

theorem tailTrace_850839 : CollatzResearch.WordTrace tailWord_850839 prefixEnd_850839 436889366590901822199569 := by
  unfold tailWord_850839
  simp only [CollatzResearch.WordTrace]
  refine ⟨31032647764563089577451571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20688431843042059718301047 31032647764563089577451571)
  ·
    refine ⟨46548971646844634366177357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31032647764563089577451571 46548971646844634366177357)
    ·
      refine ⟨17455864367566737887316509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46548971646844634366177357 17455864367566737887316509)
      ·
        refine ⟨6545949137837526707743691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17455864367566737887316509 6545949137837526707743691)
        ·
          refine ⟨9818923706756290061615537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545949137837526707743691 9818923706756290061615537)
          ·
            refine ⟨7364192780067217546211653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818923706756290061615537 7364192780067217546211653)
            ·
              refine ⟨1380786146262603289914685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7364192780067217546211653 1380786146262603289914685)
              ·
                refine ⟨517794804848476233718007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1380786146262603289914685 517794804848476233718007)
                ·
                  refine ⟨776692207272714350577011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517794804848476233718007 776692207272714350577011)
                  ·
                    refine ⟨1165038310909071525865517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 776692207272714350577011 1165038310909071525865517)
                    ·
                      refine ⟨436889366590901822199569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1165038310909071525865517 436889366590901822199569)
                      ·
                        rfl

theorem cell23_850839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_850839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850839 prefixEnd_850839 := by exact prefixLift 850839
  have htrace : WordTrace (prefixWord ++ tailWord_850839) baseStart_850839 baseEnd_850839 := by
    simpa [prefixWord, tailWord_850839, baseEnd_850839] using wordTrace_append hprefix tailTrace_850839
  have hstable : (prefixWord ++ tailWord_850839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850839).length < 2 ^ (prefixWord ++ tailWord_850839).sum := by decide
  have hdescent : baseEnd_850839 < baseStart_850839 := by decide
  rcases family_descends (prefixWord ++ tailWord_850839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850842 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_850842 : Nat := 118140960795 + 850842 * 2 ^ 59
def prefixEnd_850842 : Nat := 4983230072969 + 3 ^ 40 * 850842 * 2
def baseEnd_850842 : Nat := 145630302344288436820685

theorem tailTrace_850842 : CollatzResearch.WordTrace tailWord_850842 prefixEnd_850842 145630302344288436820685 := by
  unfold tailWord_850842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758189295888055272452695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20688504789034814059873853 7758189295888055272452695)
  ·
    refine ⟨11637283943832082908679043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7758189295888055272452695 11637283943832082908679043)
    ·
      refine ⟨17455925915748124363018565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11637283943832082908679043 17455925915748124363018565)
      ·
        refine ⟨3272986109202773318065981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17455925915748124363018565 3272986109202773318065981)
        ·
          refine ⟨1227369790951039994274743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3272986109202773318065981 1227369790951039994274743)
          ·
            refine ⟨1841054686426559991412115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227369790951039994274743 1841054686426559991412115)
            ·
              refine ⟨2761582029639839987118173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841054686426559991412115 2761582029639839987118173)
              ·
                refine ⟨1035593261114939995169315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2761582029639839987118173 1035593261114939995169315)
                ·
                  refine ⟨1553389891672409992753973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035593261114939995169315 1553389891672409992753973)
                  ·
                    refine ⟨145630302344288436820685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1553389891672409992753973 145630302344288436820685)
                    ·
                      rfl

theorem cell23_850842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_850842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850842 prefixEnd_850842 := by exact prefixLift 850842
  have htrace : WordTrace (prefixWord ++ tailWord_850842) baseStart_850842 baseEnd_850842 := by
    simpa [prefixWord, tailWord_850842, baseEnd_850842] using wordTrace_append hprefix tailTrace_850842
  have hstable : (prefixWord ++ tailWord_850842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850842).length < 2 ^ (prefixWord ++ tailWord_850842).sum := by decide
  have hdescent : baseEnd_850842 < baseStart_850842 := by decide
  rcases family_descends (prefixWord ++ tailWord_850842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850902 : List Nat := [5, 2, 1, 1, 2, 3, 9]
def baseStart_850902 : Nat := 118140960795 + 850902 * 2 ^ 59
def prefixEnd_850902 : Nat := 4983230072969 + 3 ^ 40 * 850902 * 2
def baseEnd_850902 : Nat := 5394095257680679947059

theorem tailTrace_850902 : CollatzResearch.WordTrace tailWord_850902 prefixEnd_850902 5394095257680679947059 := by
  unfold tailWord_850902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939684097708428208562185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20689963708889900891329973 1939684097708428208562185)
  ·
    refine ⟨1454763073281321156421639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1939684097708428208562185 1454763073281321156421639)
    ·
      refine ⟨2182144609921981734632459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454763073281321156421639 2182144609921981734632459)
      ·
        refine ⟨3273216914882972601948689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182144609921981734632459 3273216914882972601948689)
        ·
          refine ⟨2454912686162229451461517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3273216914882972601948689 2454912686162229451461517)
          ·
            refine ⟨920592257310836044298069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454912686162229451461517 920592257310836044298069)
            ·
              refine ⟨5394095257680679947059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 920592257310836044298069 5394095257680679947059)
              ·
                rfl

theorem cell23_850902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 9].length) (baseStart_850902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850902 prefixEnd_850902 := by exact prefixLift 850902
  have htrace : WordTrace (prefixWord ++ tailWord_850902) baseStart_850902 baseEnd_850902 := by
    simpa [prefixWord, tailWord_850902, baseEnd_850902] using wordTrace_append hprefix tailTrace_850902
  have hstable : (prefixWord ++ tailWord_850902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850902).length < 2 ^ (prefixWord ++ tailWord_850902).sum := by decide
  have hdescent : baseEnd_850902 < baseStart_850902 := by decide
  rcases family_descends (prefixWord ++ tailWord_850902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850928 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 1, 8]
def baseStart_850928 : Nat := 118140960795 + 850928 * 2 ^ 59
def prefixEnd_850928 : Nat := 4983230072969 + 3 ^ 40 * 850928 * 2
def baseEnd_850928 : Nat := 145645022123050657995553

theorem tailTrace_850928 : CollatzResearch.WordTrace tailWord_850928 prefixEnd_850928 145645022123050657995553 := by
  unfold tailWord_850928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15517946930620328888720719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20690595907493771851627625 15517946930620328888720719)
  ·
    refine ⟨23276920395930493333081079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15517946930620328888720719 23276920395930493333081079)
    ·
      refine ⟨34915380593895739999621619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23276920395930493333081079 34915380593895739999621619)
      ·
        refine ⟨52373070890843609999432429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34915380593895739999621619 52373070890843609999432429)
        ·
          refine ⟨19639901584066353749787161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52373070890843609999432429 19639901584066353749787161)
          ·
            refine ⟨14729926188049765312340371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19639901584066353749787161 14729926188049765312340371)
            ·
              refine ⟨22094889282074647968510557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14729926188049765312340371 22094889282074647968510557)
              ·
                refine ⟨8285583480777992988191459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22094889282074647968510557 8285583480777992988191459)
                ·
                  refine ⟨12428375221166989482287189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8285583480777992988191459 12428375221166989482287189)
                  ·
                    refine ⟨145645022123050657995553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12428375221166989482287189 145645022123050657995553)
                    ·
                      rfl

theorem cell23_850928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_850928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850928 prefixEnd_850928 := by exact prefixLift 850928
  have htrace : WordTrace (prefixWord ++ tailWord_850928) baseStart_850928 baseEnd_850928 := by
    simpa [prefixWord, tailWord_850928, baseEnd_850928] using wordTrace_append hprefix tailTrace_850928
  have hstable : (prefixWord ++ tailWord_850928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850928).length < 2 ^ (prefixWord ++ tailWord_850928).sum := by decide
  have hdescent : baseEnd_850928 < baseStart_850928 := by decide
  rcases family_descends (prefixWord ++ tailWord_850928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850929 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_850929 : Nat := 118140960795 + 850929 * 2 ^ 59
def prefixEnd_850929 : Nat := 4983230072969 + 3 ^ 40 * 850929 * 2
def baseEnd_850929 : Nat := 436935579849806470074155

theorem tailTrace_850929 : CollatzResearch.WordTrace tailWord_850929 prefixEnd_850929 436935579849806470074155 := by
  unfold tailWord_850929
  simp only [CollatzResearch.WordTrace]
  refine ⟨31035930334237034948227841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20690620222824689965485227 31035930334237034948227841)
  ·
    refine ⟨23276947750677776211170881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31035930334237034948227841 23276947750677776211170881)
    ·
      refine ⟨17457710813008332158378161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23276947750677776211170881 17457710813008332158378161)
      ·
        refine ⟨13093283109756249118783621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17457710813008332158378161 13093283109756249118783621)
        ·
          refine ⟨2454990583079296709771929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13093283109756249118783621 2454990583079296709771929)
          ·
            refine ⟨1841242937309472532328947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454990583079296709771929 1841242937309472532328947)
            ·
              refine ⟨2761864405964208798493421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841242937309472532328947 2761864405964208798493421)
              ·
                refine ⟨1035699152236578299435033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2761864405964208798493421 1035699152236578299435033)
                ·
                  refine ⟨776774364177433724576275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1035699152236578299435033 776774364177433724576275)
                  ·
                    refine ⟨1165161546266150586864413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 776774364177433724576275 1165161546266150586864413)
                    ·
                      refine ⟨436935579849806470074155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1165161546266150586864413 436935579849806470074155)
                      ·
                        rfl

theorem cell23_850929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_850929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850929 prefixEnd_850929 := by exact prefixLift 850929
  have htrace : WordTrace (prefixWord ++ tailWord_850929) baseStart_850929 baseEnd_850929 := by
    simpa [prefixWord, tailWord_850929, baseEnd_850929] using wordTrace_append hprefix tailTrace_850929
  have hstable : (prefixWord ++ tailWord_850929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850929).length < 2 ^ (prefixWord ++ tailWord_850929).sum := by decide
  have hdescent : baseEnd_850929 < baseStart_850929 := by decide
  rcases family_descends (prefixWord ++ tailWord_850929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850933 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_850933 : Nat := 118140960795 + 850933 * 2 ^ 59
def prefixEnd_850933 : Nat := 4983230072969 + 3 ^ 40 * 850933 * 2
def baseEnd_850933 : Nat := 436937633772424454424137

theorem tailTrace_850933 : CollatzResearch.WordTrace tailWord_850933 prefixEnd_850933 436937633772424454424137 := by
  unfold tailWord_850933
  simp only [CollatzResearch.WordTrace]
  refine ⟨31036076226222543631373453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20690717484148362420915635 31036076226222543631373453)
  ·
    refine ⟨11638528584833453861765045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31036076226222543631373453 11638528584833453861765045)
    ·
      refine ⟨1091112054828136299540473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11638528584833453861765045 1091112054828136299540473)
      ·
        refine ⟨818334041121102224655355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1091112054828136299540473 818334041121102224655355)
        ·
          refine ⟨1227501061681653336983033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818334041121102224655355 1227501061681653336983033)
          ·
            refine ⟨920625796261240002737275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1227501061681653336983033 920625796261240002737275)
            ·
              refine ⟨1380938694391860004105913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920625796261240002737275 1380938694391860004105913)
              ·
                refine ⟨1035704020793895003079435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380938694391860004105913 1035704020793895003079435)
                ·
                  refine ⟨1553556031190842504619153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035704020793895003079435 1553556031190842504619153)
                  ·
                    refine ⟨1165167023393131878464365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1553556031190842504619153 1165167023393131878464365)
                    ·
                      refine ⟨436937633772424454424137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1165167023393131878464365 436937633772424454424137)
                      ·
                        rfl

theorem cell23_850933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_850933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850933 prefixEnd_850933 := by exact prefixLift 850933
  have htrace : WordTrace (prefixWord ++ tailWord_850933) baseStart_850933 baseEnd_850933 := by
    simpa [prefixWord, tailWord_850933, baseEnd_850933] using wordTrace_append hprefix tailTrace_850933
  have hstable : (prefixWord ++ tailWord_850933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850933).length < 2 ^ (prefixWord ++ tailWord_850933).sum := by decide
  have hdescent : baseEnd_850933 < baseStart_850933 := by decide
  rcases family_descends (prefixWord ++ tailWord_850933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850946 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_850946 : Nat := 118140960795 + 850946 * 2 ^ 59
def prefixEnd_850946 : Nat := 4983230072969 + 3 ^ 40 * 850946 * 2
def baseEnd_850946 : Nat := 436944309020932903561577

theorem tailTrace_850946 : CollatzResearch.WordTrace tailWord_850946 prefixEnd_850946 436944309020932903561577 := by
  unfold tailWord_850946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7759137593793861712899173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20691033583450297901064461 7759137593793861712899173)
  ·
    refine ⟨1454838298836349071168595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7759137593793861712899173 1454838298836349071168595)
    ·
      refine ⟨2182257448254523606752893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454838298836349071168595 2182257448254523606752893)
      ·
        refine ⟨818346543095446352532335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2182257448254523606752893 818346543095446352532335)
        ·
          refine ⟨1227519814643169528798503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818346543095446352532335 1227519814643169528798503)
          ·
            refine ⟨1841279721964754293197755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227519814643169528798503 1841279721964754293197755)
            ·
              refine ⟨2761919582947131439796633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841279721964754293197755 2761919582947131439796633)
              ·
                refine ⟨2071439687210348579847475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2761919582947131439796633 2071439687210348579847475)
                ·
                  refine ⟨3107159530815522869771213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071439687210348579847475 3107159530815522869771213)
                  ·
                    refine ⟨1165184824055821076164205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107159530815522869771213 1165184824055821076164205)
                    ·
                      refine ⟨436944309020932903561577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1165184824055821076164205 436944309020932903561577)
                      ·
                        rfl

theorem cell23_850946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_850946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850946 prefixEnd_850946 := by exact prefixLift 850946
  have htrace : WordTrace (prefixWord ++ tailWord_850946) baseStart_850946 baseEnd_850946 := by
    simpa [prefixWord, tailWord_850946, baseEnd_850946] using wordTrace_append hprefix tailTrace_850946
  have hstable : (prefixWord ++ tailWord_850946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850946).length < 2 ^ (prefixWord ++ tailWord_850946).sum := by decide
  have hdescent : baseEnd_850946 < baseStart_850946 := by decide
  rcases family_descends (prefixWord ++ tailWord_850946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850952 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_850952 : Nat := 118140960795 + 850952 * 2 ^ 59
def prefixEnd_850952 : Nat := 4983230072969 + 3 ^ 40 * 850952 * 2
def baseEnd_850952 : Nat := 436947389904859880086549

theorem tailTrace_850952 : CollatzResearch.WordTrace tailWord_850952 prefixEnd_850952 436947389904859880086549 := by
  unfold tailWord_850952
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518384606576854938157555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20691179475435806584210073 15518384606576854938157555)
  ·
    refine ⟨23277576909865282407236333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15518384606576854938157555 23277576909865282407236333)
    ·
      refine ⟨8729091341199480902713625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23277576909865282407236333 8729091341199480902713625)
      ·
        refine ⟨6546818505899610677035219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8729091341199480902713625 6546818505899610677035219)
        ·
          refine ⟨9820227758849416015552829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6546818505899610677035219 9820227758849416015552829)
          ·
            refine ⟨3682585409568531005832311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9820227758849416015552829 3682585409568531005832311)
            ·
              refine ⟨5523878114352796508748467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682585409568531005832311 5523878114352796508748467)
              ·
                refine ⟨8285817171529194763122701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523878114352796508748467 8285817171529194763122701)
                ·
                  refine ⟨3107181439323448036171013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8285817171529194763122701 3107181439323448036171013)
                  ·
                    refine ⟨582596519873146506782065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3107181439323448036171013 582596519873146506782065)
                    ·
                      refine ⟨436947389904859880086549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582596519873146506782065 436947389904859880086549)
                      ·
                        rfl

theorem cell23_850952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_850952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850952 prefixEnd_850952 := by exact prefixLift 850952
  have htrace : WordTrace (prefixWord ++ tailWord_850952) baseStart_850952 baseEnd_850952 := by
    simpa [prefixWord, tailWord_850952, baseEnd_850952] using wordTrace_append hprefix tailTrace_850952
  have hstable : (prefixWord ++ tailWord_850952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850952).length < 2 ^ (prefixWord ++ tailWord_850952).sum := by decide
  have hdescent : baseEnd_850952 < baseStart_850952 := by decide
  rcases family_descends (prefixWord ++ tailWord_850952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850955 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 5]
def baseStart_850955 : Nat := 118140960795 + 850955 * 2 ^ 59
def prefixEnd_850955 : Nat := 4983230072969 + 3 ^ 40 * 850955 * 2
def baseEnd_850955 : Nat := 436948930346823368349035

theorem tailTrace_850955 : CollatzResearch.WordTrace tailWord_850955 prefixEnd_850955 436948930346823368349035 := by
  unfold tailWord_850955
  simp only [CollatzResearch.WordTrace]
  refine ⟨31036878632142841388674319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20691252421428560925782879 31036878632142841388674319)
  ·
    refine ⟨46555317948214262083011479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31036878632142841388674319 46555317948214262083011479)
    ·
      refine ⟨69832976922321393124517219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46555317948214262083011479 69832976922321393124517219)
      ·
        refine ⟨104749465383482089686775829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69832976922321393124517219 104749465383482089686775829)
        ·
          refine ⟨4910131189850722954067617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104749465383482089686775829 4910131189850722954067617)
          ·
            refine ⟨3682598392388042215550713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4910131189850722954067617 3682598392388042215550713)
            ·
              refine ⟨2761948794291031661663035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3682598392388042215550713 2761948794291031661663035)
              ·
                refine ⟨4142923191436547492494553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761948794291031661663035 4142923191436547492494553)
                ·
                  refine ⟨3107192393577410619370915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4142923191436547492494553 3107192393577410619370915)
                  ·
                    refine ⟨4660788590366115929056373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3107192393577410619370915 4660788590366115929056373)
                    ·
                      refine ⟨436948930346823368349035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4660788590366115929056373 436948930346823368349035)
                      ·
                        rfl

theorem cell23_850955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_850955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850955 prefixEnd_850955 := by exact prefixLift 850955
  have htrace : WordTrace (prefixWord ++ tailWord_850955) baseStart_850955 baseEnd_850955 := by
    simpa [prefixWord, tailWord_850955, baseEnd_850955] using wordTrace_append hprefix tailTrace_850955
  have hstable : (prefixWord ++ tailWord_850955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850955).length < 2 ^ (prefixWord ++ tailWord_850955).sum := by decide
  have hdescent : baseEnd_850955 < baseStart_850955 := by decide
  rcases family_descends (prefixWord ++ tailWord_850955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850956 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 1, 3, 2]
def baseStart_850956 : Nat := 118140960795 + 850956 * 2 ^ 59
def prefixEnd_850956 : Nat := 4983230072969 + 3 ^ 40 * 850956 * 2
def baseEnd_850956 : Nat := 436949443827477864436531

theorem tailTrace_850956 : CollatzResearch.WordTrace tailWord_850956 prefixEnd_850956 436949443827477864436531 := by
  unfold tailWord_850956
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518457552569609279730361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20691276736759479039640481 15518457552569609279730361)
  ·
    refine ⟨11638843164427206959797771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15518457552569609279730361 11638843164427206959797771)
    ·
      refine ⟨17458264746640810439696657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11638843164427206959797771 17458264746640810439696657)
      ·
        refine ⟨13093698559980607829772493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17458264746640810439696657 13093698559980607829772493)
        ·
          refine ⟨4910136959992727936164685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13093698559980607829772493 4910136959992727936164685)
          ·
            refine ⟨1841301359997272976061757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4910136959992727936164685 1841301359997272976061757)
            ·
              refine ⟨690488009998977366023159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1841301359997272976061757 690488009998977366023159)
              ·
                refine ⟨1035732014998466049034739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690488009998977366023159 1035732014998466049034739)
                ·
                  refine ⟨1553598022497699073552109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035732014998466049034739 1553598022497699073552109)
                  ·
                    refine ⟨582599258436637152582041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553598022497699073552109 582599258436637152582041)
                    ·
                      refine ⟨436949443827477864436531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582599258436637152582041 436949443827477864436531)
                      ·
                        rfl

theorem cell23_850956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_850956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850956 prefixEnd_850956 := by exact prefixLift 850956
  have htrace : WordTrace (prefixWord ++ tailWord_850956) baseStart_850956 baseEnd_850956 := by
    simpa [prefixWord, tailWord_850956, baseEnd_850956] using wordTrace_append hprefix tailTrace_850956
  have hstable : (prefixWord ++ tailWord_850956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850956).length < 2 ^ (prefixWord ++ tailWord_850956).sum := by decide
  have hdescent : baseEnd_850956 < baseStart_850956 := by decide
  rcases family_descends (prefixWord ++ tailWord_850956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850969 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 2, 2, 2]
def baseStart_850969 : Nat := 118140960795 + 850969 * 2 ^ 59
def prefixEnd_850969 : Nat := 4983230072969 + 3 ^ 40 * 850969 * 2
def baseEnd_850969 : Nat := 436956119075986313573971

theorem tailTrace_850969 : CollatzResearch.WordTrace tailWord_850969 prefixEnd_850969 436956119075986313573971 := by
  unfold tailWord_850969
  simp only [CollatzResearch.WordTrace]
  refine ⟨31037389254092121779683961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20691592836061414519789307 31037389254092121779683961)
  ·
    refine ⟨23278041940569091334762971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31037389254092121779683961 23278041940569091334762971)
    ·
      refine ⟨34917062910853637002144457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23278041940569091334762971 34917062910853637002144457)
      ·
        refine ⟨26187797183140227751608343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34917062910853637002144457 26187797183140227751608343)
        ·
          refine ⟨39281695774710341627412515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26187797183140227751608343 39281695774710341627412515)
          ·
            refine ⟨58922543662065512441118773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39281695774710341627412515 58922543662065512441118773)
            ·
              refine ⟨5523988468318641791354885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58922543662065512441118773 5523988468318641791354885)
              ·
                refine ⟨1035747837809745335879041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5523988468318641791354885 1035747837809745335879041)
                ·
                  refine ⟨776810878357309001909281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1035747837809745335879041 776810878357309001909281)
                  ·
                    refine ⟨582608158767981751431961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 776810878357309001909281 582608158767981751431961)
                    ·
                      refine ⟨436956119075986313573971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582608158767981751431961 436956119075986313573971)
                      ·
                        rfl

theorem cell23_850969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_850969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850969 prefixEnd_850969 := by exact prefixLift 850969
  have htrace : WordTrace (prefixWord ++ tailWord_850969) baseStart_850969 baseEnd_850969 := by
    simpa [prefixWord, tailWord_850969, baseEnd_850969] using wordTrace_append hprefix tailTrace_850969
  have hstable : (prefixWord ++ tailWord_850969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850969).length < 2 ^ (prefixWord ++ tailWord_850969).sum := by decide
  have hdescent : baseEnd_850969 < baseStart_850969 := by decide
  rcases family_descends (prefixWord ++ tailWord_850969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850986 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_850986 : Nat := 118140960795 + 850986 * 2 ^ 59
def prefixEnd_850986 : Nat := 4983230072969 + 3 ^ 40 * 850986 * 2
def baseEnd_850986 : Nat := 436964848247112747061393

theorem tailTrace_850986 : CollatzResearch.WordTrace tailWord_850986 prefixEnd_850986 436964848247112747061393 := by
  unfold tailWord_850986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7759502323757633420763203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20692006196687022455368541 7759502323757633420763203)
  ·
    refine ⟨11639253485636450131144805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7759502323757633420763203 11639253485636450131144805)
    ·
      refine ⟨2182360028556834399589651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11639253485636450131144805 2182360028556834399589651)
      ·
        refine ⟨3273540042835251599384477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182360028556834399589651 3273540042835251599384477)
        ·
          refine ⟨1227577516063219349769179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3273540042835251599384477 1227577516063219349769179)
          ·
            refine ⟨1841366274094829024653769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227577516063219349769179 1841366274094829024653769)
            ·
              refine ⟨1381024705571121768490327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1841366274094829024653769 1381024705571121768490327)
              ·
                refine ⟨2071537058356682652735491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381024705571121768490327 2071537058356682652735491)
                ·
                  refine ⟨3107305587535023979103237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071537058356682652735491 3107305587535023979103237)
                  ·
                    refine ⟨582619797662816996081857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3107305587535023979103237 582619797662816996081857)
                    ·
                      refine ⟨436964848247112747061393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582619797662816996081857 436964848247112747061393)
                      ·
                        rfl

theorem cell23_850986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_850986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_850986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_850986 prefixEnd_850986 := by exact prefixLift 850986
  have htrace : WordTrace (prefixWord ++ tailWord_850986) baseStart_850986 baseEnd_850986 := by
    simpa [prefixWord, tailWord_850986, baseEnd_850986] using wordTrace_append hprefix tailTrace_850986
  have hstable : (prefixWord ++ tailWord_850986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850986).length < 2 ^ (prefixWord ++ tailWord_850986).sum := by decide
  have hdescent : baseEnd_850986 < baseStart_850986 := by decide
  rcases family_descends (prefixWord ++ tailWord_850986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851052 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_851052 : Nat := 118140960795 + 851052 * 2 ^ 59
def prefixEnd_851052 : Nat := 4983230072969 + 3 ^ 40 * 851052 * 2
def baseEnd_851052 : Nat := 145666245990103162945363

theorem tailTrace_851052 : CollatzResearch.WordTrace tailWord_851052 prefixEnd_851052 145666245990103162945363 := by
  unfold tailWord_851052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15520208256395713477477705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20693611008527617969970273 15520208256395713477477705)
  ·
    refine ⟨11640156192296785108108279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15520208256395713477477705 11640156192296785108108279)
    ·
      refine ⟨17460234288445177662162419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11640156192296785108108279 17460234288445177662162419)
      ·
        refine ⟨26190351432667766493243629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17460234288445177662162419 26190351432667766493243629)
        ·
          refine ⟨9821381787250412434966361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26190351432667766493243629 9821381787250412434966361)
          ·
            refine ⟨7366036340437809326224771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9821381787250412434966361 7366036340437809326224771)
            ·
              refine ⟨11049054510656713989337157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7366036340437809326224771 11049054510656713989337157)
              ·
                refine ⟨2071697720748133873000717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11049054510656713989337157 2071697720748133873000717)
                ·
                  refine ⟨776886645280550202375269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2071697720748133873000717 776886645280550202375269)
                  ·
                    refine ⟨145666245990103162945363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 776886645280550202375269 145666245990103162945363)
                    ·
                      rfl

theorem cell23_851052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_851052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851052 prefixEnd_851052 := by exact prefixLift 851052
  have htrace : WordTrace (prefixWord ++ tailWord_851052) baseStart_851052 baseEnd_851052 := by
    simpa [prefixWord, tailWord_851052, baseEnd_851052] using wordTrace_append hprefix tailTrace_851052
  have hstable : (prefixWord ++ tailWord_851052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851052).length < 2 ^ (prefixWord ++ tailWord_851052).sum := by decide
  have hdescent : baseEnd_851052 < baseStart_851052 := by decide
  rcases family_descends (prefixWord ++ tailWord_851052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
