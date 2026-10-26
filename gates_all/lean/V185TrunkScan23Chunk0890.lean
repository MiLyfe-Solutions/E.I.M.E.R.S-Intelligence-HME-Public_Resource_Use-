import V185TrunkScan23Chunk0889

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5268053 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_5268053 : Nat := 118140960795 + 5268053 * 2 ^ 59
def prefixEnd_5268053 : Nat := 4983230072969 + 3 ^ 40 * 5268053 * 2
def baseEnd_5268053 : Nat := 2705043302360182452110171

theorem tailTrace_5268053 : CollatzResearch.WordTrace tailWord_5268053 prefixEnd_5268053 2705043302360182452110171 := by
  unfold tailWord_5268053
  simp only [CollatzResearch.WordTrace]
  refine ⟨192141677983751167667792813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128094451989167445111861875 192141677983751167667792813)
  ·
    refine ⟨72053129243906687875422305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192141677983751167667792813 72053129243906687875422305)
    ·
      refine ⟨54039846932930015906566729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72053129243906687875422305 54039846932930015906566729)
      ·
        refine ⟨40529885199697511929925047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54039846932930015906566729 40529885199697511929925047)
        ·
          refine ⟨60794827799546267894887571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40529885199697511929925047 60794827799546267894887571)
          ·
            refine ⟨91192241699319401842331357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60794827799546267894887571 91192241699319401842331357)
            ·
              refine ⟨34197090637244775690874259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91192241699319401842331357 34197090637244775690874259)
              ·
                refine ⟨51295635955867163536311389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34197090637244775690874259 51295635955867163536311389)
                ·
                  refine ⟨19235863483450186326116771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51295635955867163536311389 19235863483450186326116771)
                  ·
                    refine ⟨28853795225175279489175157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19235863483450186326116771 28853795225175279489175157)
                    ·
                      refine ⟨2705043302360182452110171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28853795225175279489175157 2705043302360182452110171)
                      ·
                        rfl

theorem cell23_5268053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_5268053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268053 prefixEnd_5268053 := by exact prefixLift 5268053
  have htrace : WordTrace (prefixWord ++ tailWord_5268053) baseStart_5268053 baseEnd_5268053 := by
    simpa [prefixWord, tailWord_5268053, baseEnd_5268053] using wordTrace_append hprefix tailTrace_5268053
  have hstable : (prefixWord ++ tailWord_5268053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268053).length < 2 ^ (prefixWord ++ tailWord_5268053).sum := by decide
  have hdescent : baseEnd_5268053 < baseStart_5268053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268067 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 3, 2, 2]
def baseStart_5268067 : Nat := 118140960795 + 5268067 * 2 ^ 59
def prefixEnd_5268067 : Nat := 4983230072969 + 3 ^ 40 * 5268067 * 2
def baseEnd_5268067 : Nat := 2705050491089345397335107

theorem tailTrace_5268067 : CollatzResearch.WordTrace tailWord_5268067 prefixEnd_5268067 2705050491089345397335107 := by
  unfold tailWord_5268067
  simp only [CollatzResearch.WordTrace]
  refine ⟨192142188605700448058802455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128094792403800298705868303 192142188605700448058802455)
  ·
    refine ⟨288213282908550672088203683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192142188605700448058802455 288213282908550672088203683)
    ·
      refine ⟨432319924362826008132305525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288213282908550672088203683 432319924362826008132305525)
      ·
        refine ⟨40529992909014938262403643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 432319924362826008132305525 40529992909014938262403643)
        ·
          refine ⟨60794989363522407393605465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40529992909014938262403643 60794989363522407393605465)
          ·
            refine ⟨45596242022641805545204099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60794989363522407393605465 45596242022641805545204099)
            ·
              refine ⟨68394363033962708317806149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45596242022641805545204099 68394363033962708317806149)
              ·
                refine ⟨12823943068868007809588653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68394363033962708317806149 12823943068868007809588653)
                ·
                  refine ⟨4808978650825502928595745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12823943068868007809588653 4808978650825502928595745)
                  ·
                    refine ⟨3606733988119127196446809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4808978650825502928595745 3606733988119127196446809)
                    ·
                      refine ⟨2705050491089345397335107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606733988119127196446809 2705050491089345397335107)
                      ·
                        rfl

theorem cell23_5268067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_5268067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268067 prefixEnd_5268067 := by exact prefixLift 5268067
  have htrace : WordTrace (prefixWord ++ tailWord_5268067) baseStart_5268067 baseEnd_5268067 := by
    simpa [prefixWord, tailWord_5268067, baseEnd_5268067] using wordTrace_append hprefix tailTrace_5268067
  have hstable : (prefixWord ++ tailWord_5268067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268067).length < 2 ^ (prefixWord ++ tailWord_5268067).sum := by decide
  have hdescent : baseEnd_5268067 < baseStart_5268067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268103 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 2, 7]
def baseStart_5268103 : Nat := 118140960795 + 5268103 * 2 ^ 59
def prefixEnd_5268103 : Nat := 4983230072969 + 3 ^ 40 * 5268103 * 2
def baseEnd_5268103 : Nat := 901689658797635752161647

theorem tailTrace_5268103 : CollatzResearch.WordTrace tailWord_5268103 prefixEnd_5268103 901689658797635752161647 := by
  unfold tailWord_5268103
  simp only [CollatzResearch.WordTrace]
  refine ⟨192143501633570026207112963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128095667755713350804741975 192143501633570026207112963)
  ·
    refine ⟨288215252450355039310669445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192143501633570026207112963 288215252450355039310669445)
    ·
      refine ⟨54040359834441569870750521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288215252450355039310669445 54040359834441569870750521)
      ·
        refine ⟨40530269875831177403062891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54040359834441569870750521 40530269875831177403062891)
        ·
          refine ⟨60795404813746766104594337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40530269875831177403062891 60795404813746766104594337)
          ·
            refine ⟨45596553610310074578445753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60795404813746766104594337 45596553610310074578445753)
            ·
              refine ⟨34197415207732555933834315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45596553610310074578445753 34197415207732555933834315)
              ·
                refine ⟨51296122811598833900751473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34197415207732555933834315 51296122811598833900751473)
                ·
                  refine ⟨38472092108699125425563605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51296122811598833900751473 38472092108699125425563605)
                  ·
                    refine ⟨901689658797635752161647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38472092108699125425563605 901689658797635752161647)
                    ·
                      rfl

theorem cell23_5268103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_5268103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268103 prefixEnd_5268103 := by exact prefixLift 5268103
  have htrace : WordTrace (prefixWord ++ tailWord_5268103) baseStart_5268103 baseEnd_5268103 := by
    simpa [prefixWord, tailWord_5268103, baseEnd_5268103] using wordTrace_append hprefix tailTrace_5268103
  have hstable : (prefixWord ++ tailWord_5268103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268103).length < 2 ^ (prefixWord ++ tailWord_5268103).sum := by decide
  have hdescent : baseEnd_5268103 < baseStart_5268103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268133 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_5268133 : Nat := 118140960795 + 5268133 * 2 ^ 59
def prefixEnd_5268133 : Nat := 4983230072969 + 3 ^ 40 * 5268133 * 2
def baseEnd_5268133 : Nat := 901694793604180713036601

theorem tailTrace_5268133 : CollatzResearch.WordTrace tailWord_5268133 prefixEnd_5268133 901694793604180713036601 := by
  unfold tailWord_5268133
  simp only [CollatzResearch.WordTrace]
  refine ⟨192144595823461341330705053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128096397215640894220470035 192144595823461341330705053)
  ·
    refine ⟨72054223433798002999014395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192144595823461341330705053 72054223433798002999014395)
    ·
      refine ⟨108081335150697004498521593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72054223433798002999014395 108081335150697004498521593)
      ·
        refine ⟨81061001363022753373891195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108081335150697004498521593 81061001363022753373891195)
        ·
          refine ⟨121591502044534130060836793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81061001363022753373891195 121591502044534130060836793)
          ·
            refine ⟨91193626533400597545627595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121591502044534130060836793 91193626533400597545627595)
            ·
              refine ⟨136790439800100896318441393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91193626533400597545627595 136790439800100896318441393)
              ·
                refine ⟨102592829850075672238831045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136790439800100896318441393 102592829850075672238831045)
                ·
                  refine ⟨19236155596889188544780821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102592829850075672238831045 19236155596889188544780821)
                  ·
                    refine ⟨901694793604180713036601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19236155596889188544780821 901694793604180713036601)
                    ·
                      rfl

theorem cell23_5268133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_5268133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268133 prefixEnd_5268133 := by exact prefixLift 5268133
  have htrace : WordTrace (prefixWord ++ tailWord_5268133) baseStart_5268133 baseEnd_5268133 := by
    simpa [prefixWord, tailWord_5268133, baseEnd_5268133] using wordTrace_append hprefix tailTrace_5268133
  have hstable : (prefixWord ++ tailWord_5268133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268133).length < 2 ^ (prefixWord ++ tailWord_5268133).sum := by decide
  have hdescent : baseEnd_5268133 < baseStart_5268133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268138 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5268138 : Nat := 118140960795 + 5268138 * 2 ^ 59
def prefixEnd_5268138 : Nat := 4983230072969 + 3 ^ 40 * 5268138 * 2
def baseEnd_5268138 : Nat := 2705086948215814619547281

theorem tailTrace_5268138 : CollatzResearch.WordTrace tailWord_5268138 prefixEnd_5268138 2705086948215814619547281 := by
  unfold tailWord_5268138
  simp only [CollatzResearch.WordTrace]
  refine ⟨48036194547110806796159267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128096518792295484789758045 48036194547110806796159267)
  ·
    refine ⟨72054291820666210194238901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48036194547110806796159267 72054291820666210194238901)
    ·
      refine ⟨6755089858187457205709897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72054291820666210194238901 6755089858187457205709897)
      ·
        refine ⟨5066317393640592904282423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6755089858187457205709897 5066317393640592904282423)
        ·
          refine ⟨7599476090460889356423635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066317393640592904282423 7599476090460889356423635)
          ·
            refine ⟨11399214135691334034635453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7599476090460889356423635 11399214135691334034635453)
            ·
              refine ⟨4274705300884250262988295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11399214135691334034635453 4274705300884250262988295)
              ·
                refine ⟨6412057951326375394482443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4274705300884250262988295 6412057951326375394482443)
                ·
                  refine ⟨9618086926989563091723665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6412057951326375394482443 9618086926989563091723665)
                  ·
                    refine ⟨7213565195242172318792749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9618086926989563091723665 7213565195242172318792749)
                    ·
                      refine ⟨2705086948215814619547281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7213565195242172318792749 2705086948215814619547281)
                      ·
                        rfl

theorem cell23_5268138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5268138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268138 prefixEnd_5268138 := by exact prefixLift 5268138
  have htrace : WordTrace (prefixWord ++ tailWord_5268138) baseStart_5268138 baseEnd_5268138 := by
    simpa [prefixWord, tailWord_5268138, baseEnd_5268138] using wordTrace_append hprefix tailTrace_5268138
  have hstable : (prefixWord ++ tailWord_5268138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268138).length < 2 ^ (prefixWord ++ tailWord_5268138).sum := by decide
  have hdescent : baseEnd_5268138 < baseStart_5268138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268153 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5268153 : Nat := 118140960795 + 5268153 * 2 ^ 59
def prefixEnd_5268153 : Nat := 4983230072969 + 3 ^ 40 * 5268153 * 2
def baseEnd_5268153 : Nat := 2705094650425632060859711

theorem tailTrace_5268153 : CollatzResearch.WordTrace tailWord_5268153 prefixEnd_5268153 2705094650425632060859711 := by
  unfold tailWord_5268153
  simp only [CollatzResearch.WordTrace]
  refine ⟨192145325283388884746433113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128096883522259256497622075 192145325283388884746433113)
  ·
    refine ⟨144108993962541663559824835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192145325283388884746433113 144108993962541663559824835)
    ·
      refine ⟨216163490943812495339737253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144108993962541663559824835 216163490943812495339737253)
      ·
        refine ⟨40530654551964842876200735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216163490943812495339737253 40530654551964842876200735)
        ·
          refine ⟨60795981827947264314301103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40530654551964842876200735 60795981827947264314301103)
          ·
            refine ⟨91193972741920896471451655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60795981827947264314301103 91193972741920896471451655)
            ·
              refine ⟨136790959112881344707177483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91193972741920896471451655 136790959112881344707177483)
              ·
                refine ⟨205186438669322017060766225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136790959112881344707177483 205186438669322017060766225)
                ·
                  refine ⟨153889829001991512795574669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205186438669322017060766225 153889829001991512795574669)
                  ·
                    refine ⟨57708685875746817298340501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153889829001991512795574669 57708685875746817298340501)
                    ·
                      refine ⟨2705094650425632060859711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57708685875746817298340501 2705094650425632060859711)
                      ·
                        rfl

theorem cell23_5268153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5268153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268153 prefixEnd_5268153 := by exact prefixLift 5268153
  have htrace : WordTrace (prefixWord ++ tailWord_5268153) baseStart_5268153 baseEnd_5268153 := by
    simpa [prefixWord, tailWord_5268153, baseEnd_5268153] using wordTrace_append hprefix tailTrace_5268153
  have hstable : (prefixWord ++ tailWord_5268153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268153).length < 2 ^ (prefixWord ++ tailWord_5268153).sum := by decide
  have hdescent : baseEnd_5268153 < baseStart_5268153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268160 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 3]
def baseStart_5268160 : Nat := 118140960795 + 5268160 * 2 ^ 59
def prefixEnd_5268160 : Nat := 4983230072969 + 3 ^ 40 * 5268160 * 2
def baseEnd_5268160 : Nat := 2705098244790213533472179

theorem tailTrace_5268160 : CollatzResearch.WordTrace tailWord_5268160 prefixEnd_5268160 2705098244790213533472179 := by
  unfold tailWord_5268160
  simp only [CollatzResearch.WordTrace]
  refine ⟨96072790297181762470968967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128097053729575683294625289 96072790297181762470968967)
  ·
    refine ⟨144109185445772643706453451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96072790297181762470968967 144109185445772643706453451)
    ·
      refine ⟨216163778168658965559680177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144109185445772643706453451 216163778168658965559680177)
      ·
        refine ⟨162122833626494224169760133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216163778168658965559680177 162122833626494224169760133)
        ·
          refine ⟨30398031304967667031830025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162122833626494224169760133 30398031304967667031830025)
          ·
            refine ⟨22798523478725750273872519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30398031304967667031830025 22798523478725750273872519)
            ·
              refine ⟨34197785218088625410808779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22798523478725750273872519 34197785218088625410808779)
              ·
                refine ⟨51296677827132938116213169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34197785218088625410808779 51296677827132938116213169)
                ·
                  refine ⟨38472508370349703587159877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51296677827132938116213169 38472508370349703587159877)
                  ·
                    refine ⟨7213595319440569422592477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38472508370349703587159877 7213595319440569422592477)
                    ·
                      refine ⟨2705098244790213533472179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7213595319440569422592477 2705098244790213533472179)
                      ·
                        rfl

theorem cell23_5268160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_5268160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268160 prefixEnd_5268160 := by exact prefixLift 5268160
  have htrace : WordTrace (prefixWord ++ tailWord_5268160) baseStart_5268160 baseEnd_5268160 := by
    simpa [prefixWord, tailWord_5268160, baseEnd_5268160] using wordTrace_append hprefix tailTrace_5268160
  have hstable : (prefixWord ++ tailWord_5268160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268160).length < 2 ^ (prefixWord ++ tailWord_5268160).sum := by decide
  have hdescent : baseEnd_5268160 < baseStart_5268160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268170 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_5268170 : Nat := 118140960795 + 5268170 * 2 ^ 59
def prefixEnd_5268170 : Nat := 4983230072969 + 3 ^ 40 * 5268170 * 2
def baseEnd_5268170 : Nat := 2705103379596758494347133

theorem tailTrace_5268170 : CollatzResearch.WordTrace tailWord_5268170 prefixEnd_5268170 2705103379596758494347133 := by
  unfold tailWord_5268170
  simp only [CollatzResearch.WordTrace]
  refine ⟨48036486331081824162450491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128097296882884864433201309 48036486331081824162450491)
  ·
    refine ⟨72054729496622736243675737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48036486331081824162450491 72054729496622736243675737)
    ·
      refine ⟨54041047122467052182756803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72054729496622736243675737 54041047122467052182756803)
      ·
        refine ⟨81061570683700578274135205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54041047122467052182756803 81061570683700578274135205)
        ·
          refine ⟨15199044503193858426400351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81061570683700578274135205 15199044503193858426400351)
          ·
            refine ⟨22798566754790787639600527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15199044503193858426400351 22798566754790787639600527)
            ·
              refine ⟨34197850132186181459400791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22798566754790787639600527 34197850132186181459400791)
              ·
                refine ⟨51296775198279272189101187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34197850132186181459400791 51296775198279272189101187)
                ·
                  refine ⟨76945162797418908283651781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51296775198279272189101187 76945162797418908283651781)
                  ·
                    refine ⟨14427218024516045303184709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76945162797418908283651781 14427218024516045303184709)
                    ·
                      refine ⟨2705103379596758494347133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14427218024516045303184709 2705103379596758494347133)
                      ·
                        rfl

theorem cell23_5268170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_5268170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268170 prefixEnd_5268170 := by exact prefixLift 5268170
  have htrace : WordTrace (prefixWord ++ tailWord_5268170) baseStart_5268170 baseEnd_5268170 := by
    simpa [prefixWord, tailWord_5268170, baseEnd_5268170] using wordTrace_append hprefix tailTrace_5268170
  have hstable : (prefixWord ++ tailWord_5268170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268170).length < 2 ^ (prefixWord ++ tailWord_5268170).sum := by decide
  have hdescent : baseEnd_5268170 < baseStart_5268170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268174 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_5268174 : Nat := 118140960795 + 5268174 * 2 ^ 59
def prefixEnd_5268174 : Nat := 4983230072969 + 3 ^ 40 * 5268174 * 2
def baseEnd_5268174 : Nat := 2705105433519376478697115

theorem tailTrace_5268174 : CollatzResearch.WordTrace tailWord_5268174 prefixEnd_5268174 2705105433519376478697115 := by
  unfold tailWord_5268174
  simp only [CollatzResearch.WordTrace]
  refine ⟨24018261402039100666618447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128097394144208536888631717 24018261402039100666618447)
  ·
    refine ⟨36027392103058650999927671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24018261402039100666618447 36027392103058650999927671)
    ·
      refine ⟨54041088154587976499891507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36027392103058650999927671 54041088154587976499891507)
      ·
        refine ⟨81061632231881964749837261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54041088154587976499891507 81061632231881964749837261)
        ·
          refine ⟨30398112086955736781188973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81061632231881964749837261 30398112086955736781188973)
          ·
            refine ⟨11399292032608401292945865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30398112086955736781188973 11399292032608401292945865)
            ·
              refine ⟨8549469024456300969709399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11399292032608401292945865 8549469024456300969709399)
              ·
                refine ⟨12824203536684451454564099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8549469024456300969709399 12824203536684451454564099)
                ·
                  refine ⟨19236305305026677181846149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12824203536684451454564099 19236305305026677181846149)
                  ·
                    refine ⟨3606807244692501971596153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19236305305026677181846149 3606807244692501971596153)
                    ·
                      refine ⟨2705105433519376478697115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606807244692501971596153 2705105433519376478697115)
                      ·
                        rfl

theorem cell23_5268174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_5268174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268174 prefixEnd_5268174 := by exact prefixLift 5268174
  have htrace : WordTrace (prefixWord ++ tailWord_5268174) baseStart_5268174 baseEnd_5268174 := by
    simpa [prefixWord, tailWord_5268174, baseEnd_5268174] using wordTrace_append hprefix tailTrace_5268174
  have hstable : (prefixWord ++ tailWord_5268174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268174).length < 2 ^ (prefixWord ++ tailWord_5268174).sum := by decide
  have hdescent : baseEnd_5268174 < baseStart_5268174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268197 : List Nat := [1, 3, 1, 4, 1, 2, 1, 5, 5]
def baseStart_5268197 : Nat := 118140960795 + 5268197 * 2 ^ 59
def prefixEnd_5268197 : Nat := 4983230072969 + 3 ^ 40 * 5268197 * 2
def baseEnd_5268197 : Nat := 300568582619381098745501

theorem tailTrace_5268197 : CollatzResearch.WordTrace tailWord_5268197 prefixEnd_5268197 300568582619381098745501 := by
  unfold tailWord_5268197
  simp only [CollatzResearch.WordTrace]
  refine ⟨192146930095229480261034845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128097953396819653507356563 192146930095229480261034845)
  ·
    refine ⟨72055098785711055097888067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192146930095229480261034845 72055098785711055097888067)
    ·
      refine ⟨108082648178566582646832101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72055098785711055097888067 108082648178566582646832101)
      ·
        refine ⟨20265496533481234246281019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108082648178566582646832101 20265496533481234246281019)
        ·
          refine ⟨30398244800221851369421529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20265496533481234246281019 30398244800221851369421529)
          ·
            refine ⟨22798683600166388527066147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30398244800221851369421529 22798683600166388527066147)
            ·
              refine ⟨34198025400249582790599221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22798683600166388527066147 34198025400249582790599221)
              ·
                refine ⟨3206064881273398386618677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34198025400249582790599221 3206064881273398386618677)
                ·
                  refine ⟨300568582619381098745501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206064881273398386618677 300568582619381098745501)
                  ·
                    rfl

theorem cell23_5268197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_5268197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268197 prefixEnd_5268197 := by exact prefixLift 5268197
  have htrace : WordTrace (prefixWord ++ tailWord_5268197) baseStart_5268197 baseEnd_5268197 := by
    simpa [prefixWord, tailWord_5268197, baseEnd_5268197] using wordTrace_append hprefix tailTrace_5268197
  have hstable : (prefixWord ++ tailWord_5268197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268197).length < 2 ^ (prefixWord ++ tailWord_5268197).sum := by decide
  have hdescent : baseEnd_5268197 < baseStart_5268197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268287 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 6]
def baseStart_5268287 : Nat := 118140960795 + 5268287 * 2 ^ 59
def prefixEnd_5268287 : Nat := 4983230072969 + 3 ^ 40 * 5268287 * 2
def baseEnd_5268287 : Nat := 300573717425926059620455

theorem tailTrace_5268287 : CollatzResearch.WordTrace tailWord_5268287 prefixEnd_5268287 300573717425926059620455 := by
  unfold tailWord_5268287
  simp only [CollatzResearch.WordTrace]
  refine ⟨192150212664903425631811115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128100141776602283754540743 192150212664903425631811115)
  ·
    refine ⟨288225318997355138447716673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192150212664903425631811115 288225318997355138447716673)
    ·
      refine ⟨216168989248016353835787505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288225318997355138447716673 216168989248016353835787505)
      ·
        refine ⟨162126741936012265376840629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216168989248016353835787505 162126741936012265376840629)
        ·
          refine ⟨15199382056501149879078809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162126741936012265376840629 15199382056501149879078809)
          ·
            refine ⟨11399536542375862409309107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15199382056501149879078809 11399536542375862409309107)
            ·
              refine ⟨17099304813563793613963661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11399536542375862409309107 17099304813563793613963661)
              ·
                refine ⟨6412239305086422605236373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17099304813563793613963661 6412239305086422605236373)
                ·
                  refine ⟨300573717425926059620455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6412239305086422605236373 300573717425926059620455)
                  ·
                    rfl

theorem cell23_5268287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 6].length) (baseStart_5268287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268287 prefixEnd_5268287 := by exact prefixLift 5268287
  have htrace : WordTrace (prefixWord ++ tailWord_5268287) baseStart_5268287 baseEnd_5268287 := by
    simpa [prefixWord, tailWord_5268287, baseEnd_5268287] using wordTrace_append hprefix tailTrace_5268287
  have hstable : (prefixWord ++ tailWord_5268287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268287).length < 2 ^ (prefixWord ++ tailWord_5268287).sum := by decide
  have hdescent : baseEnd_5268287 < baseStart_5268287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268307 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 1, 5, 2]
def baseStart_5268307 : Nat := 118140960795 + 5268307 * 2 ^ 59
def prefixEnd_5268307 : Nat := 4983230072969 + 3 ^ 40 * 5268307 * 2
def baseEnd_5268307 : Nat := 2705173726446424458334003

theorem tailTrace_5268307 : CollatzResearch.WordTrace tailWord_5268307 prefixEnd_5268307 2705173726446424458334003 := by
  unfold tailWord_5268307
  simp only [CollatzResearch.WordTrace]
  refine ⟨192150942124830969047539175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128100628083220646031692783 192150942124830969047539175)
  ·
    refine ⟨288226413187246453571308763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192150942124830969047539175 288226413187246453571308763)
    ·
      refine ⟨432339619780869680356963145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288226413187246453571308763 432339619780869680356963145)
      ·
        refine ⟨324254714835652260267722359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432339619780869680356963145 324254714835652260267722359)
        ·
          refine ⟨486382072253478390401583539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324254714835652260267722359 486382072253478390401583539)
          ·
            refine ⟨729573108380217585602375309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486382072253478390401583539 729573108380217585602375309)
            ·
              refine ⟨273589915642581594600890741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 729573108380217585602375309 273589915642581594600890741)
              ·
                refine ⟨25649054591492024493833507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 273589915642581594600890741 25649054591492024493833507)
                ·
                  refine ⟨38473581887238036740750261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25649054591492024493833507 38473581887238036740750261)
                  ·
                    refine ⟨3606898301928565944445337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38473581887238036740750261 3606898301928565944445337)
                    ·
                      refine ⟨2705173726446424458334003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606898301928565944445337 2705173726446424458334003)
                      ·
                        rfl

theorem cell23_5268307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 5, 2].length) (baseStart_5268307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268307 prefixEnd_5268307 := by exact prefixLift 5268307
  have htrace : WordTrace (prefixWord ++ tailWord_5268307) baseStart_5268307 baseEnd_5268307 := by
    simpa [prefixWord, tailWord_5268307, baseEnd_5268307] using wordTrace_append hprefix tailTrace_5268307
  have hstable : (prefixWord ++ tailWord_5268307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268307).length < 2 ^ (prefixWord ++ tailWord_5268307).sum := by decide
  have hdescent : baseEnd_5268307 < baseStart_5268307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268337 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_5268337 : Nat := 118140960795 + 5268337 * 2 ^ 59
def prefixEnd_5268337 : Nat := 4983230072969 + 3 ^ 40 * 5268337 * 2
def baseEnd_5268337 : Nat := 2705189130866059340958865

theorem tailTrace_5268337 : CollatzResearch.WordTrace tailWord_5268337 prefixEnd_5268337 2705189130866059340958865 := by
  unfold tailWord_5268337
  simp only [CollatzResearch.WordTrace]
  refine ⟨192152036314722284171131265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128101357543148189447420843 192152036314722284171131265)
  ·
    refine ⟨144114027236041713128348449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192152036314722284171131265 144114027236041713128348449)
    ·
      refine ⟨108085520427031284846261337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144114027236041713128348449 108085520427031284846261337)
      ·
        refine ⟨81064140320273463634696003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108085520427031284846261337 81064140320273463634696003)
        ·
          refine ⟨121596210480410195452044005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81064140320273463634696003 121596210480410195452044005)
          ·
            refine ⟨22799289465076911647258251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121596210480410195452044005 22799289465076911647258251)
            ·
              refine ⟨34198934197615367470887377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22799289465076911647258251 34198934197615367470887377)
              ·
                refine ⟨25649200648211525603165533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34198934197615367470887377 25649200648211525603165533)
                ·
                  refine ⟨9618450243079322101187075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25649200648211525603165533 9618450243079322101187075)
                  ·
                    refine ⟨14427675364618983151780613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9618450243079322101187075 14427675364618983151780613)
                    ·
                      refine ⟨2705189130866059340958865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14427675364618983151780613 2705189130866059340958865)
                      ·
                        rfl

theorem cell23_5268337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_5268337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268337 prefixEnd_5268337 := by exact prefixLift 5268337
  have htrace : WordTrace (prefixWord ++ tailWord_5268337) baseStart_5268337 baseEnd_5268337 := by
    simpa [prefixWord, tailWord_5268337, baseEnd_5268337] using wordTrace_append hprefix tailTrace_5268337
  have hstable : (prefixWord ++ tailWord_5268337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268337).length < 2 ^ (prefixWord ++ tailWord_5268337).sum := by decide
  have hdescent : baseEnd_5268337 < baseStart_5268337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268387 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 3]
def baseStart_5268387 : Nat := 118140960795 + 5268387 * 2 ^ 59
def prefixEnd_5268387 : Nat := 4983230072969 + 3 ^ 40 * 5268387 * 2
def baseEnd_5268387 : Nat := 2705214804898784145333635

theorem tailTrace_5268387 : CollatzResearch.WordTrace tailWord_5268387 prefixEnd_5268387 2705214804898784145333635 := by
  unfold tailWord_5268387
  simp only [CollatzResearch.WordTrace]
  refine ⟨192153859964541142710451415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128102573309694095140300943 192153859964541142710451415)
  ·
    refine ⟨288230789946811714065677123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192153859964541142710451415 288230789946811714065677123)
    ·
      refine ⟨432346184920217571098515685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288230789946811714065677123 432346184920217571098515685)
      ·
        refine ⟨81064909672540794580971691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 432346184920217571098515685 81064909672540794580971691)
        ·
          refine ⟨121597364508811191871457537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81064909672540794580971691 121597364508811191871457537)
          ·
            refine ⟨91198023381608393903593153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121597364508811191871457537 91198023381608393903593153)
            ·
              refine ⟨68398517536206295427694865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91198023381608393903593153 68398517536206295427694865)
              ·
                refine ⟨51298888152154721570771149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68398517536206295427694865 51298888152154721570771149)
                ·
                  refine ⟨19237083057058020589039181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51298888152154721570771149 19237083057058020589039181)
                  ·
                    refine ⟨7213906146396757720889693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19237083057058020589039181 7213906146396757720889693)
                    ·
                      refine ⟨2705214804898784145333635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7213906146396757720889693 2705214804898784145333635)
                      ·
                        rfl

theorem cell23_5268387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_5268387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268387 prefixEnd_5268387 := by exact prefixLift 5268387
  have htrace : WordTrace (prefixWord ++ tailWord_5268387) baseStart_5268387 baseEnd_5268387 := by
    simpa [prefixWord, tailWord_5268387, baseEnd_5268387] using wordTrace_append hprefix tailTrace_5268387
  have hstable : (prefixWord ++ tailWord_5268387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268387).length < 2 ^ (prefixWord ++ tailWord_5268387).sum := by decide
  have hdescent : baseEnd_5268387 < baseStart_5268387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268388 : List Nat := [2, 3, 1, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_5268388 : Nat := 118140960795 + 5268388 * 2 ^ 59
def prefixEnd_5268388 : Nat := 4983230072969 + 3 ^ 40 * 5268388 * 2
def baseEnd_5268388 : Nat := 2705215318379438641421131

theorem tailTrace_5268388 : CollatzResearch.WordTrace tailWord_5268388 prefixEnd_5268388 2705215318379438641421131 := by
  unfold tailWord_5268388
  simp only [CollatzResearch.WordTrace]
  refine ⟨96076948218768759940618909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128102597625025013254158545 96076948218768759940618909)
  ·
    refine ⟨36028855582038284977732091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96076948218768759940618909 36028855582038284977732091)
    ·
      refine ⟨54043283373057427466598137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36028855582038284977732091 54043283373057427466598137)
      ·
        refine ⟨40532462529793070599948603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54043283373057427466598137 40532462529793070599948603)
        ·
          refine ⟨60798693794689605899922905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40532462529793070599948603 60798693794689605899922905)
          ·
            refine ⟨45599020346017204424942179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60798693794689605899922905 45599020346017204424942179)
            ·
              refine ⟨68398530519025806637413269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45599020346017204424942179 68398530519025806637413269)
              ·
                refine ⟨3206181118079334686128747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68398530519025806637413269 3206181118079334686128747)
                ·
                  refine ⟨4809271677119002029193121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206181118079334686128747 4809271677119002029193121)
                  ·
                    refine ⟨3606953757839251521894841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4809271677119002029193121 3606953757839251521894841)
                    ·
                      refine ⟨2705215318379438641421131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606953757839251521894841 2705215318379438641421131)
                      ·
                        rfl

theorem cell23_5268388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_5268388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268388 prefixEnd_5268388 := by exact prefixLift 5268388
  have htrace : WordTrace (prefixWord ++ tailWord_5268388) baseStart_5268388 baseEnd_5268388 := by
    simpa [prefixWord, tailWord_5268388, baseEnd_5268388] using wordTrace_append hprefix tailTrace_5268388
  have hstable : (prefixWord ++ tailWord_5268388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268388).length < 2 ^ (prefixWord ++ tailWord_5268388).sum := by decide
  have hdescent : baseEnd_5268388 < baseStart_5268388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268401 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_5268401 : Nat := 118140960795 + 5268401 * 2 ^ 59
def prefixEnd_5268401 : Nat := 4983230072969 + 3 ^ 40 * 5268401 * 2
def baseEnd_5268401 : Nat := 2705221993627947090558571

theorem tailTrace_5268401 : CollatzResearch.WordTrace tailWord_5268401 prefixEnd_5268401 2705221993627947090558571 := by
  unfold tailWord_5268401
  simp only [CollatzResearch.WordTrace]
  refine ⟨192154370586490423101461057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128102913724326948734307371 192154370586490423101461057)
  ·
    refine ⟨144115777939867817326095793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192154370586490423101461057 144115777939867817326095793)
    ·
      refine ⟨108086833454900862994571845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144115777939867817326095793 108086833454900862994571845)
      ·
        refine ⟨20266281272793911811482221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108086833454900862994571845 20266281272793911811482221)
        ·
          refine ⟨7599855477297716929305833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20266281272793911811482221 7599855477297716929305833)
          ·
            refine ⟨5699891607973287696979375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7599855477297716929305833 5699891607973287696979375)
            ·
              refine ⟨8549837411959931545469063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699891607973287696979375 8549837411959931545469063)
              ·
                refine ⟨12824756117939897318203595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8549837411959931545469063 12824756117939897318203595)
                ·
                  refine ⟨19237134176909845977305393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12824756117939897318203595 19237134176909845977305393)
                  ·
                    refine ⟨14427850632682384482979045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19237134176909845977305393 14427850632682384482979045)
                    ·
                      refine ⟨2705221993627947090558571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14427850632682384482979045 2705221993627947090558571)
                      ·
                        rfl

theorem cell23_5268401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_5268401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268401 prefixEnd_5268401 := by exact prefixLift 5268401
  have htrace : WordTrace (prefixWord ++ tailWord_5268401) baseStart_5268401 baseEnd_5268401 := by
    simpa [prefixWord, tailWord_5268401, baseEnd_5268401] using wordTrace_append hprefix tailTrace_5268401
  have hstable : (prefixWord ++ tailWord_5268401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268401).length < 2 ^ (prefixWord ++ tailWord_5268401).sum := by decide
  have hdescent : baseEnd_5268401 < baseStart_5268401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268431 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 1, 3, 2]
def baseStart_5268431 : Nat := 118140960795 + 5268431 * 2 ^ 59
def prefixEnd_5268431 : Nat := 4983230072969 + 3 ^ 40 * 5268431 * 2
def baseEnd_5268431 : Nat := 2705237398047581973183433

theorem tailTrace_5268431 : CollatzResearch.WordTrace tailWord_5268431 prefixEnd_5268431 2705237398047581973183433 := by
  unfold tailWord_5268431
  simp only [CollatzResearch.WordTrace]
  refine ⟨192155464776381738225053147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128103643184254492150035431 192155464776381738225053147)
  ·
    refine ⟨288233197164572607337579721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192155464776381738225053147 288233197164572607337579721)
    ·
      refine ⟨216174897873429455503184791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288233197164572607337579721 216174897873429455503184791)
      ·
        refine ⟨324262346810144183254777187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216174897873429455503184791 324262346810144183254777187)
        ·
          refine ⟨486393520215216274882165781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324262346810144183254777187 486393520215216274882165781)
          ·
            refine ⟨22799696260088262885101521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 486393520215216274882165781 22799696260088262885101521)
            ·
              refine ⟨17099772195066197163826141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22799696260088262885101521 17099772195066197163826141)
              ·
                refine ⟨6412414573149823936434803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17099772195066197163826141 6412414573149823936434803)
                ·
                  refine ⟨9618621859724735904652205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6412414573149823936434803 9618621859724735904652205)
                  ·
                    refine ⟨3606983197396775964244577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9618621859724735904652205 3606983197396775964244577)
                    ·
                      refine ⟨2705237398047581973183433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3606983197396775964244577 2705237398047581973183433)
                      ·
                        rfl

theorem cell23_5268431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 3, 2].length) (baseStart_5268431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268431 prefixEnd_5268431 := by exact prefixLift 5268431
  have htrace : WordTrace (prefixWord ++ tailWord_5268431) baseStart_5268431 baseEnd_5268431 := by
    simpa [prefixWord, tailWord_5268431, baseEnd_5268431] using wordTrace_append hprefix tailTrace_5268431
  have hstable : (prefixWord ++ tailWord_5268431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268431).length < 2 ^ (prefixWord ++ tailWord_5268431).sum := by decide
  have hdescent : baseEnd_5268431 < baseStart_5268431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268438 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_5268438 : Nat := 118140960795 + 5268438 * 2 ^ 59
def prefixEnd_5268438 : Nat := 4983230072969 + 3 ^ 40 * 5268438 * 2
def baseEnd_5268438 : Nat := 2705240992412163445795901

theorem tailTrace_5268438 : CollatzResearch.WordTrace tailWord_5268438 prefixEnd_5268438 2705240992412163445795901 := by
  unfold tailWord_5268438
  simp only [CollatzResearch.WordTrace]
  refine ⟨12009732505459773651284873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128103813391570918947038645 12009732505459773651284873)
  ·
    refine ⟨9007299379094830238463655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12009732505459773651284873 9007299379094830238463655)
    ·
      refine ⟨13510949068642245357695483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9007299379094830238463655 13510949068642245357695483)
      ·
        refine ⟨20266423602963368036543225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13510949068642245357695483 20266423602963368036543225)
        ·
          refine ⟨15199817702222526027407419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20266423602963368036543225 15199817702222526027407419)
          ·
            refine ⟨22799726553333789041111129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15199817702222526027407419 22799726553333789041111129)
            ·
              refine ⟨17099794915000341780833347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22799726553333789041111129 17099794915000341780833347)
              ·
                refine ⟨25649692372500512671250021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17099794915000341780833347 25649692372500512671250021)
                ·
                  refine ⟨4809317319843846125859379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25649692372500512671250021 4809317319843846125859379)
                  ·
                    refine ⟨7213975979765769188789069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4809317319843846125859379 7213975979765769188789069)
                    ·
                      refine ⟨2705240992412163445795901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7213975979765769188789069 2705240992412163445795901)
                      ·
                        rfl

theorem cell23_5268438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_5268438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268438 prefixEnd_5268438 := by exact prefixLift 5268438
  have htrace : WordTrace (prefixWord ++ tailWord_5268438) baseStart_5268438 baseEnd_5268438 := by
    simpa [prefixWord, tailWord_5268438, baseEnd_5268438] using wordTrace_append hprefix tailTrace_5268438
  have hstable : (prefixWord ++ tailWord_5268438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268438).length < 2 ^ (prefixWord ++ tailWord_5268438).sum := by decide
  have hdescent : baseEnd_5268438 < baseStart_5268438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268455 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_5268455 : Nat := 118140960795 + 5268455 * 2 ^ 59
def prefixEnd_5268455 : Nat := 4983230072969 + 3 ^ 40 * 5268455 * 2
def baseEnd_5268455 : Nat := 2705249721583289879283323

theorem tailTrace_5268455 : CollatzResearch.WordTrace tailWord_5268455 prefixEnd_5268455 2705249721583289879283323 := by
  unfold tailWord_5268455
  simp only [CollatzResearch.WordTrace]
  refine ⟨192156340128294790323926819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128104226752196526882617879 192156340128294790323926819)
  ·
    refine ⟨288234510192442185485890229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192156340128294790323926819 288234510192442185485890229)
    ·
      refine ⟨27021985330541454889302209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288234510192442185485890229 27021985330541454889302209)
      ·
        refine ⟨20266488997906091166976657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27021985330541454889302209 20266488997906091166976657)
        ·
          refine ⟨15199866748429568375232493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20266488997906091166976657 15199866748429568375232493)
          ·
            refine ⟨5699950030661088140712185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15199866748429568375232493 5699950030661088140712185)
            ·
              refine ⟨4274962522995816105534139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5699950030661088140712185 4274962522995816105534139)
              ·
                refine ⟨6412443784493724158301209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4274962522995816105534139 6412443784493724158301209)
                ·
                  refine ⟨4809332838370293118725907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6412443784493724158301209 4809332838370293118725907)
                  ·
                    refine ⟨7213999257555439678088861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4809332838370293118725907 7213999257555439678088861)
                    ·
                      refine ⟨2705249721583289879283323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7213999257555439678088861 2705249721583289879283323)
                      ·
                        rfl

theorem cell23_5268455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_5268455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268455 prefixEnd_5268455 := by exact prefixLift 5268455
  have htrace : WordTrace (prefixWord ++ tailWord_5268455) baseStart_5268455 baseEnd_5268455 := by
    simpa [prefixWord, tailWord_5268455, baseEnd_5268455] using wordTrace_append hprefix tailTrace_5268455
  have hstable : (prefixWord ++ tailWord_5268455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268455).length < 2 ^ (prefixWord ++ tailWord_5268455).sum := by decide
  have hdescent : baseEnd_5268455 < baseStart_5268455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268501 : List Nat := [1, 3, 2, 1, 4, 2, 1, 4, 5]
def baseStart_5268501 : Nat := 118140960795 + 5268501 * 2 ^ 59
def prefixEnd_5268501 : Nat := 4983230072969 + 3 ^ 40 * 5268501 * 2
def baseEnd_5268501 : Nat := 300585926854821855478679

theorem tailTrace_5268501 : CollatzResearch.WordTrace tailWord_5268501 prefixEnd_5268501 300585926854821855478679 := by
  unfold tailWord_5268501
  simp only [CollatzResearch.WordTrace]
  refine ⟨192158017886128140180101357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128105345257418760120067571 192158017886128140180101357)
  ·
    refine ⟨72059256707298052567538009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192158017886128140180101357 72059256707298052567538009)
    ·
      refine ⟨54044442530473539425653507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72059256707298052567538009 54044442530473539425653507)
      ·
        refine ⟨81066663795710309138480261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54044442530473539425653507 81066663795710309138480261)
        ·
          refine ⟨15199999461695682963465049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81066663795710309138480261 15199999461695682963465049)
          ·
            refine ⟨11399999596271762222598787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15199999461695682963465049 11399999596271762222598787)
            ·
              refine ⟨17099999394407643333898181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11399999596271762222598787 17099999394407643333898181)
              ·
                refine ⟨3206249886451433125105909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17099999394407643333898181 3206249886451433125105909)
                ·
                  refine ⟨300585926854821855478679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206249886451433125105909 300585926854821855478679)
                  ·
                    rfl

theorem cell23_5268501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_5268501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268501 prefixEnd_5268501 := by exact prefixLift 5268501
  have htrace : WordTrace (prefixWord ++ tailWord_5268501) baseStart_5268501 baseEnd_5268501 := by
    simpa [prefixWord, tailWord_5268501, baseEnd_5268501] using wordTrace_append hprefix tailTrace_5268501
  have hstable : (prefixWord ++ tailWord_5268501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268501).length < 2 ^ (prefixWord ++ tailWord_5268501).sum := by decide
  have hdescent : baseEnd_5268501 < baseStart_5268501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268544 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 5, 4]
def baseStart_5268544 : Nat := 118140960795 + 5268544 * 2 ^ 59
def prefixEnd_5268544 : Nat := 4983230072969 + 3 ^ 40 * 5268544 * 2
def baseEnd_5268544 : Nat := 901765140453846677023471

theorem tailTrace_5268544 : CollatzResearch.WordTrace tailWord_5268544 prefixEnd_5268544 901765140453846677023471 := by
  unfold tailWord_5268544
  simp only [CollatzResearch.WordTrace]
  refine ⟨96079793112486179261958343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128106390816648239015944457 96079793112486179261958343)
  ·
    refine ⟨144119689668729268892937515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96079793112486179261958343 144119689668729268892937515)
    ·
      refine ⟨216179534503093903339406273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144119689668729268892937515 216179534503093903339406273)
      ·
        refine ⟨162134650877320427504554705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216179534503093903339406273 162134650877320427504554705)
        ·
          refine ⟨121600988157990320628416029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162134650877320427504554705 121600988157990320628416029)
          ·
            refine ⟨45600370559246370235656011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121600988157990320628416029 45600370559246370235656011)
            ·
              refine ⟨68400555838869555353484017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45600370559246370235656011 68400555838869555353484017)
              ·
                refine ⟨51300416879152166515113013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68400555838869555353484017 51300416879152166515113013)
                ·
                  refine ⟨4809414082420515610791845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51300416879152166515113013 4809414082420515610791845)
                  ·
                    refine ⟨901765140453846677023471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4809414082420515610791845 901765140453846677023471)
                    ·
                      rfl

theorem cell23_5268544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 4].length) (baseStart_5268544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268544 prefixEnd_5268544 := by exact prefixLift 5268544
  have htrace : WordTrace (prefixWord ++ tailWord_5268544) baseStart_5268544 baseEnd_5268544 := by
    simpa [prefixWord, tailWord_5268544, baseEnd_5268544] using wordTrace_append hprefix tailTrace_5268544
  have hstable : (prefixWord ++ tailWord_5268544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268544).length < 2 ^ (prefixWord ++ tailWord_5268544).sum := by decide
  have hdescent : baseEnd_5268544 < baseStart_5268544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268547 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 6]
def baseStart_5268547 : Nat := 118140960795 + 5268547 * 2 ^ 59
def prefixEnd_5268547 : Nat := 4983230072969 + 3 ^ 40 * 5268547 * 2
def baseEnd_5268547 : Nat := 2705296961803503519332899

theorem tailTrace_5268547 : CollatzResearch.WordTrace tailWord_5268547 prefixEnd_5268547 2705296961803503519332899 := by
  unfold tailWord_5268547
  simp only [CollatzResearch.WordTrace]
  refine ⟨192159695643961490036275895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128106463762640993357517263 192159695643961490036275895)
  ·
    refine ⟨288239543465942235054413843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192159695643961490036275895 288239543465942235054413843)
    ·
      refine ⟨432359315198913352581620765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288239543465942235054413843 432359315198913352581620765)
      ·
        refine ⟨162134743199592507218107787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432359315198913352581620765 162134743199592507218107787)
        ·
          refine ⟨243202114799388760827161681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162134743199592507218107787 243202114799388760827161681)
          ·
            refine ⟨182401586099541570620371261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243202114799388760827161681 182401586099541570620371261)
            ·
              refine ⟨68400594787328088982639223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182401586099541570620371261 68400594787328088982639223)
              ·
                refine ⟨102600892180992133473958835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68400594787328088982639223 102600892180992133473958835)
                ·
                  refine ⟨153901338271488200210938253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102600892180992133473958835 153901338271488200210938253)
                  ·
                    refine ⟨57713001851808075079101845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153901338271488200210938253 57713001851808075079101845)
                    ·
                      refine ⟨2705296961803503519332899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57713001851808075079101845 2705296961803503519332899)
                      ·
                        rfl

theorem cell23_5268547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_5268547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268547 prefixEnd_5268547 := by exact prefixLift 5268547
  have htrace : WordTrace (prefixWord ++ tailWord_5268547) baseStart_5268547 baseEnd_5268547 := by
    simpa [prefixWord, tailWord_5268547, baseEnd_5268547] using wordTrace_append hprefix tailTrace_5268547
  have hstable : (prefixWord ++ tailWord_5268547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268547).length < 2 ^ (prefixWord ++ tailWord_5268547).sum := by decide
  have hdescent : baseEnd_5268547 < baseStart_5268547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268551 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_5268551 : Nat := 118140960795 + 5268551 * 2 ^ 59
def prefixEnd_5268551 : Nat := 4983230072969 + 3 ^ 40 * 5268551 * 2
def baseEnd_5268551 : Nat := 2705299015726121503682881

theorem tailTrace_5268551 : CollatzResearch.WordTrace tailWord_5268551 prefixEnd_5268551 2705299015726121503682881 := by
  unfold tailWord_5268551
  simp only [CollatzResearch.WordTrace]
  refine ⟨192159841535946998719421507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128106561023964665812947671 192159841535946998719421507)
  ·
    refine ⟨288239762303920498079132261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192159841535946998719421507 288239762303920498079132261)
    ·
      refine ⟨54044955431985093389837299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288239762303920498079132261 54044955431985093389837299)
      ·
        refine ⟨81067433147977640084755949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54044955431985093389837299 81067433147977640084755949)
        ·
          refine ⟨30400287430491615031783481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81067433147977640084755949 30400287430491615031783481)
          ·
            refine ⟨22800215572868711273837611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30400287430491615031783481 22800215572868711273837611)
            ·
              refine ⟨34200323359303066910756417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22800215572868711273837611 34200323359303066910756417)
              ·
                refine ⟨25650242519477300183067313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34200323359303066910756417 25650242519477300183067313)
                ·
                  refine ⟨19237681889607975137300485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25650242519477300183067313 19237681889607975137300485)
                  ·
                    refine ⟨3607065354301495338243841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19237681889607975137300485 3607065354301495338243841)
                    ·
                      refine ⟨2705299015726121503682881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607065354301495338243841 2705299015726121503682881)
                      ·
                        rfl

theorem cell23_5268551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_5268551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268551 prefixEnd_5268551 := by exact prefixLift 5268551
  have htrace : WordTrace (prefixWord ++ tailWord_5268551) baseStart_5268551 baseEnd_5268551 := by
    simpa [prefixWord, tailWord_5268551, baseEnd_5268551] using wordTrace_append hprefix tailTrace_5268551
  have hstable : (prefixWord ++ tailWord_5268551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268551).length < 2 ^ (prefixWord ++ tailWord_5268551).sum := by decide
  have hdescent : baseEnd_5268551 < baseStart_5268551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268578 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_5268578 : Nat := 118140960795 + 5268578 * 2 ^ 59
def prefixEnd_5268578 : Nat := 4983230072969 + 3 ^ 40 * 5268578 * 2
def baseEnd_5268578 : Nat := 901770959901264299348419

theorem tailTrace_5268578 : CollatzResearch.WordTrace tailWord_5268578 prefixEnd_5268578 901770959901264299348419 := by
  unfold tailWord_5268578
  simp only [CollatzResearch.WordTrace]
  refine ⟨48040206576712295582663597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128107217537899454887102925 48040206576712295582663597)
  ·
    refine ⟨18015077466267110843498849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48040206576712295582663597 18015077466267110843498849)
    ·
      refine ⟨13511308099700333132624137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18015077466267110843498849 13511308099700333132624137)
      ·
        refine ⟨10133481074775249849468103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13511308099700333132624137 10133481074775249849468103)
        ·
          refine ⟨15200221612162874774202155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10133481074775249849468103 15200221612162874774202155)
          ·
            refine ⟨22800332418244312161303233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15200221612162874774202155 22800332418244312161303233)
            ·
              refine ⟨17100249313683234120977425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22800332418244312161303233 17100249313683234120977425)
              ·
                refine ⟨12825186985262425590733069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17100249313683234120977425 12825186985262425590733069)
                ·
                  refine ⟨4809445119473409596524901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12825186985262425590733069 4809445119473409596524901)
                  ·
                    refine ⟨901770959901264299348419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4809445119473409596524901 901770959901264299348419)
                    ·
                      rfl

theorem cell23_5268578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_5268578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268578 prefixEnd_5268578 := by exact prefixLift 5268578
  have htrace : WordTrace (prefixWord ++ tailWord_5268578) baseStart_5268578 baseEnd_5268578 := by
    simpa [prefixWord, tailWord_5268578, baseEnd_5268578] using wordTrace_append hprefix tailTrace_5268578
  have hstable : (prefixWord ++ tailWord_5268578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268578).length < 2 ^ (prefixWord ++ tailWord_5268578).sum := by decide
  have hdescent : baseEnd_5268578 < baseStart_5268578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268587 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 4, 9]
def baseStart_5268587 : Nat := 118140960795 + 5268587 * 2 ^ 59
def prefixEnd_5268587 : Nat := 4983230072969 + 3 ^ 40 * 5268587 * 2
def baseEnd_5268587 : Nat := 901772500343227787610905

theorem tailTrace_5268587 : CollatzResearch.WordTrace tailWord_5268587 prefixEnd_5268587 901772500343227787610905 := by
  unfold tailWord_5268587
  simp only [CollatzResearch.WordTrace]
  refine ⟨192161154563816576867732015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128107436375877717911821343 192161154563816576867732015)
  ·
    refine ⟨288241731845724865301598023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192161154563816576867732015 288241731845724865301598023)
    ·
      refine ⟨432362597768587297952397035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288241731845724865301598023 432362597768587297952397035)
      ·
        refine ⟨648543896652880946928595553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432362597768587297952397035 648543896652880946928595553)
        ·
          refine ⟨486407922489660710196446665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648543896652880946928595553 486407922489660710196446665)
          ·
            refine ⟨364805941867245532647334999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486407922489660710196446665 364805941867245532647334999)
            ·
              refine ⟨547208912800868298971002499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364805941867245532647334999 547208912800868298971002499)
              ·
                refine ⟨820813369201302448456503749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547208912800868298971002499 820813369201302448456503749)
                ·
                  refine ⟨153902506725244209085594453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820813369201302448456503749 153902506725244209085594453)
                  ·
                    refine ⟨901772500343227787610905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 153902506725244209085594453 901772500343227787610905)
                    ·
                      rfl

theorem cell23_5268587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_5268587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268587 prefixEnd_5268587 := by exact prefixLift 5268587
  have htrace : WordTrace (prefixWord ++ tailWord_5268587) baseStart_5268587 baseEnd_5268587 := by
    simpa [prefixWord, tailWord_5268587, baseEnd_5268587] using wordTrace_append hprefix tailTrace_5268587
  have hstable : (prefixWord ++ tailWord_5268587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268587).length < 2 ^ (prefixWord ++ tailWord_5268587).sum := by decide
  have hdescent : baseEnd_5268587 < baseStart_5268587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268638 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_5268638 : Nat := 118140960795 + 5268638 * 2 ^ 59
def prefixEnd_5268638 : Nat := 4983230072969 + 3 ^ 40 * 5268638 * 2
def baseEnd_5268638 : Nat := 901781229514354221098327

theorem tailTrace_5268638 : CollatzResearch.WordTrace tailWord_5268638 prefixEnd_5268638 901781229514354221098327 := by
  unfold tailWord_5268638
  simp only [CollatzResearch.WordTrace]
  refine ⟨24020376835828976572229821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128108676457754541718559045 24020376835828976572229821)
  ·
    refine ⟨9007641313435866214586183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24020376835828976572229821 9007641313435866214586183)
    ·
      refine ⟨13511461970153799321879275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9007641313435866214586183 13511461970153799321879275)
      ·
        refine ⟨20267192955230698982818913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13511461970153799321879275 20267192955230698982818913)
        ·
          refine ⟨15200394716423024237114185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20267192955230698982818913 15200394716423024237114185)
          ·
            refine ⟨11400296037317268177835639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15200394716423024237114185 11400296037317268177835639)
            ·
              refine ⟨17100444055975902266753459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11400296037317268177835639 17100444055975902266753459)
              ·
                refine ⟨25650666083963853400130189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17100444055975902266753459 25650666083963853400130189)
                ·
                  refine ⟨9618999781486445025048821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25650666083963853400130189 9618999781486445025048821)
                  ·
                    refine ⟨901781229514354221098327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9618999781486445025048821 901781229514354221098327)
                    ·
                      rfl

theorem cell23_5268638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_5268638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268638 prefixEnd_5268638 := by exact prefixLift 5268638
  have htrace : WordTrace (prefixWord ++ tailWord_5268638) baseStart_5268638 baseEnd_5268638 := by
    simpa [prefixWord, tailWord_5268638, baseEnd_5268638] using wordTrace_append hprefix tailTrace_5268638
  have hstable : (prefixWord ++ tailWord_5268638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268638).length < 2 ^ (prefixWord ++ tailWord_5268638).sum := by decide
  have hdescent : baseEnd_5268638 < baseStart_5268638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268641 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5268641 : Nat := 118140960795 + 5268641 * 2 ^ 59
def prefixEnd_5268641 : Nat := 4983230072969 + 3 ^ 40 * 5268641 * 2
def baseEnd_5268641 : Nat := 2705345228985026151557467

theorem tailTrace_5268641 : CollatzResearch.WordTrace tailWord_5268641 prefixEnd_5268641 2705345228985026151557467 := by
  unfold tailWord_5268641
  simp only [CollatzResearch.WordTrace]
  refine ⟨192163124105620944090197777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128108749403747296060131851 192163124105620944090197777)
  ·
    refine ⟨144122343079215708067648333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192163124105620944090197777 144122343079215708067648333)
    ·
      refine ⟨54045878654705890525368125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144122343079215708067648333 54045878654705890525368125)
      ·
        refine ⟨20267204495514708947013047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54045878654705890525368125 20267204495514708947013047)
        ·
          refine ⟨30400806743272063420519571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20267204495514708947013047 30400806743272063420519571)
          ·
            refine ⟨45601210114908095130779357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30400806743272063420519571 45601210114908095130779357)
            ·
              refine ⟨17100453793090535674042259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45601210114908095130779357 17100453793090535674042259)
              ·
                refine ⟨25650680689635803511063389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17100453793090535674042259 25650680689635803511063389)
                ·
                  refine ⟨9619005258613426316648771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25650680689635803511063389 9619005258613426316648771)
                  ·
                    refine ⟨14428507887920139474973157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9619005258613426316648771 14428507887920139474973157)
                    ·
                      refine ⟨2705345228985026151557467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14428507887920139474973157 2705345228985026151557467)
                      ·
                        rfl

theorem cell23_5268641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5268641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268641 prefixEnd_5268641 := by exact prefixLift 5268641
  have htrace : WordTrace (prefixWord ++ tailWord_5268641) baseStart_5268641 baseEnd_5268641 := by
    simpa [prefixWord, tailWord_5268641, baseEnd_5268641] using wordTrace_append hprefix tailTrace_5268641
  have hstable : (prefixWord ++ tailWord_5268641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268641).length < 2 ^ (prefixWord ++ tailWord_5268641).sum := by decide
  have hdescent : baseEnd_5268641 < baseStart_5268641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268668 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_5268668 : Nat := 118140960795 + 5268668 * 2 ^ 59
def prefixEnd_5268668 : Nat := 4983230072969 + 3 ^ 40 * 5268668 * 2
def baseEnd_5268668 : Nat := 901786364320899181973281

theorem tailTrace_5268668 : CollatzResearch.WordTrace tailWord_5268668 prefixEnd_5268668 901786364320899181973281 := by
  unfold tailWord_5268668
  simp only [CollatzResearch.WordTrace]
  refine ⟨96082054438261563850715329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128109405917682085134287105 96082054438261563850715329)
  ·
    refine ⟨72061540828696172888036497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96082054438261563850715329 72061540828696172888036497)
    ·
      refine ⟨54046155621522129666027373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72061540828696172888036497 54046155621522129666027373)
      ·
        refine ⟨20267308358070798624760265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54046155621522129666027373 20267308358070798624760265)
        ·
          refine ⟨15200481268553098968570199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20267308358070798624760265 15200481268553098968570199)
          ·
            refine ⟨22800721902829648452855299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15200481268553098968570199 22800721902829648452855299)
            ·
              refine ⟨34201082854244472679282949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22800721902829648452855299 34201082854244472679282949)
              ·
                refine ⟨6412703035170838627365553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34201082854244472679282949 6412703035170838627365553)
                ·
                  refine ⟨4809527276378128970524165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6412703035170838627365553 4809527276378128970524165)
                  ·
                    refine ⟨901786364320899181973281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4809527276378128970524165 901786364320899181973281)
                    ·
                      rfl

theorem cell23_5268668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_5268668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268668 prefixEnd_5268668 := by exact prefixLift 5268668
  have htrace : WordTrace (prefixWord ++ tailWord_5268668) baseStart_5268668 baseEnd_5268668 := by
    simpa [prefixWord, tailWord_5268668, baseEnd_5268668] using wordTrace_append hprefix tailTrace_5268668
  have hstable : (prefixWord ++ tailWord_5268668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268668).length < 2 ^ (prefixWord ++ tailWord_5268668).sum := by decide
  have hdescent : baseEnd_5268668 < baseStart_5268668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268709 : List Nat := [1, 3, 1, 4, 3, 1, 2, 3, 1, 2, 2]
def baseStart_5268709 : Nat := 118140960795 + 5268709 * 2 ^ 59
def prefixEnd_5268709 : Nat := 4983230072969 + 3 ^ 40 * 5268709 * 2
def baseEnd_5268709 : Nat := 2705380145669531885507155

theorem tailTrace_5268709 : CollatzResearch.WordTrace tailWord_5268709 prefixEnd_5268709 2705380145669531885507155 := by
  unfold tailWord_5268709
  simp only [CollatzResearch.WordTrace]
  refine ⟨192165604269374591703673181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128110402846249727802448787 192165604269374591703673181)
  ·
    refine ⟨72062101601015471888877443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192165604269374591703673181 72062101601015471888877443)
    ·
      refine ⟨108093152401523207833316165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72062101601015471888877443 108093152401523207833316165)
      ·
        refine ⟨20267466075285601468746781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108093152401523207833316165 20267466075285601468746781)
        ·
          refine ⟨7600299778232100550780043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20267466075285601468746781 7600299778232100550780043)
          ·
            refine ⟨11400449667348150826170065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7600299778232100550780043 11400449667348150826170065)
            ·
              refine ⟨8550337250511113119627549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11400449667348150826170065 8550337250511113119627549)
              ·
                refine ⟨3206376468941667419860331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8550337250511113119627549 3206376468941667419860331)
                ·
                  refine ⟨4809564703412501129790497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206376468941667419860331 4809564703412501129790497)
                  ·
                    refine ⟨3607173527559375847342873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4809564703412501129790497 3607173527559375847342873)
                    ·
                      refine ⟨2705380145669531885507155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607173527559375847342873 2705380145669531885507155)
                      ·
                        rfl

theorem cell23_5268709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_5268709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268709 prefixEnd_5268709 := by exact prefixLift 5268709
  have htrace : WordTrace (prefixWord ++ tailWord_5268709) baseStart_5268709 baseEnd_5268709 := by
    simpa [prefixWord, tailWord_5268709, baseEnd_5268709] using wordTrace_append hprefix tailTrace_5268709
  have hstable : (prefixWord ++ tailWord_5268709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268709).length < 2 ^ (prefixWord ++ tailWord_5268709).sum := by decide
  have hdescent : baseEnd_5268709 < baseStart_5268709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268731 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 10, 2]
def baseStart_5268731 : Nat := 118140960795 + 5268731 * 2 ^ 59
def prefixEnd_5268731 : Nat := 4983230072969 + 3 ^ 40 * 5268731 * 2
def baseEnd_5268731 : Nat := 2705391442243930799432053

theorem tailTrace_5268731 : CollatzResearch.WordTrace tailWord_5268731 prefixEnd_5268731 2705391442243930799432053 := by
  unfold tailWord_5268731
  simp only [CollatzResearch.WordTrace]
  refine ⟨192166406675294889460974047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128110937783529926307316031 192166406675294889460974047)
  ·
    refine ⟨288249610012942334191461071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192166406675294889460974047 288249610012942334191461071)
    ·
      refine ⟨432374415019413501287191607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288249610012942334191461071 432374415019413501287191607)
      ·
        refine ⟨648561622529120251930787411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432374415019413501287191607 648561622529120251930787411)
        ·
          refine ⟨972842433793680377896181117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648561622529120251930787411 972842433793680377896181117)
          ·
            refine ⟨364815912672630141711067919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 972842433793680377896181117 364815912672630141711067919)
            ·
              refine ⟨547223869008945212566601879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364815912672630141711067919 547223869008945212566601879)
              ·
                refine ⟨820835803513417818849902819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547223869008945212566601879 820835803513417818849902819)
                ·
                  refine ⟨1231253705270126728274854229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820835803513417818849902819 1231253705270126728274854229)
                  ·
                    refine ⟨3607188589658574399242737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1231253705270126728274854229 3607188589658574399242737)
                    ·
                      refine ⟨2705391442243930799432053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607188589658574399242737 2705391442243930799432053)
                      ·
                        rfl

theorem cell23_5268731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 10, 2].length) (baseStart_5268731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268731 prefixEnd_5268731 := by exact prefixLift 5268731
  have htrace : WordTrace (prefixWord ++ tailWord_5268731) baseStart_5268731 baseEnd_5268731 := by
    simpa [prefixWord, tailWord_5268731, baseEnd_5268731] using wordTrace_append hprefix tailTrace_5268731
  have hstable : (prefixWord ++ tailWord_5268731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268731).length < 2 ^ (prefixWord ++ tailWord_5268731).sum := by decide
  have hdescent : baseEnd_5268731 < baseStart_5268731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268768 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5268768 : Nat := 118140960795 + 5268768 * 2 ^ 59
def prefixEnd_5268768 : Nat := 4983230072969 + 3 ^ 40 * 5268768 * 2
def baseEnd_5268768 : Nat := 2705410441028147154669383

theorem tailTrace_5268768 : CollatzResearch.WordTrace tailWord_5268768 prefixEnd_5268768 2705410441028147154669383 := by
  unfold tailWord_5268768
  simp only [CollatzResearch.WordTrace]
  refine ⟨96083878088080422390035479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128111837450773896520047305 96083878088080422390035479)
  ·
    refine ⟨144125817132120633585053219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96083878088080422390035479 144125817132120633585053219)
    ·
      refine ⟨216188725698180950377579829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144125817132120633585053219 216188725698180950377579829)
      ·
        refine ⟨20267693034204464097898109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216188725698180950377579829 20267693034204464097898109)
        ·
          refine ⟨7600384887826674036711791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20267693034204464097898109 7600384887826674036711791)
          ·
            refine ⟨11400577331740011055067687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7600384887826674036711791 11400577331740011055067687)
            ·
              refine ⟨17100865997610016582601531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11400577331740011055067687 17100865997610016582601531)
              ·
                refine ⟨25651298996415024873902297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17100865997610016582601531 25651298996415024873902297)
                ·
                  refine ⟨19238474247311268655426723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25651298996415024873902297 19238474247311268655426723)
                  ·
                    refine ⟨28857711370966902983140085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19238474247311268655426723 28857711370966902983140085)
                    ·
                      refine ⟨2705410441028147154669383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28857711370966902983140085 2705410441028147154669383)
                      ·
                        rfl

theorem cell23_5268768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5268768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268768 prefixEnd_5268768 := by exact prefixLift 5268768
  have htrace : WordTrace (prefixWord ++ tailWord_5268768) baseStart_5268768 baseEnd_5268768 := by
    simpa [prefixWord, tailWord_5268768, baseEnd_5268768] using wordTrace_append hprefix tailTrace_5268768
  have hstable : (prefixWord ++ tailWord_5268768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268768).length < 2 ^ (prefixWord ++ tailWord_5268768).sum := by decide
  have hdescent : baseEnd_5268768 < baseStart_5268768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268798 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_5268798 : Nat := 118140960795 + 5268798 * 2 ^ 59
def prefixEnd_5268798 : Nat := 4983230072969 + 3 ^ 40 * 5268798 * 2
def baseEnd_5268798 : Nat := 2705425845447782037294245

theorem tailTrace_5268798 : CollatzResearch.WordTrace tailWord_5268798 prefixEnd_5268798 2705425845447782037294245 := by
  unfold tailWord_5268798
  simp only [CollatzResearch.WordTrace]
  refine ⟨24021106295756519987957881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128112566910701439935775365 24021106295756519987957881)
  ·
    refine ⟨18015829721817389990968411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24021106295756519987957881 18015829721817389990968411)
    ·
      refine ⟨27023744582726084986452617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18015829721817389990968411 27023744582726084986452617)
      ·
        refine ⟨20267808437044563739839463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27023744582726084986452617 20267808437044563739839463)
        ·
          refine ⟨30401712655566845609759195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20267808437044563739839463 30401712655566845609759195)
          ·
            refine ⟨45602568983350268414638793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30401712655566845609759195 45602568983350268414638793)
            ·
              refine ⟨34201926737512701310979095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45602568983350268414638793 34201926737512701310979095)
              ·
                refine ⟨51302890106269051966468643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34201926737512701310979095 51302890106269051966468643)
                ·
                  refine ⟨76954335159403577949702965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51302890106269051966468643 76954335159403577949702965)
                  ·
                    refine ⟨7214468921194085432784653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76954335159403577949702965 7214468921194085432784653)
                    ·
                      refine ⟨2705425845447782037294245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7214468921194085432784653 2705425845447782037294245)
                      ·
                        rfl

theorem cell23_5268798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_5268798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268798 prefixEnd_5268798 := by exact prefixLift 5268798
  have htrace : WordTrace (prefixWord ++ tailWord_5268798) baseStart_5268798 baseEnd_5268798 := by
    simpa [prefixWord, tailWord_5268798, baseEnd_5268798] using wordTrace_append hprefix tailTrace_5268798
  have hstable : (prefixWord ++ tailWord_5268798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268798).length < 2 ^ (prefixWord ++ tailWord_5268798).sum := by decide
  have hdescent : baseEnd_5268798 < baseStart_5268798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268799 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 2, 2, 2]
def baseStart_5268799 : Nat := 118140960795 + 5268799 * 2 ^ 59
def prefixEnd_5268799 : Nat := 4983230072969 + 3 ^ 40 * 5268799 * 2
def baseEnd_5268799 : Nat := 2705426358928436533381741

theorem tailTrace_5268799 : CollatzResearch.WordTrace tailWord_5268799 prefixEnd_5268799 2705426358928436533381741 := by
  unfold tailWord_5268799
  simp only [CollatzResearch.WordTrace]
  refine ⟨192168886839048537074449451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128112591226032358049632967 192168886839048537074449451)
  ·
    refine ⟨288253330258572805611674177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192168886839048537074449451 288253330258572805611674177)
    ·
      refine ⟨216189997693929604208755633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288253330258572805611674177 216189997693929604208755633)
      ·
        refine ⟨162142498270447203156566725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216189997693929604208755633 162142498270447203156566725)
        ·
          refine ⟨30401718425708850591856261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162142498270447203156566725 30401718425708850591856261)
          ·
            refine ⟨5700322204820409485973049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30401718425708850591856261 5700322204820409485973049)
            ·
              refine ⟨4275241653615307114479787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5700322204820409485973049 4275241653615307114479787)
              ·
                refine ⟨6412862480422960671719681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275241653615307114479787 6412862480422960671719681)
                ·
                  refine ⟨4809646860317220503789761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6412862480422960671719681 4809646860317220503789761)
                  ·
                    refine ⟨3607235145237915377842321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4809646860317220503789761 3607235145237915377842321)
                    ·
                      refine ⟨2705426358928436533381741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607235145237915377842321 2705426358928436533381741)
                      ·
                        rfl

theorem cell23_5268799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_5268799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268799 prefixEnd_5268799 := by exact prefixLift 5268799
  have htrace : WordTrace (prefixWord ++ tailWord_5268799) baseStart_5268799 baseEnd_5268799 := by
    simpa [prefixWord, tailWord_5268799, baseEnd_5268799] using wordTrace_append hprefix tailTrace_5268799
  have hstable : (prefixWord ++ tailWord_5268799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268799).length < 2 ^ (prefixWord ++ tailWord_5268799).sum := by decide
  have hdescent : baseEnd_5268799 < baseStart_5268799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268839 : List Nat := [1, 1, 5, 1, 5, 1, 2, 2, 5]
def baseStart_5268839 : Nat := 118140960795 + 5268839 * 2 ^ 59
def prefixEnd_5268839 : Nat := 4983230072969 + 3 ^ 40 * 5268839 * 2
def baseEnd_5268839 : Nat := 300605210906068486320173

theorem tailTrace_5268839 : CollatzResearch.WordTrace tailWord_5268839 prefixEnd_5268839 300605210906068486320173 := by
  unfold tailWord_5268839
  simp only [CollatzResearch.WordTrace]
  refine ⟨192170345758903623905905571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128113563839269082603937047 192170345758903623905905571)
  ·
    refine ⟨288255518638355435858858357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192170345758903623905905571 288255518638355435858858357)
    ·
      refine ⟨27023954872345822111767971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288255518638355435858858357 27023954872345822111767971)
      ·
        refine ⟨40535932308518733167651957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27023954872345822111767971 40535932308518733167651957)
        ·
          refine ⟨3800243653923631234467371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40535932308518733167651957 3800243653923631234467371)
          ·
            refine ⟨5700365480885446851701057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800243653923631234467371 5700365480885446851701057)
            ·
              refine ⟨4275274110664085138775793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5700365480885446851701057 4275274110664085138775793)
              ·
                refine ⟨3206455582998063854081845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4275274110664085138775793 3206455582998063854081845)
                ·
                  refine ⟨300605210906068486320173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206455582998063854081845 300605210906068486320173)
                  ·
                    rfl

theorem cell23_5268839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 5].length) (baseStart_5268839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268839 prefixEnd_5268839 := by exact prefixLift 5268839
  have htrace : WordTrace (prefixWord ++ tailWord_5268839) baseStart_5268839 baseEnd_5268839 := by
    simpa [prefixWord, tailWord_5268839, baseEnd_5268839] using wordTrace_append hprefix tailTrace_5268839
  have hstable : (prefixWord ++ tailWord_5268839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268839).length < 2 ^ (prefixWord ++ tailWord_5268839).sum := by decide
  have hdescent : baseEnd_5268839 < baseStart_5268839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268848 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 3, 4]
def baseStart_5268848 : Nat := 118140960795 + 5268848 * 2 ^ 59
def prefixEnd_5268848 : Nat := 4983230072969 + 3 ^ 40 * 5268848 * 2
def baseEnd_5268848 : Nat := 901817173160168947223005

theorem tailTrace_5268848 : CollatzResearch.WordTrace tailWord_5268848 prefixEnd_5268848 901817173160168947223005 := by
  unfold tailWord_5268848
  simp only [CollatzResearch.WordTrace]
  refine ⟨96085337007935509221491599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128113782677247345628655465 96085337007935509221491599)
  ·
    refine ⟨144128005511903263832237399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96085337007935509221491599 144128005511903263832237399)
    ·
      refine ⟨216192008267854895748356099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144128005511903263832237399 216192008267854895748356099)
      ·
        refine ⟨324288012401782343622534149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216192008267854895748356099 324288012401782343622534149)
        ·
          refine ⟨60804002325334189429225153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 324288012401782343622534149 60804002325334189429225153)
          ·
            refine ⟨45603001744000642071918865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60804002325334189429225153 45603001744000642071918865)
            ·
              refine ⟨34202251308000481553939149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45603001744000642071918865 34202251308000481553939149)
              ·
                refine ⟨12825844240500180582727181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34202251308000481553939149 12825844240500180582727181)
                ·
                  refine ⟨4809691590187567718522693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12825844240500180582727181 4809691590187567718522693)
                  ·
                    refine ⟨901817173160168947223005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4809691590187567718522693 901817173160168947223005)
                    ·
                      rfl

theorem cell23_5268848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 4].length) (baseStart_5268848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268848 prefixEnd_5268848 := by exact prefixLift 5268848
  have htrace : WordTrace (prefixWord ++ tailWord_5268848) baseStart_5268848 baseEnd_5268848 := by
    simpa [prefixWord, tailWord_5268848, baseEnd_5268848] using wordTrace_append hprefix tailTrace_5268848
  have hstable : (prefixWord ++ tailWord_5268848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268848).length < 2 ^ (prefixWord ++ tailWord_5268848).sum := by decide
  have hdescent : baseEnd_5268848 < baseStart_5268848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268895 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 6]
def baseStart_5268895 : Nat := 118140960795 + 5268895 * 2 ^ 59
def prefixEnd_5268895 : Nat := 4983230072969 + 3 ^ 40 * 5268895 * 2
def baseEnd_5268895 : Nat := 300608405896807573086811

theorem tailTrace_5268895 : CollatzResearch.WordTrace tailWord_5268895 prefixEnd_5268895 300608405896807573086811 := by
  unfold tailWord_5268895
  simp only [CollatzResearch.WordTrace]
  refine ⟨192172388246700745469944139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128114925497800496979962759 192172388246700745469944139)
  ·
    refine ⟨288258582370051118204916209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192172388246700745469944139 288258582370051118204916209)
    ·
      refine ⟨216193936777538338653687157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288258582370051118204916209 216193936777538338653687157)
      ·
        refine ⟨20268181572894219248783171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216193936777538338653687157 20268181572894219248783171)
        ·
          refine ⟨30402272359341328873174757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20268181572894219248783171 30402272359341328873174757)
          ·
            refine ⟨5700426067376499163720267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30402272359341328873174757 5700426067376499163720267)
            ·
              refine ⟨8550639101064748745580401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700426067376499163720267 8550639101064748745580401)
              ·
                refine ⟨6412979325798561559185301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8550639101064748745580401 6412979325798561559185301)
                ·
                  refine ⟨300608405896807573086811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6412979325798561559185301 300608405896807573086811)
                  ·
                    rfl

theorem cell23_5268895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 6].length) (baseStart_5268895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268895 prefixEnd_5268895 := by exact prefixLift 5268895
  have htrace : WordTrace (prefixWord ++ tailWord_5268895) baseStart_5268895 baseEnd_5268895 := by
    simpa [prefixWord, tailWord_5268895, baseEnd_5268895] using wordTrace_append hprefix tailTrace_5268895
  have hstable : (prefixWord ++ tailWord_5268895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268895).length < 2 ^ (prefixWord ++ tailWord_5268895).sum := by decide
  have hdescent : baseEnd_5268895 < baseStart_5268895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268898 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5268898 : Nat := 118140960795 + 5268898 * 2 ^ 59
def prefixEnd_5268898 : Nat := 4983230072969 + 3 ^ 40 * 5268898 * 2
def baseEnd_5268898 : Nat := 2705477193513231646043785

theorem tailTrace_5268898 : CollatzResearch.WordTrace tailWord_5268898 prefixEnd_5268898 2705477193513231646043785 := by
  unfold tailWord_5268898
  simp only [CollatzResearch.WordTrace]
  refine ⟨48043124416422469245575837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128114998443793251321535565 48043124416422469245575837)
  ·
    refine ⟨18016171656158425967090939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48043124416422469245575837 18016171656158425967090939)
    ·
      refine ⟨27024257484237638950636409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18016171656158425967090939 27024257484237638950636409)
      ·
        refine ⟨20268193113178229212977307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27024257484237638950636409 20268193113178229212977307)
        ·
          refine ⟨30402289669767343819465961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20268193113178229212977307 30402289669767343819465961)
          ·
            refine ⟨22801717252325507864599471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30402289669767343819465961 22801717252325507864599471)
            ·
              refine ⟨34202575878488261796899207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22801717252325507864599471 34202575878488261796899207)
              ·
                refine ⟨51303863817732392695348811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34202575878488261796899207 51303863817732392695348811)
                ·
                  refine ⟨76955795726598589043023217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51303863817732392695348811 76955795726598589043023217)
                  ·
                    refine ⟨57716846794948941782267413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76955795726598589043023217 57716846794948941782267413)
                    ·
                      refine ⟨2705477193513231646043785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57716846794948941782267413 2705477193513231646043785)
                      ·
                        rfl

theorem cell23_5268898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5268898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268898 prefixEnd_5268898 := by exact prefixLift 5268898
  have htrace : WordTrace (prefixWord ++ tailWord_5268898) baseStart_5268898 baseEnd_5268898 := by
    simpa [prefixWord, tailWord_5268898, baseEnd_5268898] using wordTrace_append hprefix tailTrace_5268898
  have hstable : (prefixWord ++ tailWord_5268898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268898).length < 2 ^ (prefixWord ++ tailWord_5268898).sum := by decide
  have hdescent : baseEnd_5268898 < baseStart_5268898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268901 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_5268901 : Nat := 118140960795 + 5268901 * 2 ^ 59
def prefixEnd_5268901 : Nat := 4983230072969 + 3 ^ 40 * 5268901 * 2
def baseEnd_5268901 : Nat := 2705478733955195134306271

theorem tailTrace_5268901 : CollatzResearch.WordTrace tailWord_5268901 prefixEnd_5268901 2705478733955195134306271 := by
  unfold tailWord_5268901
  simp only [CollatzResearch.WordTrace]
  refine ⟨192172607084679008494662557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128115071389786005663108371 192172607084679008494662557)
  ·
    refine ⟨72064727656754628185498459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192172607084679008494662557 72064727656754628185498459)
    ·
      refine ⟨108097091485131942278247689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72064727656754628185498459 108097091485131942278247689)
      ·
        refine ⟨81072818613848956708685767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108097091485131942278247689 81072818613848956708685767)
        ·
          refine ⟨121609227920773435063028651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81072818613848956708685767 121609227920773435063028651)
          ·
            refine ⟨182413841881160152594542977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121609227920773435063028651 182413841881160152594542977)
            ·
              refine ⟨136810381410870114445907233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182413841881160152594542977 136810381410870114445907233)
              ·
                refine ⟨102607786058152585834430425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136810381410870114445907233 102607786058152585834430425)
                ·
                  refine ⟨76955839543614439375822819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102607786058152585834430425 76955839543614439375822819)
                  ·
                    refine ⟨115433759315421659063734229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76955839543614439375822819 115433759315421659063734229)
                    ·
                      refine ⟨2705478733955195134306271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115433759315421659063734229 2705478733955195134306271)
                      ·
                        rfl

theorem cell23_5268901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_5268901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268901 prefixEnd_5268901 := by exact prefixLift 5268901
  have htrace : WordTrace (prefixWord ++ tailWord_5268901) baseStart_5268901 baseEnd_5268901 := by
    simpa [prefixWord, tailWord_5268901, baseEnd_5268901] using wordTrace_append hprefix tailTrace_5268901
  have hstable : (prefixWord ++ tailWord_5268901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268901).length < 2 ^ (prefixWord ++ tailWord_5268901).sum := by decide
  have hdescent : baseEnd_5268901 < baseStart_5268901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268925 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_5268925 : Nat := 118140960795 + 5268925 * 2 ^ 59
def prefixEnd_5268925 : Nat := 4983230072969 + 3 ^ 40 * 5268925 * 2
def baseEnd_5268925 : Nat := 901830352496967680135387

theorem tailTrace_5268925 : CollatzResearch.WordTrace tailWord_5268925 prefixEnd_5268925 901830352496967680135387 := by
  unfold tailWord_5268925
  simp only [CollatzResearch.WordTrace]
  refine ⟨192173482436592060593536229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128115654957728040395690819 192173482436592060593536229)
  ·
    refine ⟨36032527956861011361288043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192173482436592060593536229 36032527956861011361288043)
    ·
      refine ⟨54048791935291517041932065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36032527956861011361288043 54048791935291517041932065)
      ·
        refine ⟨40536593951468637781449049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54048791935291517041932065 40536593951468637781449049)
        ·
          refine ⟨30402445463601478336086787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40536593951468637781449049 30402445463601478336086787)
          ·
            refine ⟨45603668195402217504130181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30402445463601478336086787 45603668195402217504130181)
            ·
              refine ⟨8550687786637915782024409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45603668195402217504130181 8550687786637915782024409)
              ·
                refine ⟨6413015839978436836518307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8550687786637915782024409 6413015839978436836518307)
                ·
                  refine ⟨9619523759967655254777461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6413015839978436836518307 9619523759967655254777461)
                  ·
                    refine ⟨901830352496967680135387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9619523759967655254777461 901830352496967680135387)
                    ·
                      rfl

theorem cell23_5268925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_5268925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268925 prefixEnd_5268925 := by exact prefixLift 5268925
  have htrace : WordTrace (prefixWord ++ tailWord_5268925) baseStart_5268925 baseEnd_5268925 := by
    simpa [prefixWord, tailWord_5268925, baseEnd_5268925] using wordTrace_append hprefix tailTrace_5268925
  have hstable : (prefixWord ++ tailWord_5268925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268925).length < 2 ^ (prefixWord ++ tailWord_5268925).sum := by decide
  have hdescent : baseEnd_5268925 < baseStart_5268925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268928 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_5268928 : Nat := 118140960795 + 5268928 * 2 ^ 59
def prefixEnd_5268928 : Nat := 4983230072969 + 3 ^ 40 * 5268928 * 2
def baseEnd_5268928 : Nat := 2705492597932866528668647

theorem tailTrace_5268928 : CollatzResearch.WordTrace tailWord_5268928 prefixEnd_5268928 2705492597932866528668647 := by
  unfold tailWord_5268928
  simp only [CollatzResearch.WordTrace]
  refine ⟨96086795927790596052947719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128115727903720794737263625 96086795927790596052947719)
  ·
    refine ⟨144130193891685894079421579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96086795927790596052947719 144130193891685894079421579)
    ·
      refine ⟨216195290837528841119132369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144130193891685894079421579 216195290837528841119132369)
      ·
        refine ⟨162146468128146630839349277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216195290837528841119132369 162146468128146630839349277)
        ·
          refine ⟨60804925548054986564755979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162146468128146630839349277 60804925548054986564755979)
          ·
            refine ⟨91207388322082479847133969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60804925548054986564755979 91207388322082479847133969)
            ·
              refine ⟨68405541241561859885350477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91207388322082479847133969 68405541241561859885350477)
              ·
                refine ⟨25652077965585697457006429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68405541241561859885350477 25652077965585697457006429)
                ·
                  refine ⟨9619529237094636546377411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25652077965585697457006429 9619529237094636546377411)
                  ·
                    refine ⟨14429293855641954819566117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9619529237094636546377411 14429293855641954819566117)
                    ·
                      refine ⟨2705492597932866528668647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14429293855641954819566117 2705492597932866528668647)
                      ·
                        rfl

theorem cell23_5268928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_5268928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268928 prefixEnd_5268928 := by exact prefixLift 5268928
  have htrace : WordTrace (prefixWord ++ tailWord_5268928) baseStart_5268928 baseEnd_5268928 := by
    simpa [prefixWord, tailWord_5268928, baseEnd_5268928] using wordTrace_append hprefix tailTrace_5268928
  have hstable : (prefixWord ++ tailWord_5268928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268928).length < 2 ^ (prefixWord ++ tailWord_5268928).sum := by decide
  have hdescent : baseEnd_5268928 < baseStart_5268928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268932 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5268932 : Nat := 118140960795 + 5268932 * 2 ^ 59
def prefixEnd_5268932 : Nat := 4983230072969 + 3 ^ 40 * 5268932 * 2
def baseEnd_5268932 : Nat := 2705494651855484513018629

theorem tailTrace_5268932 : CollatzResearch.WordTrace tailWord_5268932 prefixEnd_5268932 2705494651855484513018629 := by
  unfold tailWord_5268932
  simp only [CollatzResearch.WordTrace]
  refine ⟨96086868873783350394520525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128115825165044467192694033 96086868873783350394520525)
  ·
    refine ⟨36032575827668756397945197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96086868873783350394520525 36032575827668756397945197)
    ·
      refine ⟨13512215935375783649229449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36032575827668756397945197 13512215935375783649229449)
      ·
        refine ⟨10134161951531837736922087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13512215935375783649229449 10134161951531837736922087)
        ·
          refine ⟨15201242927297756605383131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10134161951531837736922087 15201242927297756605383131)
          ·
            refine ⟨22801864390946634908074697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15201242927297756605383131 22801864390946634908074697)
            ·
              refine ⟨17101398293209976181056023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22801864390946634908074697 17101398293209976181056023)
              ·
                refine ⟨25652097439814964271584035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17101398293209976181056023 25652097439814964271584035)
                ·
                  refine ⟨38478146159722446407376053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25652097439814964271584035 38478146159722446407376053)
                  ·
                    refine ⟨3607326202473979350691505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38478146159722446407376053 3607326202473979350691505)
                    ·
                      refine ⟨2705494651855484513018629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607326202473979350691505 2705494651855484513018629)
                      ·
                        rfl

theorem cell23_5268932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5268932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268932 prefixEnd_5268932 := by exact prefixLift 5268932
  have htrace : WordTrace (prefixWord ++ tailWord_5268932) baseStart_5268932 baseEnd_5268932 := by
    simpa [prefixWord, tailWord_5268932, baseEnd_5268932] using wordTrace_append hprefix tailTrace_5268932
  have hstable : (prefixWord ++ tailWord_5268932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268932).length < 2 ^ (prefixWord ++ tailWord_5268932).sum := by decide
  have hdescent : baseEnd_5268932 < baseStart_5268932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268965 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5268965 : Nat := 118140960795 + 5268965 * 2 ^ 59
def prefixEnd_5268965 : Nat := 4983230072969 + 3 ^ 40 * 5268965 * 2
def baseEnd_5268965 : Nat := 2705511596717082883905977

theorem tailTrace_5268965 : CollatzResearch.WordTrace tailWord_5268965 prefixEnd_5268965 2705511596717082883905977 := by
  unfold tailWord_5268965
  simp only [CollatzResearch.WordTrace]
  refine ⟨192174941356447147424992349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128116627570964764949994899 192174941356447147424992349)
  ·
    refine ⟨72065603008667680284372131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192174941356447147424992349 72065603008667680284372131)
    ·
      refine ⟨108098404513001520426558197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72065603008667680284372131 108098404513001520426558197)
      ·
        refine ⟨10134225423093892539989831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108098404513001520426558197 10134225423093892539989831)
        ·
          refine ⟨15201338134640838809984747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10134225423093892539989831 15201338134640838809984747)
          ·
            refine ⟨22802007201961258214977121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15201338134640838809984747 22802007201961258214977121)
            ·
              refine ⟨17101505401470943661232841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22802007201961258214977121 17101505401470943661232841)
              ·
                refine ⟨12826129051103207745924631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17101505401470943661232841 12826129051103207745924631)
                ·
                  refine ⟨19239193576654811618886947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12826129051103207745924631 19239193576654811618886947)
                  ·
                    refine ⟨28858790364982217428330421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19239193576654811618886947 28858790364982217428330421)
                    ·
                      refine ⟨2705511596717082883905977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28858790364982217428330421 2705511596717082883905977)
                      ·
                        rfl

theorem cell23_5268965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5268965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268965 prefixEnd_5268965 := by exact prefixLift 5268965
  have htrace : WordTrace (prefixWord ++ tailWord_5268965) baseStart_5268965 baseEnd_5268965 := by
    simpa [prefixWord, tailWord_5268965, baseEnd_5268965] using wordTrace_append hprefix tailTrace_5268965
  have hstable : (prefixWord ++ tailWord_5268965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268965).length < 2 ^ (prefixWord ++ tailWord_5268965).sum := by decide
  have hdescent : baseEnd_5268965 < baseStart_5268965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268968 : List Nat := [2, 1, 4, 1, 1, 2, 4, 8]
def baseStart_5268968 : Nat := 118140960795 + 5268968 * 2 ^ 59
def prefixEnd_5268968 : Nat := 4983230072969 + 3 ^ 40 * 5268968 * 2
def baseEnd_5268968 : Nat := 100204190265149865635869

theorem tailTrace_5268968 : CollatzResearch.WordTrace tailWord_5268968 prefixEnd_5268968 100204190265149865635869 := by
  unfold tailWord_5268968
  simp only [CollatzResearch.WordTrace]
  refine ⟨96087525387718139468675779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128116700516957519291567705 96087525387718139468675779)
  ·
    refine ⟨144131288081577209203013669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96087525387718139468675779 144131288081577209203013669)
    ·
      refine ⟨27024616515295726725565063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144131288081577209203013669 27024616515295726725565063)
      ·
        refine ⟨40536924772943590088347595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27024616515295726725565063 40536924772943590088347595)
        ·
          refine ⟨60805387159415385132521393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40536924772943590088347595 60805387159415385132521393)
          ·
            refine ⟨45604040369561538849391045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60805387159415385132521393 45604040369561538849391045)
            ·
              refine ⟨8550757569292788534260821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45604040369561538849391045 8550757569292788534260821)
              ·
                refine ⟨100204190265149865635869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8550757569292788534260821 100204190265149865635869)
                ·
                  rfl

theorem cell23_5268968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 8].length) (baseStart_5268968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268968 prefixEnd_5268968 := by exact prefixLift 5268968
  have htrace : WordTrace (prefixWord ++ tailWord_5268968) baseStart_5268968 baseEnd_5268968 := by
    simpa [prefixWord, tailWord_5268968, baseEnd_5268968] using wordTrace_append hprefix tailTrace_5268968
  have hstable : (prefixWord ++ tailWord_5268968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268968).length < 2 ^ (prefixWord ++ tailWord_5268968).sum := by decide
  have hdescent : baseEnd_5268968 < baseStart_5268968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268982 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_5268982 : Nat := 118140960795 + 5268982 * 2 ^ 59
def prefixEnd_5268982 : Nat := 4983230072969 + 3 ^ 40 * 5268982 * 2
def baseEnd_5268982 : Nat := 2705520325888209317393399

theorem tailTrace_5268982 : CollatzResearch.WordTrace tailWord_5268982 prefixEnd_5268982 2705520325888209317393399 := by
  unfold tailWord_5268982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12010972587336597458022575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128117040931590372885574133 12010972587336597458022575)
  ·
    refine ⟨18016458881004896187033863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12010972587336597458022575 18016458881004896187033863)
    ·
      refine ⟨27024688321507344280550795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18016458881004896187033863 27024688321507344280550795)
      ·
        refine ⟨40537032482261016420826193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27024688321507344280550795 40537032482261016420826193)
        ·
          refine ⟨30402774361695762315619645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40537032482261016420826193 30402774361695762315619645)
          ·
            refine ⟨11401040385635910868357367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30402774361695762315619645 11401040385635910868357367)
            ·
              refine ⟨17101560578453866302536051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11401040385635910868357367 17101560578453866302536051)
              ·
                refine ⟨25652340867680799453804077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17101560578453866302536051 25652340867680799453804077)
                ·
                  refine ⟨9619627825380299795176529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25652340867680799453804077 9619627825380299795176529)
                  ·
                    refine ⟨7214720869035224846382397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9619627825380299795176529 7214720869035224846382397)
                    ·
                      refine ⟨2705520325888209317393399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7214720869035224846382397 2705520325888209317393399)
                      ·
                        rfl

theorem cell23_5268982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_5268982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268982 prefixEnd_5268982 := by exact prefixLift 5268982
  have htrace : WordTrace (prefixWord ++ tailWord_5268982) baseStart_5268982 baseEnd_5268982 := by
    simpa [prefixWord, tailWord_5268982, baseEnd_5268982] using wordTrace_append hprefix tailTrace_5268982
  have hstable : (prefixWord ++ tailWord_5268982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268982).length < 2 ^ (prefixWord ++ tailWord_5268982).sum := by decide
  have hdescent : baseEnd_5268982 < baseStart_5268982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268995 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 3]
def baseStart_5268995 : Nat := 118140960795 + 5268995 * 2 ^ 59
def prefixEnd_5268995 : Nat := 4983230072969 + 3 ^ 40 * 5268995 * 2
def baseEnd_5268995 : Nat := 2705527001136717766530839

theorem tailTrace_5268995 : CollatzResearch.WordTrace tailWord_5268995 prefixEnd_5268995 2705527001136717766530839 := by
  unfold tailWord_5268995
  simp only [CollatzResearch.WordTrace]
  refine ⟨192176035546338462548584439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128117357030892308365722959 192176035546338462548584439)
  ·
    refine ⟨288264053319507693822876659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192176035546338462548584439 288264053319507693822876659)
    ·
      refine ⟨432396079979261540734314989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288264053319507693822876659 432396079979261540734314989)
      ·
        refine ⟨162148529992223077775368121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432396079979261540734314989 162148529992223077775368121)
        ·
          refine ⟨121611397494167308331526091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162148529992223077775368121 121611397494167308331526091)
          ·
            refine ⟨182417096241250962497289137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121611397494167308331526091 182417096241250962497289137)
            ·
              refine ⟨136812822180938221872966853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182417096241250962497289137 136812822180938221872966853)
              ·
                refine ⟨25652404158925916601181285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136812822180938221872966853 25652404158925916601181285)
                ·
                  refine ⟨4809825779798609362721491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25652404158925916601181285 4809825779798609362721491)
                  ·
                    refine ⟨7214738669697914044082237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4809825779798609362721491 7214738669697914044082237)
                    ·
                      refine ⟨2705527001136717766530839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7214738669697914044082237 2705527001136717766530839)
                      ·
                        rfl

theorem cell23_5268995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_5268995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268995 prefixEnd_5268995 := by exact prefixLift 5268995
  have htrace : WordTrace (prefixWord ++ tailWord_5268995) baseStart_5268995 baseEnd_5268995 := by
    simpa [prefixWord, tailWord_5268995, baseEnd_5268995] using wordTrace_append hprefix tailTrace_5268995
  have hstable : (prefixWord ++ tailWord_5268995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268995).length < 2 ^ (prefixWord ++ tailWord_5268995).sum := by decide
  have hdescent : baseEnd_5268995 < baseStart_5268995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5268999 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_5268999 : Nat := 118140960795 + 5268999 * 2 ^ 59
def prefixEnd_5268999 : Nat := 4983230072969 + 3 ^ 40 * 5268999 * 2
def baseEnd_5268999 : Nat := 2705529055059335750880821

theorem tailTrace_5268999 : CollatzResearch.WordTrace tailWord_5268999 prefixEnd_5268999 2705529055059335750880821 := by
  unfold tailWord_5268999
  simp only [CollatzResearch.WordTrace]
  refine ⟨192176181438323971231730051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128117454292215980821153367 192176181438323971231730051)
  ·
    refine ⟨288264272157485956847595077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192176181438323971231730051 288264272157485956847595077)
    ·
      refine ⟨54049551029528616908924077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288264272157485956847595077 54049551029528616908924077)
      ·
        refine ⟨20268581636073231340846529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54049551029528616908924077 20268581636073231340846529)
        ·
          refine ⟨15201436227054923505634897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20268581636073231340846529 15201436227054923505634897)
          ·
            refine ⟨11401077170291192629226173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15201436227054923505634897 11401077170291192629226173)
            ·
              refine ⟨4275403938859197235959815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11401077170291192629226173 4275403938859197235959815)
              ·
                refine ⟨6413105908288795853939723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275403938859197235959815 6413105908288795853939723)
                ·
                  refine ⟨9619658862433193780909585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6413105908288795853939723 9619658862433193780909585)
                  ·
                    refine ⟨7214744146824895335682189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9619658862433193780909585 7214744146824895335682189)
                    ·
                      refine ⟨2705529055059335750880821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7214744146824895335682189 2705529055059335750880821)
                      ·
                        rfl

theorem cell23_5268999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_5268999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5268999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5268999 prefixEnd_5268999 := by exact prefixLift 5268999
  have htrace : WordTrace (prefixWord ++ tailWord_5268999) baseStart_5268999 baseEnd_5268999 := by
    simpa [prefixWord, tailWord_5268999, baseEnd_5268999] using wordTrace_append hprefix tailTrace_5268999
  have hstable : (prefixWord ++ tailWord_5268999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5268999).length < 2 ^ (prefixWord ++ tailWord_5268999).sum := by decide
  have hdescent : baseEnd_5268999 < baseStart_5268999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5268999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269013 : List Nat := [1, 3, 2, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_5269013 : Nat := 118140960795 + 5269013 * 2 ^ 59
def prefixEnd_5269013 : Nat := 4983230072969 + 3 ^ 40 * 5269013 * 2
def baseEnd_5269013 : Nat := 2705536243788498696105757

theorem tailTrace_5269013 : CollatzResearch.WordTrace tailWord_5269013 prefixEnd_5269013 2705536243788498696105757 := by
  unfold tailWord_5269013
  simp only [CollatzResearch.WordTrace]
  refine ⟨192176692060273251622739693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128117794706848834415159795 192176692060273251622739693)
  ·
    refine ⟨72066259522602469358527385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192176692060273251622739693 72066259522602469358527385)
    ·
      refine ⟨54049694641951852018895539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72066259522602469358527385 54049694641951852018895539)
      ·
        refine ⟨81074541962927778028343309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54049694641951852018895539 81074541962927778028343309)
        ·
          refine ⟨30402953236097916760628741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81074541962927778028343309 30402953236097916760628741)
          ·
            refine ⟨5700553731768359392617889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30402953236097916760628741 5700553731768359392617889)
            ·
              refine ⟨4275415298826269544463417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5700553731768359392617889 4275415298826269544463417)
              ·
                refine ⟨3206561474119702158347563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4275415298826269544463417 3206561474119702158347563)
                ·
                  refine ⟨4809842211179553237521345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206561474119702158347563 4809842211179553237521345)
                  ·
                    refine ⟨3607381658384664928141009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4809842211179553237521345 3607381658384664928141009)
                    ·
                      refine ⟨2705536243788498696105757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607381658384664928141009 2705536243788498696105757)
                      ·
                        rfl

theorem cell23_5269013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_5269013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269013 prefixEnd_5269013 := by exact prefixLift 5269013
  have htrace : WordTrace (prefixWord ++ tailWord_5269013) baseStart_5269013 baseEnd_5269013 := by
    simpa [prefixWord, tailWord_5269013, baseEnd_5269013] using wordTrace_append hprefix tailTrace_5269013
  have hstable : (prefixWord ++ tailWord_5269013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269013).length < 2 ^ (prefixWord ++ tailWord_5269013).sum := by decide
  have hdescent : baseEnd_5269013 < baseStart_5269013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269109 : List Nat := [1, 3, 4, 2, 1, 1, 3, 3, 5]
def baseStart_5269109 : Nat := 118140960795 + 5269109 * 2 ^ 59
def prefixEnd_5269109 : Nat := 4983230072969 + 3 ^ 40 * 5269109 * 2
def baseEnd_5269109 : Nat := 300620615325703368945035

theorem tailTrace_5269109 : CollatzResearch.WordTrace tailWord_5269109 prefixEnd_5269109 300620615325703368945035 := by
  unfold tailWord_5269109
  simp only [CollatzResearch.WordTrace]
  refine ⟨192180193467925460018234381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128120128978616973345489587 192180193467925460018234381)
  ·
    refine ⟨72067572550472047506837893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192180193467925460018234381 72067572550472047506837893)
    ·
      refine ⟨13512669853213508907532105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72067572550472047506837893 13512669853213508907532105)
      ·
        refine ⟨10134502389910131680649079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13512669853213508907532105 10134502389910131680649079)
        ·
          refine ⟨15201753584865197520973619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10134502389910131680649079 15201753584865197520973619)
          ·
            refine ⟨22802630377297796281460429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15201753584865197520973619 22802630377297796281460429)
            ·
              refine ⟨8550986391486673605547661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22802630377297796281460429 8550986391486673605547661)
              ·
                refine ⟨3206619896807502602080373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8550986391486673605547661 3206619896807502602080373)
                ·
                  refine ⟨300620615325703368945035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206619896807502602080373 300620615325703368945035)
                  ·
                    rfl

theorem cell23_5269109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_5269109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269109 prefixEnd_5269109 := by exact prefixLift 5269109
  have htrace : WordTrace (prefixWord ++ tailWord_5269109) baseStart_5269109 baseEnd_5269109 := by
    simpa [prefixWord, tailWord_5269109, baseEnd_5269109] using wordTrace_append hprefix tailTrace_5269109
  have hstable : (prefixWord ++ tailWord_5269109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269109).length < 2 ^ (prefixWord ++ tailWord_5269109).sum := by decide
  have hdescent : baseEnd_5269109 < baseStart_5269109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269145 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 3]
def baseStart_5269145 : Nat := 118140960795 + 5269145 * 2 ^ 59
def prefixEnd_5269145 : Nat := 4983230072969 + 3 ^ 40 * 5269145 * 2
def baseEnd_5269145 : Nat := 2705604023234892179655149

theorem tailTrace_5269145 : CollatzResearch.WordTrace tailWord_5269145 prefixEnd_5269145 2705604023234892179655149 := by
  unfold tailWord_5269145
  simp only [CollatzResearch.WordTrace]
  refine ⟨192181506495795038166544889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128121004330530025444363259 192181506495795038166544889)
  ·
    refine ⟨144136129871846278624908667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192181506495795038166544889 144136129871846278624908667)
    ·
      refine ⟨216204194807769417937363001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144136129871846278624908667 216204194807769417937363001)
      ·
        refine ⟨162153146105827063453022251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216204194807769417937363001 162153146105827063453022251)
        ·
          refine ⟨243229719158740595179533377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162153146105827063453022251 243229719158740595179533377)
          ·
            refine ⟨182422289369055446384650033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243229719158740595179533377 182422289369055446384650033)
            ·
              refine ⟨136816717026791584788487525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182422289369055446384650033 136816717026791584788487525)
              ·
                refine ⟨25653134442523422147841411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136816717026791584788487525 25653134442523422147841411)
                ·
                  refine ⟨38479701663785133221762117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25653134442523422147841411 38479701663785133221762117)
                  ·
                    refine ⟨7214944061959712479080397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38479701663785133221762117 7214944061959712479080397)
                    ·
                      refine ⟨2705604023234892179655149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7214944061959712479080397 2705604023234892179655149)
                      ·
                        rfl

theorem cell23_5269145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_5269145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269145 prefixEnd_5269145 := by exact prefixLift 5269145
  have htrace : WordTrace (prefixWord ++ tailWord_5269145) baseStart_5269145 baseEnd_5269145 := by
    simpa [prefixWord, tailWord_5269145, baseEnd_5269145] using wordTrace_append hprefix tailTrace_5269145
  have hstable : (prefixWord ++ tailWord_5269145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269145).length < 2 ^ (prefixWord ++ tailWord_5269145).sum := by decide
  have hdescent : baseEnd_5269145 < baseStart_5269145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269182 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_5269182 : Nat := 118140960795 + 5269182 * 2 ^ 59
def prefixEnd_5269182 : Nat := 4983230072969 + 3 ^ 40 * 5269182 * 2
def baseEnd_5269182 : Nat := 300624780224345392765831

theorem tailTrace_5269182 : CollatzResearch.WordTrace tailWord_5269182 prefixEnd_5269182 300624780224345392765831 := by
  unfold tailWord_5269182
  simp only [CollatzResearch.WordTrace]
  refine ⟨24022856999582624185705225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128121903997773995657094533 24022856999582624185705225)
  ·
    refine ⟨18017142749686968139278919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24022856999582624185705225 18017142749686968139278919)
    ·
      refine ⟨27025714124530452208918379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18017142749686968139278919 27025714124530452208918379)
      ·
        refine ⟨40538571186795678313377569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27025714124530452208918379 40538571186795678313377569)
        ·
          refine ⟨30403928390096758735033177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40538571186795678313377569 30403928390096758735033177)
          ·
            refine ⟨22802946292572569051274883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30403928390096758735033177 22802946292572569051274883)
            ·
              refine ⟨34204419438858853576912325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22802946292572569051274883 34204419438858853576912325)
              ·
                refine ⟨6413328644786035045671061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34204419438858853576912325 6413328644786035045671061)
                ·
                  refine ⟨300624780224345392765831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6413328644786035045671061 300624780224345392765831)
                  ·
                    rfl

theorem cell23_5269182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_5269182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269182 prefixEnd_5269182 := by exact prefixLift 5269182
  have htrace : WordTrace (prefixWord ++ tailWord_5269182) baseStart_5269182 baseEnd_5269182 := by
    simpa [prefixWord, tailWord_5269182, baseEnd_5269182] using wordTrace_append hprefix tailTrace_5269182
  have hstable : (prefixWord ++ tailWord_5269182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269182).length < 2 ^ (prefixWord ++ tailWord_5269182).sum := by decide
  have hdescent : baseEnd_5269182 < baseStart_5269182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269209 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 3]
def baseStart_5269209 : Nat := 118140960795 + 5269209 * 2 ^ 59
def prefixEnd_5269209 : Nat := 4983230072969 + 3 ^ 40 * 5269209 * 2
def baseEnd_5269209 : Nat := 2705636885996779929254855

theorem tailTrace_5269209 : CollatzResearch.WordTrace tailWord_5269209 prefixEnd_5269209 2705636885996779929254855 := by
  unfold tailWord_5269209
  simp only [CollatzResearch.WordTrace]
  refine ⟨192183840767563177096874681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128122560511708784731249787 192183840767563177096874681)
  ·
    refine ⟨144137880575672382822656011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192183840767563177096874681 144137880575672382822656011)
    ·
      refine ⟨216206820863508574233984017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144137880575672382822656011 216206820863508574233984017)
      ·
        refine ⟨162155115647631430675488013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216206820863508574233984017 162155115647631430675488013)
        ·
          refine ⟨60808168367861786503308005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162155115647631430675488013 60808168367861786503308005)
          ·
            refine ⟨11401531568974084969370251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60808168367861786503308005 11401531568974084969370251)
            ·
              refine ⟨17102297353461127454055377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11401531568974084969370251 17102297353461127454055377)
              ·
                refine ⟨12826723015095845590541533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17102297353461127454055377 12826723015095845590541533)
                ·
                  refine ⟨4810021130660942096453075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12826723015095845590541533 4810021130660942096453075)
                  ·
                    refine ⟨7215031695991413144679613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810021130660942096453075 7215031695991413144679613)
                    ·
                      refine ⟨2705636885996779929254855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215031695991413144679613 2705636885996779929254855)
                      ·
                        rfl

theorem cell23_5269209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_5269209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269209 prefixEnd_5269209 := by exact prefixLift 5269209
  have htrace : WordTrace (prefixWord ++ tailWord_5269209) baseStart_5269209 baseEnd_5269209 := by
    simpa [prefixWord, tailWord_5269209, baseEnd_5269209] using wordTrace_append hprefix tailTrace_5269209
  have hstable : (prefixWord ++ tailWord_5269209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269209).length < 2 ^ (prefixWord ++ tailWord_5269209).sum := by decide
  have hdescent : baseEnd_5269209 < baseStart_5269209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269213 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5269213 : Nat := 118140960795 + 5269213 * 2 ^ 59
def prefixEnd_5269213 : Nat := 4983230072969 + 3 ^ 40 * 5269213 * 2
def baseEnd_5269213 : Nat := 2705638939919397913604837

theorem tailTrace_5269213 : CollatzResearch.WordTrace tailWord_5269213 prefixEnd_5269213 2705638939919397913604837 := by
  unfold tailWord_5269213
  simp only [CollatzResearch.WordTrace]
  refine ⟨192183986659548685780020293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128122657773032457186680195 192183986659548685780020293)
  ·
    refine ⟨36034497498665378583753805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192183986659548685780020293 36034497498665378583753805)
    ·
      refine ⟨13512936561999516968907677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36034497498665378583753805 13512936561999516968907677)
      ·
        refine ⟨5067351210749818863340379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13512936561999516968907677 5067351210749818863340379)
        ·
          refine ⟨7601026816124728295010569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067351210749818863340379 7601026816124728295010569)
          ·
            refine ⟨5700770112093546221257927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7601026816124728295010569 5700770112093546221257927)
            ·
              refine ⟨8551155168140319331886891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700770112093546221257927 8551155168140319331886891)
              ·
                refine ⟨12826732752210478997830337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8551155168140319331886891 12826732752210478997830337)
                ·
                  refine ⟨9620049564157859248372753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12826732752210478997830337 9620049564157859248372753)
                  ·
                    refine ⟨7215037173118394436279565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9620049564157859248372753 7215037173118394436279565)
                    ·
                      refine ⟨2705638939919397913604837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215037173118394436279565 2705638939919397913604837)
                      ·
                        rfl

theorem cell23_5269213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5269213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269213 prefixEnd_5269213 := by exact prefixLift 5269213
  have htrace : WordTrace (prefixWord ++ tailWord_5269213) baseStart_5269213 baseEnd_5269213 := by
    simpa [prefixWord, tailWord_5269213, baseEnd_5269213] using wordTrace_append hprefix tailTrace_5269213
  have hstable : (prefixWord ++ tailWord_5269213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269213).length < 2 ^ (prefixWord ++ tailWord_5269213).sum := by decide
  have hdescent : baseEnd_5269213 < baseStart_5269213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269226 : List Nat := [3, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_5269226 : Nat := 118140960795 + 5269226 * 2 ^ 59
def prefixEnd_5269226 : Nat := 4983230072969 + 3 ^ 40 * 5269226 * 2
def baseEnd_5269226 : Nat := 2705645615167906362742277

theorem tailTrace_5269226 : CollatzResearch.WordTrace tailWord_5269226 prefixEnd_5269226 2705645615167906362742277 := by
  unfold tailWord_5269226
  simp only [CollatzResearch.WordTrace]
  refine ⟨48046115202125397250060883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128122973872334392666829021 48046115202125397250060883)
  ·
    refine ⟨72069172803188095875091325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48046115202125397250060883 72069172803188095875091325)
    ·
      refine ⟨27025939801195535953159247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72069172803188095875091325 27025939801195535953159247)
      ·
        refine ⟨40538909701793303929738871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27025939801195535953159247 40538909701793303929738871)
        ·
          refine ⟨60808364552689955894608307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40538909701793303929738871 60808364552689955894608307)
          ·
            refine ⟨91212546829034933841912461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60808364552689955894608307 91212546829034933841912461)
            ·
              refine ⟨34204705060888100190717173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91212546829034933841912461 34204705060888100190717173)
              ·
                refine ⟨3206691099458259392879735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34204705060888100190717173 3206691099458259392879735)
                ·
                  refine ⟨4810036649187389089319603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206691099458259392879735 4810036649187389089319603)
                  ·
                    refine ⟨7215054973781083633979405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810036649187389089319603 7215054973781083633979405)
                    ·
                      refine ⟨2705645615167906362742277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215054973781083633979405 2705645615167906362742277)
                      ·
                        rfl

theorem cell23_5269226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_5269226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269226 prefixEnd_5269226 := by exact prefixLift 5269226
  have htrace : WordTrace (prefixWord ++ tailWord_5269226) baseStart_5269226 baseEnd_5269226 := by
    simpa [prefixWord, tailWord_5269226, baseEnd_5269226] using wordTrace_append hprefix tailTrace_5269226
  have hstable : (prefixWord ++ tailWord_5269226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269226).length < 2 ^ (prefixWord ++ tailWord_5269226).sum := by decide
  have hdescent : baseEnd_5269226 < baseStart_5269226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269229 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_5269229 : Nat := 118140960795 + 5269229 * 2 ^ 59
def prefixEnd_5269229 : Nat := 4983230072969 + 3 ^ 40 * 5269229 * 2
def baseEnd_5269229 : Nat := 901882385203289950334921

theorem tailTrace_5269229 : CollatzResearch.WordTrace tailWord_5269229 prefixEnd_5269229 901882385203289950334921 := by
  unfold tailWord_5269229
  simp only [CollatzResearch.WordTrace]
  refine ⟨192184570227490720512602741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128123046818327147008401827 192184570227490720512602741)
  ·
    refine ⟨18017303458827255048056507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192184570227490720512602741 18017303458827255048056507)
    ·
      refine ⟨27025955188240882572084761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18017303458827255048056507 27025955188240882572084761)
      ·
        refine ⟨20269466391180661929063571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27025955188240882572084761 20269466391180661929063571)
        ·
          refine ⟨30404199586770992893595357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20269466391180661929063571 30404199586770992893595357)
          ·
            refine ⟨11401574845039122335098259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30404199586770992893595357 11401574845039122335098259)
            ·
              refine ⟨17102362267558683502647389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11401574845039122335098259 17102362267558683502647389)
              ·
                refine ⟨6413385850334506313492771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17102362267558683502647389 6413385850334506313492771)
                ·
                  refine ⟨9620078775501759470239157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6413385850334506313492771 9620078775501759470239157)
                  ·
                    refine ⟨901882385203289950334921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9620078775501759470239157 901882385203289950334921)
                    ·
                      rfl

theorem cell23_5269229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_5269229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269229 prefixEnd_5269229 := by exact prefixLift 5269229
  have htrace : WordTrace (prefixWord ++ tailWord_5269229) baseStart_5269229 baseEnd_5269229 := by
    simpa [prefixWord, tailWord_5269229, baseEnd_5269229] using wordTrace_append hprefix tailTrace_5269229
  have hstable : (prefixWord ++ tailWord_5269229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269229).length < 2 ^ (prefixWord ++ tailWord_5269229).sum := by decide
  have hdescent : baseEnd_5269229 < baseStart_5269229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269252 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_5269252 : Nat := 118140960795 + 5269252 * 2 ^ 59
def prefixEnd_5269252 : Nat := 4983230072969 + 3 ^ 40 * 5269252 * 2
def baseEnd_5269252 : Nat := 2705658965664923261017157

theorem tailTrace_5269252 : CollatzResearch.WordTrace tailWord_5269252 prefixEnd_5269252 2705658965664923261017157 := by
  unfold tailWord_5269252
  simp only [CollatzResearch.WordTrace]
  refine ⟨96092704553203697720345005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128123606070938263627126673 96092704553203697720345005)
  ·
    refine ⟨36034764207451386645129377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96092704553203697720345005 36034764207451386645129377)
    ·
      refine ⟨27026073155588539983847033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36034764207451386645129377 27026073155588539983847033)
      ·
        refine ⟨20269554866691404987885275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27026073155588539983847033 20269554866691404987885275)
        ·
          refine ⟨30404332300037107481827913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20269554866691404987885275 30404332300037107481827913)
          ·
            refine ⟨22803249225027830611370935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30404332300037107481827913 22803249225027830611370935)
            ·
              refine ⟨34204873837541745917056403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22803249225027830611370935 34204873837541745917056403)
              ·
                refine ⟨51307310756312618875584605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34204873837541745917056403 51307310756312618875584605)
                ·
                  refine ⟨19240241533617232078344227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51307310756312618875584605 19240241533617232078344227)
                  ·
                    refine ⟨28860362300425848117516341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19240241533617232078344227 28860362300425848117516341)
                    ·
                      refine ⟨2705658965664923261017157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28860362300425848117516341 2705658965664923261017157)
                      ·
                        rfl

theorem cell23_5269252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_5269252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269252 prefixEnd_5269252 := by exact prefixLift 5269252
  have htrace : WordTrace (prefixWord ++ tailWord_5269252) baseStart_5269252 baseEnd_5269252 := by
    simpa [prefixWord, tailWord_5269252, baseEnd_5269252] using wordTrace_append hprefix tailTrace_5269252
  have hstable : (prefixWord ++ tailWord_5269252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269252).length < 2 ^ (prefixWord ++ tailWord_5269252).sum := by decide
  have hdescent : baseEnd_5269252 < baseStart_5269252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269266 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5269266 : Nat := 118140960795 + 5269266 * 2 ^ 59
def prefixEnd_5269266 : Nat := 4983230072969 + 3 ^ 40 * 5269266 * 2
def baseEnd_5269266 : Nat := 2705666154394086206242093

theorem tailTrace_5269266 : CollatzResearch.WordTrace tailWord_5269266 prefixEnd_5269266 2705666154394086206242093 := by
  unfold tailWord_5269266
  simp only [CollatzResearch.WordTrace]
  refine ⟨48046479932089168957924913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128123946485571117221133101 48046479932089168957924913)
  ·
    refine ⟨36034859949066876718443685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48046479932089168957924913 36034859949066876718443685)
    ·
      refine ⟨6756536240450039384708191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36034859949066876718443685 6756536240450039384708191)
      ·
        refine ⟨10134804360675059077062287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756536240450039384708191 10134804360675059077062287)
        ·
          refine ⟨15202206541012588615593431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10134804360675059077062287 15202206541012588615593431)
          ·
            refine ⟨22803309811518882923390147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15202206541012588615593431 22803309811518882923390147)
            ·
              refine ⟨34204964717278324385085221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22803309811518882923390147 34204964717278324385085221)
              ·
                refine ⟨6413430884489685822203479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34204964717278324385085221 6413430884489685822203479)
                ·
                  refine ⟨9620146326734528733305219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6413430884489685822203479 9620146326734528733305219)
                  ·
                    refine ⟨14430219490101793099957829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9620146326734528733305219 14430219490101793099957829)
                    ·
                      refine ⟨2705666154394086206242093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14430219490101793099957829 2705666154394086206242093)
                      ·
                        rfl

theorem cell23_5269266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5269266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269266 prefixEnd_5269266 := by exact prefixLift 5269266
  have htrace : WordTrace (prefixWord ++ tailWord_5269266) baseStart_5269266 baseEnd_5269266 := by
    simpa [prefixWord, tailWord_5269266, baseEnd_5269266] using wordTrace_append hprefix tailTrace_5269266
  have hstable : (prefixWord ++ tailWord_5269266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269266).length < 2 ^ (prefixWord ++ tailWord_5269266).sum := by decide
  have hdescent : baseEnd_5269266 < baseStart_5269266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269269 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_5269269 : Nat := 118140960795 + 5269269 * 2 ^ 59
def prefixEnd_5269269 : Nat := 4983230072969 + 3 ^ 40 * 5269269 * 2
def baseEnd_5269269 : Nat := 2705667694836049694504579

theorem tailTrace_5269269 : CollatzResearch.WordTrace tailWord_5269269 prefixEnd_5269269 2705667694836049694504579 := by
  unfold tailWord_5269269
  simp only [CollatzResearch.WordTrace]
  refine ⟨192186029147345807344058861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128124019431563871562705907 192186029147345807344058861)
  ·
    refine ⟨72069760930254677754022073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192186029147345807344058861 72069760930254677754022073)
    ·
      refine ⟨54052320697691008315516555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72069760930254677754022073 54052320697691008315516555)
      ·
        refine ⟨81078481046536512473274833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54052320697691008315516555 81078481046536512473274833)
        ·
          refine ⟨60808860784902384354956125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81078481046536512473274833 60808860784902384354956125)
          ·
            refine ⟨22803322794338394133108547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60808860784902384354956125 22803322794338394133108547)
            ·
              refine ⟨34204984191507591199662821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22803322794338394133108547 34204984191507591199662821)
              ·
                refine ⟨6413434535907673349936779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34204984191507591199662821 6413434535907673349936779)
                ·
                  refine ⟨9620151803861510024905169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6413434535907673349936779 9620151803861510024905169)
                  ·
                    refine ⟨7215113852896132518678877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9620151803861510024905169 7215113852896132518678877)
                    ·
                      refine ⟨2705667694836049694504579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215113852896132518678877 2705667694836049694504579)
                      ·
                        rfl

theorem cell23_5269269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_5269269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269269 prefixEnd_5269269 := by exact prefixLift 5269269
  have htrace : WordTrace (prefixWord ++ tailWord_5269269) baseStart_5269269 baseEnd_5269269 := by
    simpa [prefixWord, tailWord_5269269, baseEnd_5269269] using wordTrace_append hprefix tailTrace_5269269
  have hstable : (prefixWord ++ tailWord_5269269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269269).length < 2 ^ (prefixWord ++ tailWord_5269269).sum := by decide
  have hdescent : baseEnd_5269269 < baseStart_5269269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269272 : List Nat := [2, 1, 2, 3, 1, 1, 6, 7]
def baseStart_5269272 : Nat := 118140960795 + 5269272 * 2 ^ 59
def prefixEnd_5269272 : Nat := 4983230072969 + 3 ^ 40 * 5269272 * 2
def baseEnd_5269272 : Nat := 100209971676963451213595

theorem tailTrace_5269272 : CollatzResearch.WordTrace tailWord_5269272 prefixEnd_5269272 100209971676963451213595 := by
  unfold tailWord_5269272
  simp only [CollatzResearch.WordTrace]
  refine ⟨96093069283167469428209035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128124092377556625904278713 96093069283167469428209035)
  ·
    refine ⟨144139603924751204142313553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96093069283167469428209035 144139603924751204142313553)
    ·
      refine ⟨108104702943563403106735165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144139603924751204142313553 108104702943563403106735165)
      ·
        refine ⟨40539263603836276165025687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108104702943563403106735165 40539263603836276165025687)
        ·
          refine ⟨60808895405754414247538531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40539263603836276165025687 60808895405754414247538531)
          ·
            refine ⟨91213343108631621371307797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60808895405754414247538531 91213343108631621371307797)
            ·
              refine ⟨4275625458217107251780053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91213343108631621371307797 4275625458217107251780053)
              ·
                refine ⟨100209971676963451213595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4275625458217107251780053 100209971676963451213595)
                ·
                  rfl

theorem cell23_5269272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 7].length) (baseStart_5269272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269272 prefixEnd_5269272 := by exact prefixLift 5269272
  have htrace : WordTrace (prefixWord ++ tailWord_5269272) baseStart_5269272 baseEnd_5269272 := by
    simpa [prefixWord, tailWord_5269272, baseEnd_5269272] using wordTrace_append hprefix tailTrace_5269272
  have hstable : (prefixWord ++ tailWord_5269272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269272).length < 2 ^ (prefixWord ++ tailWord_5269272).sum := by decide
  have hdescent : baseEnd_5269272 < baseStart_5269272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269283 : List Nat := [1, 1, 1, 4, 2, 1, 5, 3, 1, 2, 2]
def baseStart_5269283 : Nat := 118140960795 + 5269283 * 2 ^ 59
def prefixEnd_5269283 : Nat := 4983230072969 + 3 ^ 40 * 5269283 * 2
def baseEnd_5269283 : Nat := 2705674883565212639729515

theorem tailTrace_5269283 : CollatzResearch.WordTrace tailWord_5269283 prefixEnd_5269283 2705674883565212639729515 := by
  unfold tailWord_5269283
  simp only [CollatzResearch.WordTrace]
  refine ⟨192186539769295087735068503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128124359846196725156712335 192186539769295087735068503)
  ·
    refine ⟨288279809653942631602602755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192186539769295087735068503 288279809653942631602602755)
    ·
      refine ⟨432419714480913947403904133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288279809653942631602602755 432419714480913947403904133)
      ·
        refine ⟨81078696465171365138232025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 432419714480913947403904133 81078696465171365138232025)
        ·
          refine ⟨60809022348878523853674019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81078696465171365138232025 60809022348878523853674019)
          ·
            refine ⟨91213533523317785780511029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60809022348878523853674019 91213533523317785780511029)
            ·
              refine ⟨8551268767811042416922909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91213533523317785780511029 8551268767811042416922909)
              ·
                refine ⟨3206725787929140906346091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8551268767811042416922909 3206725787929140906346091)
                ·
                  refine ⟨4810088681893711359519137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206725787929140906346091 4810088681893711359519137)
                  ·
                    refine ⟨3607566511420283519639353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810088681893711359519137 3607566511420283519639353)
                    ·
                      refine ⟨2705674883565212639729515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607566511420283519639353 2705674883565212639729515)
                      ·
                        rfl

theorem cell23_5269283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_5269283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269283 prefixEnd_5269283 := by exact prefixLift 5269283
  have htrace : WordTrace (prefixWord ++ tailWord_5269283) baseStart_5269283 baseEnd_5269283 := by
    simpa [prefixWord, tailWord_5269283, baseEnd_5269283] using wordTrace_append hprefix tailTrace_5269283
  have hstable : (prefixWord ++ tailWord_5269283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269283).length < 2 ^ (prefixWord ++ tailWord_5269283).sum := by decide
  have hdescent : baseEnd_5269283 < baseStart_5269283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269300 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_5269300 : Nat := 118140960795 + 5269300 * 2 ^ 59
def prefixEnd_5269300 : Nat := 4983230072969 + 3 ^ 40 * 5269300 * 2
def baseEnd_5269300 : Nat := 2705683612736339073216937

theorem tailTrace_5269300 : CollatzResearch.WordTrace tailWord_5269300 prefixEnd_5269300 2705683612736339073216937 := by
  unfold tailWord_5269300
  simp only [CollatzResearch.WordTrace]
  refine ⟨96093579905116749819218677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128124773206822333092291569 96093579905116749819218677)
  ·
    refine ⟨9008773116104695295551751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96093579905116749819218677 9008773116104695295551751)
    ·
      refine ⟨13513159674157042943327627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9008773116104695295551751 13513159674157042943327627)
      ·
        refine ⟨20269739511235564414991441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13513159674157042943327627 20269739511235564414991441)
        ·
          refine ⟨15202304633426673311243581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20269739511235564414991441 15202304633426673311243581)
          ·
            refine ⟨5700864237535002491716343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15202304633426673311243581 5700864237535002491716343)
            ·
              refine ⟨8551296356302503737574515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700864237535002491716343 8551296356302503737574515)
              ·
                refine ⟨12826944534453755606361773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8551296356302503737574515 12826944534453755606361773)
                ·
                  refine ⟨4810104200420158352385665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12826944534453755606361773 4810104200420158352385665)
                  ·
                    refine ⟨3607578150315118764289249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810104200420158352385665 3607578150315118764289249)
                    ·
                      refine ⟨2705683612736339073216937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607578150315118764289249 2705683612736339073216937)
                      ·
                        rfl

theorem cell23_5269300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_5269300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269300 prefixEnd_5269300 := by exact prefixLift 5269300
  have htrace : WordTrace (prefixWord ++ tailWord_5269300) baseStart_5269300 baseEnd_5269300 := by
    simpa [prefixWord, tailWord_5269300, baseEnd_5269300] using wordTrace_append hprefix tailTrace_5269300
  have hstable : (prefixWord ++ tailWord_5269300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269300).length < 2 ^ (prefixWord ++ tailWord_5269300).sum := by decide
  have hdescent : baseEnd_5269300 < baseStart_5269300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269343 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 1, 3, 2]
def baseStart_5269343 : Nat := 118140960795 + 5269343 * 2 ^ 59
def prefixEnd_5269343 : Nat := 4983230072969 + 3 ^ 40 * 5269343 * 2
def baseEnd_5269343 : Nat := 2705705692404482404979239

theorem tailTrace_5269343 : CollatzResearch.WordTrace tailWord_5269343 prefixEnd_5269343 2705705692404482404979239 := by
  unfold tailWord_5269343
  simp only [CollatzResearch.WordTrace]
  refine ⟨192188728149077717982252683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128125818766051811988168455 192188728149077717982252683)
  ·
    refine ⟨288283092223616576973379025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192188728149077717982252683 288283092223616576973379025)
    ·
      refine ⟨216212319167712432730034269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288283092223616576973379025 216212319167712432730034269)
      ·
        refine ⟨81079619687892162273762851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216212319167712432730034269 81079619687892162273762851)
        ·
          refine ⟨121619429531838243410644277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81079619687892162273762851 121619429531838243410644277)
          ·
            refine ⟨11401821518609835319747901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121619429531838243410644277 11401821518609835319747901)
            ·
              refine ⟨4275683069478688244905463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11401821518609835319747901 4275683069478688244905463)
              ·
                refine ⟨6413524604218032367358195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275683069478688244905463 6413524604218032367358195)
                ·
                  refine ⟨9620286906327048551037293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6413524604218032367358195 9620286906327048551037293)
                  ·
                    refine ⟨3607607589872643206638985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9620286906327048551037293 3607607589872643206638985)
                    ·
                      refine ⟨2705705692404482404979239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607607589872643206638985 2705705692404482404979239)
                      ·
                        rfl

theorem cell23_5269343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_5269343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269343 prefixEnd_5269343 := by exact prefixLift 5269343
  have htrace : WordTrace (prefixWord ++ tailWord_5269343) baseStart_5269343 baseEnd_5269343 := by
    simpa [prefixWord, tailWord_5269343, baseEnd_5269343] using wordTrace_append hprefix tailTrace_5269343
  have hstable : (prefixWord ++ tailWord_5269343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269343).length < 2 ^ (prefixWord ++ tailWord_5269343).sum := by decide
  have hdescent : baseEnd_5269343 < baseStart_5269343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269362 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 7]
def baseStart_5269362 : Nat := 118140960795 + 5269362 * 2 ^ 59
def prefixEnd_5269362 : Nat := 4983230072969 + 3 ^ 40 * 5269362 * 2
def baseEnd_5269362 : Nat := 300635049837435314515739

theorem tailTrace_5269362 : CollatzResearch.WordTrace tailWord_5269362 prefixEnd_5269362 300635049837435314515739 := by
  unfold tailWord_5269362
  simp only [CollatzResearch.WordTrace]
  refine ⟨48047355284002221056798585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128126280757339256151462893 48047355284002221056798585)
  ·
    refine ⟨36035516463001665792598939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48047355284002221056798585 36035516463001665792598939)
    ·
      refine ⟨54053274694502498688898409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36035516463001665792598939 54053274694502498688898409)
      ·
        refine ⟨40539956020876874016673807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54053274694502498688898409 40539956020876874016673807)
        ·
          refine ⟨60809934031315311025010711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40539956020876874016673807 60809934031315311025010711)
          ·
            refine ⟨91214901046972966537516067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60809934031315311025010711 91214901046972966537516067)
            ·
              refine ⟨136822351570459449806274101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91214901046972966537516067 136822351570459449806274101)
              ·
                refine ⟨12827095459730573419338197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136822351570459449806274101 12827095459730573419338197)
                ·
                  refine ⟨300635049837435314515739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12827095459730573419338197 300635049837435314515739)
                  ·
                    rfl

theorem cell23_5269362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_5269362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269362 prefixEnd_5269362 := by exact prefixLift 5269362
  have htrace : WordTrace (prefixWord ++ tailWord_5269362) baseStart_5269362 baseEnd_5269362 := by
    simpa [prefixWord, tailWord_5269362, baseEnd_5269362] using wordTrace_append hprefix tailTrace_5269362
  have hstable : (prefixWord ++ tailWord_5269362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269362).length < 2 ^ (prefixWord ++ tailWord_5269362).sum := by decide
  have hdescent : baseEnd_5269362 < baseStart_5269362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269366 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_5269366 : Nat := 118140960795 + 5269366 * 2 ^ 59
def prefixEnd_5269366 : Nat := 4983230072969 + 3 ^ 40 * 5269366 * 2
def baseEnd_5269366 : Nat := 901905834153178604997211

theorem tailTrace_5269366 : CollatzResearch.WordTrace tailWord_5269366 prefixEnd_5269366 901905834153178604997211 := by
  unfold tailWord_5269366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12011847939249649556896247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128126378018662928606893301 12011847939249649556896247)
  ·
    refine ⟨18017771908874474335344371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12011847939249649556896247 18017771908874474335344371)
    ·
      refine ⟨27026657863311711503016557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18017771908874474335344371 27026657863311711503016557)
      ·
        refine ⟨10134996698741891813631209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27026657863311711503016557 10134996698741891813631209)
        ·
          refine ⟨7601247524056418860223407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10134996698741891813631209 7601247524056418860223407)
          ·
            refine ⟨11401871286084628290335111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601247524056418860223407 11401871286084628290335111)
            ·
              refine ⟨17102806929126942435502667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11401871286084628290335111 17102806929126942435502667)
              ·
                refine ⟨25654210393690413653254001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17102806929126942435502667 25654210393690413653254001)
                ·
                  refine ⟨19240657795267810239940501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25654210393690413653254001 19240657795267810239940501)
                  ·
                    refine ⟨901905834153178604997211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19240657795267810239940501 901905834153178604997211)
                    ·
                      rfl

theorem cell23_5269366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_5269366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269366 prefixEnd_5269366 := by exact prefixLift 5269366
  have htrace : WordTrace (prefixWord ++ tailWord_5269366) baseStart_5269366 baseEnd_5269366 := by
    simpa [prefixWord, tailWord_5269366, baseEnd_5269366] using wordTrace_append hprefix tailTrace_5269366
  have hstable : (prefixWord ++ tailWord_5269366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269366).length < 2 ^ (prefixWord ++ tailWord_5269366).sum := by decide
  have hdescent : baseEnd_5269366 < baseStart_5269366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269396 : List Nat := [2, 4, 2, 1, 1, 2, 1, 5, 5]
def baseStart_5269396 : Nat := 118140960795 + 5269396 * 2 ^ 59
def prefixEnd_5269396 : Nat := 4983230072969 + 3 ^ 40 * 5269396 * 2
def baseEnd_5269396 : Nat := 300636989653241188624055

theorem tailTrace_5269396 : CollatzResearch.WordTrace tailWord_5269396 prefixEnd_5269396 300636989653241188624055 := by
  unfold tailWord_5269396
  simp only [CollatzResearch.WordTrace]
  refine ⟨96095330608942854016966021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128127107478590472022621361 96095330608942854016966021)
  ·
    refine ⟨18017874489176785128181129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96095330608942854016966021 18017874489176785128181129)
    ·
      refine ⟨13513405866882588846135847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18017874489176785128181129 13513405866882588846135847)
      ·
        refine ⟨20270108800323883269203771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13513405866882588846135847 20270108800323883269203771)
        ·
          refine ⟨30405163200485824903805657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20270108800323883269203771 30405163200485824903805657)
          ·
            refine ⟨22803872400364368677854243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30405163200485824903805657 22803872400364368677854243)
            ·
              refine ⟨34205808600546553016781365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22803872400364368677854243 34205808600546553016781365)
              ·
                refine ⟨3206794556301239345323253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34205808600546553016781365 3206794556301239345323253)
                ·
                  refine ⟨300636989653241188624055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206794556301239345323253 300636989653241188624055)
                  ·
                    rfl

theorem cell23_5269396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_5269396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269396 prefixEnd_5269396 := by exact prefixLift 5269396
  have htrace : WordTrace (prefixWord ++ tailWord_5269396) baseStart_5269396 baseEnd_5269396 := by
    simpa [prefixWord, tailWord_5269396, baseEnd_5269396] using wordTrace_append hprefix tailTrace_5269396
  have hstable : (prefixWord ++ tailWord_5269396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269396).length < 2 ^ (prefixWord ++ tailWord_5269396).sum := by decide
  have hdescent : baseEnd_5269396 < baseStart_5269396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269407 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 2, 2, 2]
def baseStart_5269407 : Nat := 118140960795 + 5269407 * 2 ^ 59
def prefixEnd_5269407 : Nat := 4983230072969 + 3 ^ 40 * 5269407 * 2
def baseEnd_5269407 : Nat := 2705738555166370154578945

theorem tailTrace_5269407 : CollatzResearch.WordTrace tailWord_5269407 prefixEnd_5269407 2705738555166370154578945 := by
  unfold tailWord_5269407
  simp only [CollatzResearch.WordTrace]
  refine ⟨192191062420845856912582475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128127374947230571275054983 192191062420845856912582475)
  ·
    refine ⟨288286593631268785368873713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192191062420845856912582475 288286593631268785368873713)
    ·
      refine ⟨216214945223451589026655285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288286593631268785368873713 216214945223451589026655285)
      ·
        refine ⟨20270151114698586471248933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216214945223451589026655285 20270151114698586471248933)
        ·
          refine ⟨3800653334005984963359175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20270151114698586471248933 3800653334005984963359175)
          ·
            refine ⟨5700980001008977445038763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800653334005984963359175 5700980001008977445038763)
            ·
              refine ⟨8551470001513466167558145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700980001008977445038763 8551470001513466167558145)
              ·
                refine ⟨6413602501135099625668609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8551470001513466167558145 6413602501135099625668609)
                ·
                  refine ⟨4810201875851324719251457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413602501135099625668609 4810201875851324719251457)
                  ·
                    refine ⟨3607651406888493539438593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810201875851324719251457 3607651406888493539438593)
                    ·
                      refine ⟨2705738555166370154578945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607651406888493539438593 2705738555166370154578945)
                      ·
                        rfl

theorem cell23_5269407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_5269407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269407 prefixEnd_5269407 := by exact prefixLift 5269407
  have htrace : WordTrace (prefixWord ++ tailWord_5269407) baseStart_5269407 baseEnd_5269407 := by
    simpa [prefixWord, tailWord_5269407, baseEnd_5269407] using wordTrace_append hprefix tailTrace_5269407
  have hstable : (prefixWord ++ tailWord_5269407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269407).length < 2 ^ (prefixWord ++ tailWord_5269407).sum := by decide
  have hdescent : baseEnd_5269407 < baseStart_5269407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269429 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_5269429 : Nat := 118140960795 + 5269429 * 2 ^ 59
def prefixEnd_5269429 : Nat := 4983230072969 + 3 ^ 40 * 5269429 * 2
def baseEnd_5269429 : Nat := 2705749851740769068503843

theorem tailTrace_5269429 : CollatzResearch.WordTrace tailWord_5269429 prefixEnd_5269429 2705749851740769068503843 := by
  unfold tailWord_5269429
  simp only [CollatzResearch.WordTrace]
  refine ⟨192191864826766154669883341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128127909884510769779922227 192191864826766154669883341)
  ·
    refine ⟨72071949310037308001206253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192191864826766154669883341 72071949310037308001206253)
    ·
      refine ⟨27026980991263990500452345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72071949310037308001206253 27026980991263990500452345)
      ·
        refine ⟨20270235743447992875339259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27026980991263990500452345 20270235743447992875339259)
        ·
          refine ⟨30405353615171989313008889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20270235743447992875339259 30405353615171989313008889)
          ·
            refine ⟨22804015211378991984756667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30405353615171989313008889 22804015211378991984756667)
            ·
              refine ⟨34206022817068487977135001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22804015211378991984756667 34206022817068487977135001)
              ·
                refine ⟨25654517112801365982851251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34206022817068487977135001 25654517112801365982851251)
                ·
                  refine ⟨38481775669202048974276877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25654517112801365982851251 38481775669202048974276877)
                  ·
                    refine ⟨14430665875950768365353829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38481775669202048974276877 14430665875950768365353829)
                    ·
                      refine ⟨2705749851740769068503843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14430665875950768365353829 2705749851740769068503843)
                      ·
                        rfl

theorem cell23_5269429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_5269429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269429 prefixEnd_5269429 := by exact prefixLift 5269429
  have htrace : WordTrace (prefixWord ++ tailWord_5269429) baseStart_5269429 baseEnd_5269429 := by
    simpa [prefixWord, tailWord_5269429, baseEnd_5269429] using wordTrace_append hprefix tailTrace_5269429
  have hstable : (prefixWord ++ tailWord_5269429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269429).length < 2 ^ (prefixWord ++ tailWord_5269429).sum := by decide
  have hdescent : baseEnd_5269429 < baseStart_5269429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269439 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 3, 4]
def baseStart_5269439 : Nat := 118140960795 + 5269439 * 2 ^ 59
def prefixEnd_5269439 : Nat := 4983230072969 + 3 ^ 40 * 5269439 * 2
def baseEnd_5269439 : Nat := 901918328849104676459599

theorem tailTrace_5269439 : CollatzResearch.WordTrace tailWord_5269439 prefixEnd_5269439 901918328849104676459599 := by
  unfold tailWord_5269439
  simp only [CollatzResearch.WordTrace]
  refine ⟨192192229556729926377747371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128128153037819950918498247 192192229556729926377747371)
  ·
    refine ⟨288288344335094889566621057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192192229556729926377747371 288288344335094889566621057)
    ·
      refine ⟨216216258251321167174965793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288288344335094889566621057 216216258251321167174965793)
      ·
        refine ⟨162162193688490875381224345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216216258251321167174965793 162162193688490875381224345)
        ·
          refine ⟨121621645266368156535918259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162162193688490875381224345 121621645266368156535918259)
          ·
            refine ⟨182432467899552234803877389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121621645266368156535918259 182432467899552234803877389)
            ·
              refine ⟨68412175462332088051454021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182432467899552234803877389 68412175462332088051454021)
              ·
                refine ⟨12827282899187266509647629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68412175462332088051454021 12827282899187266509647629)
                ·
                  refine ⟨4810231087195224941117861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12827282899187266509647629 4810231087195224941117861)
                  ·
                    refine ⟨901918328849104676459599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810231087195224941117861 901918328849104676459599)
                    ·
                      rfl

theorem cell23_5269439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 4].length) (baseStart_5269439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269439 prefixEnd_5269439 := by exact prefixLift 5269439
  have htrace : WordTrace (prefixWord ++ tailWord_5269439) baseStart_5269439 baseEnd_5269439 := by
    simpa [prefixWord, tailWord_5269439, baseEnd_5269439] using wordTrace_append hprefix tailTrace_5269439
  have hstable : (prefixWord ++ tailWord_5269439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269439).length < 2 ^ (prefixWord ++ tailWord_5269439).sum := by decide
  have hdescent : baseEnd_5269439 < baseStart_5269439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269472 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_5269472 : Nat := 118140960795 + 5269472 * 2 ^ 59
def prefixEnd_5269472 : Nat := 4983230072969 + 3 ^ 40 * 5269472 * 2
def baseEnd_5269472 : Nat := 2705771931408912400266145

theorem tailTrace_5269472 : CollatzResearch.WordTrace tailWord_5269472 prefixEnd_5269472 2705771931408912400266145 := by
  unfold tailWord_5269472
  simp only [CollatzResearch.WordTrace]
  refine ⟨96096716582805186506849335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128128955443740248675799113 96096716582805186506849335)
  ·
    refine ⟨144145074874207779760274003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96096716582805186506849335 144145074874207779760274003)
    ·
      refine ⟨216217612311311669640411005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144145074874207779760274003 216217612311311669640411005)
      ·
        refine ⟨81081604616741876115154127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216217612311311669640411005 81081604616741876115154127)
        ·
          refine ⟨121622406925112814172731191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81081604616741876115154127 121622406925112814172731191)
          ·
            refine ⟨182433610387669221259096787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121622406925112814172731191 182433610387669221259096787)
            ·
              refine ⟨273650415581503831888645181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182433610387669221259096787 273650415581503831888645181)
              ·
                refine ⟨102618905843063936958241943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273650415581503831888645181 102618905843063936958241943)
                ·
                  refine ⟨153928358764595905437362915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102618905843063936958241943 153928358764595905437362915)
                  ·
                    refine ⟨230892538146893858156044373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153928358764595905437362915 230892538146893858156044373)
                    ·
                      refine ⟨2705771931408912400266145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 230892538146893858156044373 2705771931408912400266145)
                      ·
                        rfl

theorem cell23_5269472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_5269472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269472 prefixEnd_5269472 := by exact prefixLift 5269472
  have htrace : WordTrace (prefixWord ++ tailWord_5269472) baseStart_5269472 baseEnd_5269472 := by
    simpa [prefixWord, tailWord_5269472, baseEnd_5269472] using wordTrace_append hprefix tailTrace_5269472
  have hstable : (prefixWord ++ tailWord_5269472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269472).length < 2 ^ (prefixWord ++ tailWord_5269472).sum := by decide
  have hdescent : baseEnd_5269472 < baseStart_5269472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269486 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_5269486 : Nat := 118140960795 + 5269486 * 2 ^ 59
def prefixEnd_5269486 : Nat := 4983230072969 + 3 ^ 40 * 5269486 * 2
def baseEnd_5269486 : Nat := 300642124459786149499009

theorem tailTrace_5269486 : CollatzResearch.WordTrace tailWord_5269486 prefixEnd_5269486 300642124459786149499009 := by
  unfold tailWord_5269486
  simp only [CollatzResearch.WordTrace]
  refine ⟨24024242973444956675588539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128129295858373102269805541 24024242973444956675588539)
  ·
    refine ⟨36036364460167435013382809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24024242973444956675588539 36036364460167435013382809)
    ·
      refine ⟨27027273345125576260037107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36036364460167435013382809 27027273345125576260037107)
      ·
        refine ⟨40540910017688364390055661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27027273345125576260037107 40540910017688364390055661)
        ·
          refine ⟨15202841256633136646270873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40540910017688364390055661 15202841256633136646270873)
          ·
            refine ⟨11402130942474852484703155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15202841256633136646270873 11402130942474852484703155)
            ·
              refine ⟨17103196413712278727054733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11402130942474852484703155 17103196413712278727054733)
              ·
                refine ⟨6413698655142104522645525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17103196413712278727054733 6413698655142104522645525)
                ·
                  refine ⟨300642124459786149499009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6413698655142104522645525 300642124459786149499009)
                  ·
                    rfl

theorem cell23_5269486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_5269486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269486 prefixEnd_5269486 := by exact prefixLift 5269486
  have htrace : WordTrace (prefixWord ++ tailWord_5269486) baseStart_5269486 baseEnd_5269486 := by
    simpa [prefixWord, tailWord_5269486, baseEnd_5269486] using wordTrace_append hprefix tailTrace_5269486
  have hstable : (prefixWord ++ tailWord_5269486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269486).length < 2 ^ (prefixWord ++ tailWord_5269486).sum := by decide
  have hdescent : baseEnd_5269486 < baseStart_5269486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269496 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_5269496 : Nat := 118140960795 + 5269496 * 2 ^ 59
def prefixEnd_5269496 : Nat := 4983230072969 + 3 ^ 40 * 5269496 * 2
def baseEnd_5269496 : Nat := 2705784254944620306366035

theorem tailTrace_5269496 : CollatzResearch.WordTrace tailWord_5269496 prefixEnd_5269496 2705784254944620306366035 := by
  unfold tailWord_5269496
  simp only [CollatzResearch.WordTrace]
  refine ⟨96097154258761712556286171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128129539011682283408381561 96097154258761712556286171)
  ·
    refine ⟨144145731388142568834429257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96097154258761712556286171 144145731388142568834429257)
    ·
      refine ⟨108109298541106926625821943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144145731388142568834429257 108109298541106926625821943)
      ·
        refine ⟨162163947811660389938732915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108109298541106926625821943 162163947811660389938732915)
        ·
          refine ⟨243245921717490584908099373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162163947811660389938732915 243245921717490584908099373)
          ·
            refine ⟨91217220644058969340537265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243245921717490584908099373 91217220644058969340537265)
            ·
              refine ⟨68412915483044227005402949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91217220644058969340537265 68412915483044227005402949)
              ·
                refine ⟨12827421653070792563513053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68412915483044227005402949 12827421653070792563513053)
                ·
                  refine ⟨4810283119901547211317395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12827421653070792563513053 4810283119901547211317395)
                  ·
                    refine ⟨7215424679852320816976093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810283119901547211317395 7215424679852320816976093)
                    ·
                      refine ⟨2705784254944620306366035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215424679852320816976093 2705784254944620306366035)
                      ·
                        rfl

theorem cell23_5269496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_5269496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269496 prefixEnd_5269496 := by exact prefixLift 5269496
  have htrace : WordTrace (prefixWord ++ tailWord_5269496) baseStart_5269496 baseEnd_5269496 := by
    simpa [prefixWord, tailWord_5269496, baseEnd_5269496] using wordTrace_append hprefix tailTrace_5269496
  have hstable : (prefixWord ++ tailWord_5269496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269496).length < 2 ^ (prefixWord ++ tailWord_5269496).sum := by decide
  have hdescent : baseEnd_5269496 < baseStart_5269496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269530 : List Nat := [3, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3]
def baseStart_5269530 : Nat := 118140960795 + 5269530 * 2 ^ 59
def prefixEnd_5269530 : Nat := 4983230072969 + 3 ^ 40 * 5269530 * 2
def baseEnd_5269530 : Nat := 2705801713286873173340879

theorem tailTrace_5269530 : CollatzResearch.WordTrace tailWord_5269530 prefixEnd_5269530 2705801713286873173340879 := by
  unfold tailWord_5269530
  simp only [CollatzResearch.WordTrace]
  refine ⟨48048887149850062229827511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128130365732933499279540029 48048887149850062229827511)
  ·
    refine ⟨72073330724775093344741267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48048887149850062229827511 72073330724775093344741267)
    ·
      refine ⟨108109996087162640017111901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72073330724775093344741267 108109996087162640017111901)
      ·
        refine ⟨40541248532685990006416963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108109996087162640017111901 40541248532685990006416963)
        ·
          refine ⟨60811872799028985009625445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40541248532685990006416963 60811872799028985009625445)
          ·
            refine ⟨11402226149817934689304771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60811872799028985009625445 11402226149817934689304771)
            ·
              refine ⟨17103339224726902033957157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11402226149817934689304771 17103339224726902033957157)
              ·
                refine ⟨3206876104636294131366967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17103339224726902033957157 3206876104636294131366967)
                ·
                  refine ⟨4810314156954441197050451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206876104636294131366967 4810314156954441197050451)
                  ·
                    refine ⟨7215471235431661795575677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810314156954441197050451 7215471235431661795575677)
                    ·
                      refine ⟨2705801713286873173340879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215471235431661795575677 2705801713286873173340879)
                      ·
                        rfl

theorem cell23_5269530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_5269530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269530 prefixEnd_5269530 := by exact prefixLift 5269530
  have htrace : WordTrace (prefixWord ++ tailWord_5269530) baseStart_5269530 baseEnd_5269530 := by
    simpa [prefixWord, tailWord_5269530, baseEnd_5269530] using wordTrace_append hprefix tailTrace_5269530
  have hstable : (prefixWord ++ tailWord_5269530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269530).length < 2 ^ (prefixWord ++ tailWord_5269530).sum := by decide
  have hdescent : baseEnd_5269530 < baseStart_5269530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269539 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 5]
def baseStart_5269539 : Nat := 118140960795 + 5269539 * 2 ^ 59
def prefixEnd_5269539 : Nat := 4983230072969 + 3 ^ 40 * 5269539 * 2
def baseEnd_5269539 : Nat := 2705806334612763638128337

theorem tailTrace_5269539 : CollatzResearch.WordTrace tailWord_5269539 prefixEnd_5269539 2705806334612763638128337 := by
  unfold tailWord_5269539
  simp only [CollatzResearch.WordTrace]
  refine ⟨192195876856367643456387671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128130584570911762304258447 192195876856367643456387671)
  ·
    refine ⟨288293815284551465184581507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192195876856367643456387671 288293815284551465184581507)
    ·
      refine ⟨432440722926827197776872261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288293815284551465184581507 432440722926827197776872261)
      ·
        refine ⟨81082635548780099583163549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 432440722926827197776872261 81082635548780099583163549)
        ·
          refine ⟨30405988330792537343686331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81082635548780099583163549 30405988330792537343686331)
          ·
            refine ⟨45608982496188806015529497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30405988330792537343686331 45608982496188806015529497)
            ·
              refine ⟨34206736872141604511647123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45608982496188806015529497 34206736872141604511647123)
              ·
                refine ⟨51310105308212406767470685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34206736872141604511647123 51310105308212406767470685)
                ·
                  refine ⟨19241289490579652537801507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51310105308212406767470685 19241289490579652537801507)
                  ·
                    refine ⟨28861934235869478806702261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19241289490579652537801507 28861934235869478806702261)
                    ·
                      refine ⟨2705806334612763638128337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28861934235869478806702261 2705806334612763638128337)
                      ·
                        rfl

theorem cell23_5269539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_5269539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269539 prefixEnd_5269539 := by exact prefixLift 5269539
  have htrace : WordTrace (prefixWord ++ tailWord_5269539) baseStart_5269539 baseEnd_5269539 := by
    simpa [prefixWord, tailWord_5269539, baseEnd_5269539] using wordTrace_append hprefix tailTrace_5269539
  have hstable : (prefixWord ++ tailWord_5269539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269539).length < 2 ^ (prefixWord ++ tailWord_5269539).sum := by decide
  have hdescent : baseEnd_5269539 < baseStart_5269539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269546 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_5269546 : Nat := 118140960795 + 5269546 * 2 ^ 59
def prefixEnd_5269546 : Nat := 4983230072969 + 3 ^ 40 * 5269546 * 2
def baseEnd_5269546 : Nat := 901936642992448370246935

theorem tailTrace_5269546 : CollatzResearch.WordTrace tailWord_5269546 prefixEnd_5269546 901936642992448370246935 := by
  unfold tailWord_5269546
  simp only [CollatzResearch.WordTrace]
  refine ⟨48049033041835570912973123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128130754778228189101261661 48049033041835570912973123)
  ·
    refine ⟨72073549562753356369459685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48049033041835570912973123 72073549562753356369459685)
    ·
      refine ⟨13513790543016254319273691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72073549562753356369459685 13513790543016254319273691)
      ·
        refine ⟨20270685814524381478910537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13513790543016254319273691 20270685814524381478910537)
        ·
          refine ⟨15203014360893286109182903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20270685814524381478910537 15203014360893286109182903)
          ·
            refine ⟨22804521541339929163774355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15203014360893286109182903 22804521541339929163774355)
            ·
              refine ⟨34206782312009893745661533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22804521541339929163774355 34206782312009893745661533)
              ·
                refine ⟨12827543367003710154623075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34206782312009893745661533 12827543367003710154623075)
                ·
                  refine ⟨19241315050505565231934613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12827543367003710154623075 19241315050505565231934613)
                  ·
                    refine ⟨901936642992448370246935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19241315050505565231934613 901936642992448370246935)
                    ·
                      rfl

theorem cell23_5269546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_5269546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269546 prefixEnd_5269546 := by exact prefixLift 5269546
  have htrace : WordTrace (prefixWord ++ tailWord_5269546) baseStart_5269546 baseEnd_5269546 := by
    simpa [prefixWord, tailWord_5269546, baseEnd_5269546] using wordTrace_append hprefix tailTrace_5269546
  have hstable : (prefixWord ++ tailWord_5269546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269546).length < 2 ^ (prefixWord ++ tailWord_5269546).sum := by decide
  have hdescent : baseEnd_5269546 < baseStart_5269546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269553 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 5, 2, 2]
def baseStart_5269553 : Nat := 118140960795 + 5269553 * 2 ^ 59
def prefixEnd_5269553 : Nat := 4983230072969 + 3 ^ 40 * 5269553 * 2
def baseEnd_5269553 : Nat := 2705813523341926583353273

theorem tailTrace_5269553 : CollatzResearch.WordTrace tailWord_5269553 prefixEnd_5269553 2705813523341926583353273 := by
  unfold tailWord_5269553
  simp only [CollatzResearch.WordTrace]
  refine ⟨192196387478316923847397313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128130924985544615898264875 192196387478316923847397313)
  ·
    refine ⟨144147290608737692885547985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192196387478316923847397313 144147290608737692885547985)
    ·
      refine ⟨108110467956553269664160989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144147290608737692885547985 108110467956553269664160989)
      ·
        refine ⟨40541425483707476124060371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108110467956553269664160989 40541425483707476124060371)
        ·
          refine ⟨60812138225561214186090557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40541425483707476124060371 60812138225561214186090557)
          ·
            refine ⟨22804551834585455319783959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60812138225561214186090557 22804551834585455319783959)
            ·
              refine ⟨34206827751878182979675939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22804551834585455319783959 34206827751878182979675939)
              ·
                refine ⟨51310241627817274469513909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34206827751878182979675939 51310241627817274469513909)
                ·
                  refine ⟨4810335152607869481516929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51310241627817274469513909 4810335152607869481516929)
                  ·
                    refine ⟨3607751364455902111137697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810335152607869481516929 3607751364455902111137697)
                    ·
                      refine ⟨2705813523341926583353273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607751364455902111137697 2705813523341926583353273)
                      ·
                        rfl

theorem cell23_5269553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_5269553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269553 prefixEnd_5269553 := by exact prefixLift 5269553
  have htrace : WordTrace (prefixWord ++ tailWord_5269553) baseStart_5269553 baseEnd_5269553 := by
    simpa [prefixWord, tailWord_5269553, baseEnd_5269553] using wordTrace_append hprefix tailTrace_5269553
  have hstable : (prefixWord ++ tailWord_5269553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269553).length < 2 ^ (prefixWord ++ tailWord_5269553).sum := by decide
  have hdescent : baseEnd_5269553 < baseStart_5269553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269590 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5269590 : Nat := 118140960795 + 5269590 * 2 ^ 59
def prefixEnd_5269590 : Nat := 4983230072969 + 3 ^ 40 * 5269590 * 2
def baseEnd_5269590 : Nat := 2705832522126142938590603

theorem tailTrace_5269590 : CollatzResearch.WordTrace tailWord_5269590 prefixEnd_5269590 2705832522126142938590603 := by
  unfold tailWord_5269590
  simp only [CollatzResearch.WordTrace]
  refine ⟨12012358561198929947905889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128131824652788586110996149 12012358561198929947905889)
  ·
    refine ⟨9009268920899197460929417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12012358561198929947905889 9009268920899197460929417)
    ·
      refine ⟨6756951690674398095697063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9009268920899197460929417 6756951690674398095697063)
      ·
        refine ⟨10135427536011597143545595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756951690674398095697063 10135427536011597143545595)
        ·
          refine ⟨15203141304017395715318393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10135427536011597143545595 15203141304017395715318393)
          ·
            refine ⟨11402355978013046786488795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15203141304017395715318393 11402355978013046786488795)
            ·
              refine ⟨17103533967019570179733193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11402355978013046786488795 17103533967019570179733193)
              ·
                refine ⟨12827650475264677634799895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17103533967019570179733193 12827650475264677634799895)
                ·
                  refine ⟨19241475712897016452199843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12827650475264677634799895 19241475712897016452199843)
                  ·
                    refine ⟨28862213569345524678299765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19241475712897016452199843 28862213569345524678299765)
                    ·
                      refine ⟨2705832522126142938590603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28862213569345524678299765 2705832522126142938590603)
                      ·
                        rfl

theorem cell23_5269590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5269590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269590 prefixEnd_5269590 := by exact prefixLift 5269590
  have htrace : WordTrace (prefixWord ++ tailWord_5269590) baseStart_5269590 baseEnd_5269590 := by
    simpa [prefixWord, tailWord_5269590, baseEnd_5269590] using wordTrace_append hprefix tailTrace_5269590
  have hstable : (prefixWord ++ tailWord_5269590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269590).length < 2 ^ (prefixWord ++ tailWord_5269590).sum := by decide
  have hdescent : baseEnd_5269590 < baseStart_5269590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269597 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5269597 : Nat := 118140960795 + 5269597 * 2 ^ 59
def prefixEnd_5269597 : Nat := 4983230072969 + 3 ^ 40 * 5269597 * 2
def baseEnd_5269597 : Nat := 901945372163574803734357

theorem tailTrace_5269597 : CollatzResearch.WordTrace tailWord_5269597 prefixEnd_5269597 901945372163574803734357 := by
  unfold tailWord_5269597
  simp only [CollatzResearch.WordTrace]
  refine ⟨192197992290157519361999045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128131994860105012907999363 192197992290157519361999045)
  ·
    refine ⟨36037123554404534880374821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192197992290157519361999045 36037123554404534880374821)
    ·
      refine ⟨6756960666450850290070279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36037123554404534880374821 6756960666450850290070279)
      ·
        refine ⟨10135440999676275435105419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756960666450850290070279 10135440999676275435105419)
        ·
          refine ⟨15203161499514413152658129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10135440999676275435105419 15203161499514413152658129)
          ·
            refine ⟨11402371124635809864493597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15203161499514413152658129 11402371124635809864493597)
            ·
              refine ⟨4275889171738428699185099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11402371124635809864493597 4275889171738428699185099)
              ·
                refine ⟨6413833757607643048777649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275889171738428699185099 6413833757607643048777649)
                ·
                  refine ⟨4810375318205732286583237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413833757607643048777649 4810375318205732286583237)
                  ·
                    refine ⟨901945372163574803734357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810375318205732286583237 901945372163574803734357)
                    ·
                      rfl

theorem cell23_5269597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5269597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269597 prefixEnd_5269597 := by exact prefixLift 5269597
  have htrace : WordTrace (prefixWord ++ tailWord_5269597) baseStart_5269597 baseEnd_5269597 := by
    simpa [prefixWord, tailWord_5269597, baseEnd_5269597] using wordTrace_append hprefix tailTrace_5269597
  have hstable : (prefixWord ++ tailWord_5269597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269597).length < 2 ^ (prefixWord ++ tailWord_5269597).sum := by decide
  have hdescent : baseEnd_5269597 < baseStart_5269597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269603 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 3]
def baseStart_5269603 : Nat := 118140960795 + 5269603 * 2 ^ 59
def prefixEnd_5269603 : Nat := 4983230072969 + 3 ^ 40 * 5269603 * 2
def baseEnd_5269603 : Nat := 2705839197374651387728043

theorem tailTrace_5269603 : CollatzResearch.WordTrace tailWord_5269603 prefixEnd_5269603 2705839197374651387728043 := by
  unfold tailWord_5269603
  simp only [CollatzResearch.WordTrace]
  refine ⟨192198211128135782386717463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128132140752090521591144975 192198211128135782386717463)
  ·
    refine ⟨288297316692203673580076195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192198211128135782386717463 288297316692203673580076195)
    ·
      refine ⟨432445975038305510370114293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288297316692203673580076195 432445975038305510370114293)
      ·
        refine ⟨40541810159841141597198215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 432445975038305510370114293 40541810159841141597198215)
        ·
          refine ⟨60812715239761712395797323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40541810159841141597198215 60812715239761712395797323)
          ·
            refine ⟨91219072859642568593695985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60812715239761712395797323 91219072859642568593695985)
            ·
              refine ⟨68414304644731926445271989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91219072859642568593695985 68414304644731926445271989)
              ·
                refine ⟨6413841060443618104244249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68414304644731926445271989 6413841060443618104244249)
                ·
                  refine ⟨4810380795332713578183187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413841060443618104244249 4810380795332713578183187)
                  ·
                    refine ⟨7215571192999070367274781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810380795332713578183187 7215571192999070367274781)
                    ·
                      refine ⟨2705839197374651387728043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215571192999070367274781 2705839197374651387728043)
                      ·
                        rfl

theorem cell23_5269603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_5269603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269603 prefixEnd_5269603 := by exact prefixLift 5269603
  have htrace : WordTrace (prefixWord ++ tailWord_5269603) baseStart_5269603 baseEnd_5269603 := by
    simpa [prefixWord, tailWord_5269603, baseEnd_5269603] using wordTrace_append hprefix tailTrace_5269603
  have hstable : (prefixWord ++ tailWord_5269603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269603).length < 2 ^ (prefixWord ++ tailWord_5269603).sum := by decide
  have hdescent : baseEnd_5269603 < baseStart_5269603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269610 : List Nat := [3, 1, 3, 2, 4, 1, 2, 7]
def baseStart_5269610 : Nat := 118140960795 + 5269610 * 2 ^ 59
def prefixEnd_5269610 : Nat := 4983230072969 + 3 ^ 40 * 5269610 * 2
def baseEnd_5269610 : Nat := 100216399694045661494093

theorem tailTrace_5269610 : CollatzResearch.WordTrace tailWord_5269610 prefixEnd_5269610 100216399694045661494093 := by
  unfold tailWord_5269610
  simp only [CollatzResearch.WordTrace]
  refine ⟨48049616609777605645555571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128132310959406948388148189 48049616609777605645555571)
  ·
    refine ⟨72074424914666408468333357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48049616609777605645555571 72074424914666408468333357)
    ·
      refine ⟨27027909342999903175625009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72074424914666408468333357 27027909342999903175625009)
      ·
        refine ⟨20270932007249927381718757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27027909342999903175625009 20270932007249927381718757)
        ·
          refine ⟨3800799751359361384072267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20270932007249927381718757 3800799751359361384072267)
          ·
            refine ⟨5701199627039042076108401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800799751359361384072267 5701199627039042076108401)
            ·
              refine ⟨4275899720279281557081301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701199627039042076108401 4275899720279281557081301)
              ·
                refine ⟨100216399694045661494093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4275899720279281557081301 100216399694045661494093)
                ·
                  rfl

theorem cell23_5269610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 7].length) (baseStart_5269610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269610 prefixEnd_5269610 := by exact prefixLift 5269610
  have htrace : WordTrace (prefixWord ++ tailWord_5269610) baseStart_5269610 baseEnd_5269610 := by
    simpa [prefixWord, tailWord_5269610, baseEnd_5269610] using wordTrace_append hprefix tailTrace_5269610
  have hstable : (prefixWord ++ tailWord_5269610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269610).length < 2 ^ (prefixWord ++ tailWord_5269610).sum := by decide
  have hdescent : baseEnd_5269610 < baseStart_5269610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269694 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_5269694 : Nat := 118140960795 + 5269694 * 2 ^ 59
def prefixEnd_5269694 : Nat := 4983230072969 + 3 ^ 40 * 5269694 * 2
def baseEnd_5269694 : Nat := 2705885924114210531690125

theorem tailTrace_5269694 : CollatzResearch.WordTrace tailWord_5269694 prefixEnd_5269694 2705885924114210531690125 := by
  unfold tailWord_5269694
  simp only [CollatzResearch.WordTrace]
  refine ⟨24025191271350763116035017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128134353447204069952186757 24025191271350763116035017)
  ·
    refine ⟨18018893453513072337026263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24025191271350763116035017 18018893453513072337026263)
    ·
      refine ⟨27028340180269608505539395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18018893453513072337026263 27028340180269608505539395)
      ·
        refine ⟨40542510270404412758309093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27028340180269608505539395 40542510270404412758309093)
        ·
          refine ⟨7601720675700827392182955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40542510270404412758309093 7601720675700827392182955)
          ·
            refine ⟨11402581013551241088274433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601720675700827392182955 11402581013551241088274433)
            ·
              refine ⟨8551935760163430816205825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11402581013551241088274433 8551935760163430816205825)
              ·
                refine ⟨6413951820122573112154369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8551935760163430816205825 6413951820122573112154369)
                ·
                  refine ⟨4810463865091929834115777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413951820122573112154369 4810463865091929834115777)
                  ·
                    refine ⟨3607847898818947375586833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810463865091929834115777 3607847898818947375586833)
                    ·
                      refine ⟨2705885924114210531690125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607847898818947375586833 2705885924114210531690125)
                      ·
                        rfl

theorem cell23_5269694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_5269694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269694 prefixEnd_5269694 := by exact prefixLift 5269694
  have htrace : WordTrace (prefixWord ++ tailWord_5269694) baseStart_5269694 baseEnd_5269694 := by
    simpa [prefixWord, tailWord_5269694, baseEnd_5269694] using wordTrace_append hprefix tailTrace_5269694
  have hstable : (prefixWord ++ tailWord_5269694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269694).length < 2 ^ (prefixWord ++ tailWord_5269694).sum := by decide
  have hdescent : baseEnd_5269694 < baseStart_5269694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269700 : List Nat := [2, 3, 3, 1, 2, 2, 1, 4, 5]
def baseStart_5269700 : Nat := 118140960795 + 5269700 * 2 ^ 59
def prefixEnd_5269700 : Nat := 4983230072969 + 3 ^ 40 * 5269700 * 2
def baseEnd_5269700 : Nat := 300654333888681945357233

theorem tailTrace_5269700 : CollatzResearch.WordTrace tailWord_5269700 prefixEnd_5269700 300654333888681945357233 := by
  unfold tailWord_5269700
  simp only [CollatzResearch.WordTrace]
  refine ⟨96100874504392183976499277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128134499339189578635332369 96100874504392183976499277)
  ·
    refine ⟨36037827939147068991187229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96100874504392183976499277 36037827939147068991187229)
    ·
      refine ⟨13514185477180150871695211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36037827939147068991187229 13514185477180150871695211)
      ·
        refine ⟨20271278215770226307542817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13514185477180150871695211 20271278215770226307542817)
        ·
          refine ⟨15203458661827669730657113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20271278215770226307542817 15203458661827669730657113)
          ·
            refine ⟨11402593996370752297992835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15203458661827669730657113 11402593996370752297992835)
            ·
              refine ⟨17103890994556128446989253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11402593996370752297992835 17103890994556128446989253)
              ·
                refine ⟨3206979561479274083810485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17103890994556128446989253 3206979561479274083810485)
                ·
                  refine ⟨300654333888681945357233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206979561479274083810485 300654333888681945357233)
                  ·
                    rfl

theorem cell23_5269700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_5269700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269700 prefixEnd_5269700 := by exact prefixLift 5269700
  have htrace : WordTrace (prefixWord ++ tailWord_5269700) baseStart_5269700 baseEnd_5269700 := by
    simpa [prefixWord, tailWord_5269700, baseEnd_5269700] using wordTrace_append hprefix tailTrace_5269700
  have hstable : (prefixWord ++ tailWord_5269700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269700).length < 2 ^ (prefixWord ++ tailWord_5269700).sum := by decide
  have hdescent : baseEnd_5269700 < baseStart_5269700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269706 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_5269706 : Nat := 118140960795 + 5269706 * 2 ^ 59
def prefixEnd_5269706 : Nat := 4983230072969 + 3 ^ 40 * 5269706 * 2
def baseEnd_5269706 : Nat := 2705892085882064484740069

theorem tailTrace_5269706 : CollatzResearch.WordTrace tailWord_5269706 prefixEnd_5269706 2705892085882064484740069 := by
  unfold tailWord_5269706
  simp only [CollatzResearch.WordTrace]
  refine ⟨48050491961690657744429243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128134645231175087318477981 48050491961690657744429243)
  ·
    refine ⟨72075737942535986616643865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48050491961690657744429243 72075737942535986616643865)
    ·
      refine ⟨54056803456901989962482899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72075737942535986616643865 54056803456901989962482899)
      ·
        refine ⟨81085205185352984943724349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54056803456901989962482899 81085205185352984943724349)
        ·
          refine ⟨30406951944507369353896631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81085205185352984943724349 30406951944507369353896631)
          ·
            refine ⟨45610427916761054030844947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30406951944507369353896631 45610427916761054030844947)
            ·
              refine ⟨68415641875141581046267421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45610427916761054030844947 68415641875141581046267421)
              ·
                refine ⟨25655865703178092892350283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68415641875141581046267421 25655865703178092892350283)
                ·
                  refine ⟨38483798554767139338525425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25655865703178092892350283 38483798554767139338525425)
                  ·
                    refine ⟨28862848916075354503894069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38483798554767139338525425 28862848916075354503894069)
                    ·
                      refine ⟨2705892085882064484740069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28862848916075354503894069 2705892085882064484740069)
                      ·
                        rfl

theorem cell23_5269706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_5269706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269706 prefixEnd_5269706 := by exact prefixLift 5269706
  have htrace : WordTrace (prefixWord ++ tailWord_5269706) baseStart_5269706 baseEnd_5269706 := by
    simpa [prefixWord, tailWord_5269706, baseEnd_5269706] using wordTrace_append hprefix tailTrace_5269706
  have hstable : (prefixWord ++ tailWord_5269706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269706).length < 2 ^ (prefixWord ++ tailWord_5269706).sum := by decide
  have hdescent : baseEnd_5269706 < baseStart_5269706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269733 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5269733 : Nat := 118140960795 + 5269733 * 2 ^ 59
def prefixEnd_5269733 : Nat := 4983230072969 + 3 ^ 40 * 5269733 * 2
def baseEnd_5269733 : Nat := 2705905949859735879102445

theorem tailTrace_5269733 : CollatzResearch.WordTrace tailWord_5269733 prefixEnd_5269733 2705905949859735879102445 := by
  unfold tailWord_5269733
  simp only [CollatzResearch.WordTrace]
  refine ⟨192202952617664814588949853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128135301745109876392633235 192202952617664814588949853)
  ·
    refine ⟨72076107231624305470856195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192202952617664814588949853 72076107231624305470856195)
    ·
      refine ⟨108114160847436458206284293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72076107231624305470856195 108114160847436458206284293)
      ·
        refine ⟨20271405158894335913678305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108114160847436458206284293 20271405158894335913678305)
        ·
          refine ⟨15203553869170751935258729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20271405158894335913678305 15203553869170751935258729)
          ·
            refine ⟨11402665401878063951444047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15203553869170751935258729 11402665401878063951444047)
            ·
              refine ⟨17103998102817095927166071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11402665401878063951444047 17103998102817095927166071)
              ·
                refine ⟨25655997154225643890749107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17103998102817095927166071 25655997154225643890749107)
                ·
                  refine ⟨38483995731338465836123661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25655997154225643890749107 38483995731338465836123661)
                  ·
                    refine ⟨14431498399251924688546373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38483995731338465836123661 14431498399251924688546373)
                    ·
                      refine ⟨2705905949859735879102445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14431498399251924688546373 2705905949859735879102445)
                      ·
                        rfl

theorem cell23_5269733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5269733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269733 prefixEnd_5269733 := by exact prefixLift 5269733
  have htrace : WordTrace (prefixWord ++ tailWord_5269733) baseStart_5269733 baseEnd_5269733 := by
    simpa [prefixWord, tailWord_5269733, baseEnd_5269733] using wordTrace_append hprefix tailTrace_5269733
  have hstable : (prefixWord ++ tailWord_5269733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269733).length < 2 ^ (prefixWord ++ tailWord_5269733).sum := by decide
  have hdescent : baseEnd_5269733 < baseStart_5269733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269750 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_5269750 : Nat := 118140960795 + 5269750 * 2 ^ 59
def prefixEnd_5269750 : Nat := 4983230072969 + 3 ^ 40 * 5269750 * 2
def baseEnd_5269750 : Nat := 2705914679030862312589867

theorem tailTrace_5269750 : CollatzResearch.WordTrace tailWord_5269750 prefixEnd_5269750 2705914679030862312589867 := by
  unfold tailWord_5269750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12012723291162701655769919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128135715105735484328212469 12012723291162701655769919)
  ·
    refine ⟨18019084936744052483654879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12012723291162701655769919 18019084936744052483654879)
    ·
      refine ⟨27028627405116078725482319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18019084936744052483654879 27028627405116078725482319)
      ·
        refine ⟨40542941107674118088223479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27028627405116078725482319 40542941107674118088223479)
        ·
          refine ⟨60814411661511177132335219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40542941107674118088223479 60814411661511177132335219)
          ·
            refine ⟨91221617492266765698502829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60814411661511177132335219 91221617492266765698502829)
            ·
              refine ⟨34208106559600037136938561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91221617492266765698502829 34208106559600037136938561)
              ·
                refine ⟨25656079919700027852703921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34208106559600037136938561 25656079919700027852703921)
                ·
                  refine ⟨19242059939775020889527941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25656079919700027852703921 19242059939775020889527941)
                  ·
                    refine ⟨3607886238707816416786489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19242059939775020889527941 3607886238707816416786489)
                    ·
                      refine ⟨2705914679030862312589867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607886238707816416786489 2705914679030862312589867)
                      ·
                        rfl

theorem cell23_5269750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_5269750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269750 prefixEnd_5269750 := by exact prefixLift 5269750
  have htrace : WordTrace (prefixWord ++ tailWord_5269750) baseStart_5269750 baseEnd_5269750 := by
    simpa [prefixWord, tailWord_5269750, baseEnd_5269750] using wordTrace_append hprefix tailTrace_5269750
  have hstable : (prefixWord ++ tailWord_5269750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269750).length < 2 ^ (prefixWord ++ tailWord_5269750).sum := by decide
  have hdescent : baseEnd_5269750 < baseStart_5269750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269760 : List Nat := [2, 1, 1, 2, 1, 1, 6, 4, 1, 4]
def baseStart_5269760 : Nat := 118140960795 + 5269760 * 2 ^ 59
def prefixEnd_5269760 : Nat := 4983230072969 + 3 ^ 40 * 5269760 * 2
def baseEnd_5269760 : Nat := 901973271279135757821607

theorem tailTrace_5269760 : CollatzResearch.WordTrace tailWord_5269760 prefixEnd_5269760 901973271279135757821607 := by
  unfold tailWord_5269760
  simp only [CollatzResearch.WordTrace]
  refine ⟨96101968694283499100091367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128135958259044665466788489 96101968694283499100091367)
  ·
    refine ⟨144152953041425248650137051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96101968694283499100091367 144152953041425248650137051)
    ·
      refine ⟨216229429562137872975205577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144152953041425248650137051 216229429562137872975205577)
      ·
        refine ⟨162172072171603404731404183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216229429562137872975205577 162172072171603404731404183)
        ·
          refine ⟨243258108257405107097106275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162172072171603404731404183 243258108257405107097106275)
          ·
            refine ⟨364887162386107660645659413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243258108257405107097106275 364887162386107660645659413)
            ·
              refine ⟨17104085736848796592765285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 364887162386107660645659413 17104085736848796592765285)
              ·
                refine ⟨3207016075659149361143491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17104085736848796592765285 3207016075659149361143491)
                ·
                  refine ⟨4810524113488724041715237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207016075659149361143491 4810524113488724041715237)
                  ·
                    refine ⟨901973271279135757821607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810524113488724041715237 901973271279135757821607)
                    ·
                      rfl

theorem cell23_5269760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 4].length) (baseStart_5269760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269760 prefixEnd_5269760 := by exact prefixLift 5269760
  have htrace : WordTrace (prefixWord ++ tailWord_5269760) baseStart_5269760 baseEnd_5269760 := by
    simpa [prefixWord, tailWord_5269760, baseEnd_5269760] using wordTrace_append hprefix tailTrace_5269760
  have hstable : (prefixWord ++ tailWord_5269760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269760).length < 2 ^ (prefixWord ++ tailWord_5269760).sum := by decide
  have hdescent : baseEnd_5269760 < baseStart_5269760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269790 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_5269790 : Nat := 118140960795 + 5269790 * 2 ^ 59
def prefixEnd_5269790 : Nat := 4983230072969 + 3 ^ 40 * 5269790 * 2
def baseEnd_5269790 : Nat := 300659468695226906232187

theorem tailTrace_5269790 : CollatzResearch.WordTrace tailWord_5269790 prefixEnd_5269790 300659468695226906232187 := by
  unfold tailWord_5269790
  simp only [CollatzResearch.WordTrace]
  refine ⟨24025628947307289165471853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128136687718972208882516549 24025628947307289165471853)
  ·
    refine ⟨9009610855240233437051945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24025628947307289165471853 9009610855240233437051945)
    ·
      refine ⟨6757208141430175077788959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9009610855240233437051945 6757208141430175077788959)
      ·
        refine ⟨10135812212145262616683439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6757208141430175077788959 10135812212145262616683439)
        ·
          refine ⟨15203718318217893925025159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10135812212145262616683439 15203718318217893925025159)
          ·
            refine ⟨22805577477326840887537739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15203718318217893925025159 22805577477326840887537739)
            ·
              refine ⟨34208366215990261331306609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22805577477326840887537739 34208366215990261331306609)
              ·
                refine ⟨25656274661992695998479957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34208366215990261331306609 25656274661992695998479957)
                ·
                  refine ⟨300659468695226906232187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25656274661992695998479957 300659468695226906232187)
                  ·
                    rfl

theorem cell23_5269790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_5269790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269790 prefixEnd_5269790 := by exact prefixLift 5269790
  have htrace : WordTrace (prefixWord ++ tailWord_5269790) baseStart_5269790 baseEnd_5269790 := by
    simpa [prefixWord, tailWord_5269790, baseEnd_5269790] using wordTrace_append hprefix tailTrace_5269790
  have hstable : (prefixWord ++ tailWord_5269790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269790).length < 2 ^ (prefixWord ++ tailWord_5269790).sum := by decide
  have hdescent : baseEnd_5269790 < baseStart_5269790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269794 : List Nat := [3, 3, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_5269794 : Nat := 118140960795 + 5269794 * 2 ^ 59
def prefixEnd_5269794 : Nat := 4983230072969 + 3 ^ 40 * 5269794 * 2
def baseEnd_5269794 : Nat := 901979090726553380146555

theorem tailTrace_5269794 : CollatzResearch.WordTrace tailWord_5269794 prefixEnd_5269794 901979090726553380146555 := by
  unfold tailWord_5269794
  simp only [CollatzResearch.WordTrace]
  refine ⟨48051294367610955501730109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128136784980295881337946957 48051294367610955501730109)
  ·
    refine ⟨18019235387854108313148791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48051294367610955501730109 18019235387854108313148791)
    ·
      refine ⟨27028853081781162469723187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18019235387854108313148791 27028853081781162469723187)
      ·
        refine ⟨40543279622671743704584781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27028853081781162469723187 40543279622671743704584781)
        ·
          refine ⟨15203729858501903889219293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40543279622671743704584781 15203729858501903889219293)
          ·
            refine ⟨5701398696938213958457235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15203729858501903889219293 5701398696938213958457235)
            ·
              refine ⟨8552098045407320937685853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701398696938213958457235 8552098045407320937685853)
              ·
                refine ⟨3207036767027745351632195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8552098045407320937685853 3207036767027745351632195)
                ·
                  refine ⟨4810555150541618027448293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207036767027745351632195 4810555150541618027448293)
                  ·
                    refine ⟨901979090726553380146555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810555150541618027448293 901979090726553380146555)
                    ·
                      rfl

theorem cell23_5269794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_5269794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269794 prefixEnd_5269794 := by exact prefixLift 5269794
  have htrace : WordTrace (prefixWord ++ tailWord_5269794) baseStart_5269794 baseEnd_5269794 := by
    simpa [prefixWord, tailWord_5269794, baseEnd_5269794] using wordTrace_append hprefix tailTrace_5269794
  have hstable : (prefixWord ++ tailWord_5269794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269794).length < 2 ^ (prefixWord ++ tailWord_5269794).sum := by decide
  have hdescent : baseEnd_5269794 < baseStart_5269794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269817 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5269817 : Nat := 118140960795 + 5269817 * 2 ^ 59
def prefixEnd_5269817 : Nat := 4983230072969 + 3 ^ 40 * 5269817 * 2
def baseEnd_5269817 : Nat := 2705949082234713550452059

theorem tailTrace_5269817 : CollatzResearch.WordTrace tailWord_5269817 prefixEnd_5269817 2705949082234713550452059 := by
  unfold tailWord_5269817
  simp only [CollatzResearch.WordTrace]
  refine ⟨192206016349360496935007705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128137344232906997956671803 192206016349360496935007705)
  ·
    refine ⟨144154512262020372701255779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192206016349360496935007705 144154512262020372701255779)
    ·
      refine ⟨216231768393030559051883669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144154512262020372701255779 216231768393030559051883669)
      ·
        refine ⟨10135864143423307455557047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 216231768393030559051883669 10135864143423307455557047)
        ·
          refine ⟨15203796215134961183335571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10135864143423307455557047 15203796215134961183335571)
          ·
            refine ⟨22805694322702441775003357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15203796215134961183335571 22805694322702441775003357)
            ·
              refine ⟨8552135371013415665626259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22805694322702441775003357 8552135371013415665626259)
              ·
                refine ⟨12828203056520123498439389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8552135371013415665626259 12828203056520123498439389)
                ·
                  refine ⟨4810576146195046311914771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12828203056520123498439389 4810576146195046311914771)
                  ·
                    refine ⟨7215864219292569467872157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810576146195046311914771 7215864219292569467872157)
                    ·
                      refine ⟨2705949082234713550452059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215864219292569467872157 2705949082234713550452059)
                      ·
                        rfl

theorem cell23_5269817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5269817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269817 prefixEnd_5269817 := by exact prefixLift 5269817
  have htrace : WordTrace (prefixWord ++ tailWord_5269817) baseStart_5269817 baseEnd_5269817 := by
    simpa [prefixWord, tailWord_5269817, baseEnd_5269817] using wordTrace_append hprefix tailTrace_5269817
  have hstable : (prefixWord ++ tailWord_5269817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269817).length < 2 ^ (prefixWord ++ tailWord_5269817).sum := by decide
  have hdescent : baseEnd_5269817 < baseStart_5269817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269823 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_5269823 : Nat := 118140960795 + 5269823 * 2 ^ 59
def prefixEnd_5269823 : Nat := 4983230072969 + 3 ^ 40 * 5269823 * 2
def baseEnd_5269823 : Nat := 2705952163118640526977031

theorem tailTrace_5269823 : CollatzResearch.WordTrace tailWord_5269823 prefixEnd_5269823 2705952163118640526977031 := by
  unfold tailWord_5269823
  simp only [CollatzResearch.WordTrace]
  refine ⟨192206235187338759959726123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128137490124892506639817415 192206235187338759959726123)
  ·
    refine ⟨288309352781008139939589185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192206235187338759959726123 288309352781008139939589185)
    ·
      refine ⟨216232014585756104954691889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288309352781008139939589185 216232014585756104954691889)
      ·
        refine ⟨162174010939317078716018917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216232014585756104954691889 162174010939317078716018917)
        ·
          refine ⟨30407627051121952259253547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162174010939317078716018917 30407627051121952259253547)
          ·
            refine ⟨45611440576682928388880321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30407627051121952259253547 45611440576682928388880321)
            ·
              refine ⟨34208580432512196291660241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45611440576682928388880321 34208580432512196291660241)
              ·
                refine ⟨25656435324384147218745181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34208580432512196291660241 25656435324384147218745181)
                ·
                  refine ⟨9621163246644055207029443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25656435324384147218745181 9621163246644055207029443)
                  ·
                    refine ⟨14431744869966082810544165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9621163246644055207029443 14431744869966082810544165)
                    ·
                      refine ⟨2705952163118640526977031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14431744869966082810544165 2705952163118640526977031)
                      ·
                        rfl

theorem cell23_5269823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_5269823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269823 prefixEnd_5269823 := by exact prefixLift 5269823
  have htrace : WordTrace (prefixWord ++ tailWord_5269823) baseStart_5269823 baseEnd_5269823 := by
    simpa [prefixWord, tailWord_5269823, baseEnd_5269823] using wordTrace_append hprefix tailTrace_5269823
  have hstable : (prefixWord ++ tailWord_5269823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269823).length < 2 ^ (prefixWord ++ tailWord_5269823).sum := by decide
  have hdescent : baseEnd_5269823 < baseStart_5269823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269840 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 4]
def baseStart_5269840 : Nat := 118140960795 + 5269840 * 2 ^ 59
def prefixEnd_5269840 : Nat := 4983230072969 + 3 ^ 40 * 5269840 * 2
def baseEnd_5269840 : Nat := 2705960892289766960464453

theorem tailTrace_5269840 : CollatzResearch.WordTrace tailWord_5269840 prefixEnd_5269840 2705960892289766960464453 := by
  unfold tailWord_5269840
  simp only [CollatzResearch.WordTrace]
  refine ⟨96103427614138585931547487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128137903485518114575396649 96103427614138585931547487)
  ·
    refine ⟨144155141421207878897321231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96103427614138585931547487 144155141421207878897321231)
    ·
      refine ⟨216232712131811818345981847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144155141421207878897321231 216232712131811818345981847)
      ·
        refine ⟨324349068197717727518972771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216232712131811818345981847 324349068197717727518972771)
        ·
          refine ⟨486523602296576591278459157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324349068197717727518972771 486523602296576591278459157)
          ·
            refine ⟨22805793857652027716177773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 486523602296576591278459157 22805793857652027716177773)
            ·
              refine ⟨8552172696619510393566665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22805793857652027716177773 8552172696619510393566665)
              ·
                refine ⟨6414129522464632795174999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8552172696619510393566665 6414129522464632795174999)
                ·
                  refine ⟨9621194283696949192762499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414129522464632795174999 9621194283696949192762499)
                  ·
                    refine ⟨14431791425545423789143749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9621194283696949192762499 14431791425545423789143749)
                    ·
                      refine ⟨2705960892289766960464453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14431791425545423789143749 2705960892289766960464453)
                      ·
                        rfl

theorem cell23_5269840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 4].length) (baseStart_5269840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269840 prefixEnd_5269840 := by exact prefixLift 5269840
  have htrace : WordTrace (prefixWord ++ tailWord_5269840) baseStart_5269840 baseEnd_5269840 := by
    simpa [prefixWord, tailWord_5269840, baseEnd_5269840] using wordTrace_append hprefix tailTrace_5269840
  have hstable : (prefixWord ++ tailWord_5269840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269840).length < 2 ^ (prefixWord ++ tailWord_5269840).sum := by decide
  have hdescent : baseEnd_5269840 < baseStart_5269840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269868 : List Nat := [2, 2, 1, 1, 7, 1, 2, 2, 1, 1, 3]
def baseStart_5269868 : Nat := 118140960795 + 5269868 * 2 ^ 59
def prefixEnd_5269868 : Nat := 4983230072969 + 3 ^ 40 * 5269868 * 2
def baseEnd_5269868 : Nat := 2705975269748092850914325

theorem tailTrace_5269868 : CollatzResearch.WordTrace tailWord_5269868 prefixEnd_5269868 2705975269748092850914325 := by
  unfold tailWord_5269868
  simp only [CollatzResearch.WordTrace]
  refine ⟨96103938236087866322557129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128138584314783821763409505 96103938236087866322557129)
  ·
    refine ⟨72077953677065899741917847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96103938236087866322557129 72077953677065899741917847)
    ·
      refine ⟨108116930515598849612876771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72077953677065899741917847 108116930515598849612876771)
      ·
        refine ⟨162175395773398274419315157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108116930515598849612876771 162175395773398274419315157)
        ·
          refine ⟨3800985838439022056702699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 162175395773398274419315157 3800985838439022056702699)
          ·
            refine ⟨5701478757658533085054049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800985838439022056702699 5701478757658533085054049)
            ·
              refine ⟨4276109068243899813790537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701478757658533085054049 4276109068243899813790537)
              ·
                refine ⟨3207081801182924860342903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4276109068243899813790537 3207081801182924860342903)
                ·
                  refine ⟨4810622701774387290514355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207081801182924860342903 4810622701774387290514355)
                  ·
                    refine ⟨7215934052661580935771533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810622701774387290514355 7215934052661580935771533)
                    ·
                      refine ⟨2705975269748092850914325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215934052661580935771533 2705975269748092850914325)
                      ·
                        rfl

theorem cell23_5269868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_5269868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269868 prefixEnd_5269868 := by exact prefixLift 5269868
  have htrace : WordTrace (prefixWord ++ tailWord_5269868) baseStart_5269868 baseEnd_5269868 := by
    simpa [prefixWord, tailWord_5269868, baseEnd_5269868] using wordTrace_append hprefix tailTrace_5269868
  have hstable : (prefixWord ++ tailWord_5269868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269868).length < 2 ^ (prefixWord ++ tailWord_5269868).sum := by decide
  have hdescent : baseEnd_5269868 < baseStart_5269868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269873 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_5269873 : Nat := 118140960795 + 5269873 * 2 ^ 59
def prefixEnd_5269873 : Nat := 4983230072969 + 3 ^ 40 * 5269873 * 2
def baseEnd_5269873 : Nat := 2705977837151365331351801

theorem tailTrace_5269873 : CollatzResearch.WordTrace tailWord_5269873 prefixEnd_5269873 2705977837151365331351801 := by
  unfold tailWord_5269873
  simp only [CollatzResearch.WordTrace]
  refine ⟨192208058837157618499046273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128138705891438412332697515 192208058837157618499046273)
  ·
    refine ⟨144156044127868213874284705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192208058837157618499046273 144156044127868213874284705)
    ·
      refine ⟨108117033095901160405713529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144156044127868213874284705 108117033095901160405713529)
      ·
        refine ⟨81087774821925870304285147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108117033095901160405713529 81087774821925870304285147)
        ·
          refine ⟨121631662232888805456427721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81087774821925870304285147 121631662232888805456427721)
          ·
            refine ⟨91223746674666604092320791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121631662232888805456427721 91223746674666604092320791)
            ·
              refine ⟨136835620011999906138481187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91223746674666604092320791 136835620011999906138481187)
              ·
                refine ⟨205253430017999859207721781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136835620011999906138481187 205253430017999859207721781)
                ·
                  refine ⟨19242509064187486800723917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205253430017999859207721781 19242509064187486800723917)
                  ·
                    refine ⟨7215940899070307550271469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19242509064187486800723917 7215940899070307550271469)
                    ·
                      refine ⟨2705977837151365331351801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7215940899070307550271469 2705977837151365331351801)
                      ·
                        rfl

theorem cell23_5269873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_5269873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269873 prefixEnd_5269873 := by exact prefixLift 5269873
  have htrace : WordTrace (prefixWord ++ tailWord_5269873) baseStart_5269873 baseEnd_5269873 := by
    simpa [prefixWord, tailWord_5269873, baseEnd_5269873] using wordTrace_append hprefix tailTrace_5269873
  have hstable : (prefixWord ++ tailWord_5269873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269873).length < 2 ^ (prefixWord ++ tailWord_5269873).sum := by decide
  have hdescent : baseEnd_5269873 < baseStart_5269873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269908 : List Nat := [2, 4, 2, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_5269908 : Nat := 118140960795 + 5269908 * 2 ^ 59
def prefixEnd_5269908 : Nat := 4983230072969 + 3 ^ 40 * 5269908 * 2
def baseEnd_5269908 : Nat := 2705995808974272694414141

theorem tailTrace_5269908 : CollatzResearch.WordTrace tailWord_5269908 prefixEnd_5269908 2705995808974272694414141 := by
  unfold tailWord_5269908
  simp only [CollatzResearch.WordTrace]
  refine ⟨96104667696015409738285189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128139556928020546317713585 96104667696015409738285189)
  ·
    refine ⟨18019625193002889325928473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96104667696015409738285189 18019625193002889325928473)
    ·
      refine ⟨13514718894752166994446355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18019625193002889325928473 13514718894752166994446355)
      ·
        refine ⟨20272078342128250491669533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13514718894752166994446355 20272078342128250491669533)
        ·
          refine ⟨7602029378298093934376075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20272078342128250491669533 7602029378298093934376075)
          ·
            refine ⟨11403044067447140901564113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7602029378298093934376075 11403044067447140901564113)
            ·
              refine ⟨8552283050585355676173085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11403044067447140901564113 8552283050585355676173085)
              ·
                refine ⟨3207106143969508378564907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8552283050585355676173085 3207106143969508378564907)
                ·
                  refine ⟨4810659215954262567847361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207106143969508378564907 4810659215954262567847361)
                  ·
                    refine ⟨3607994411965696925885521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810659215954262567847361 3607994411965696925885521)
                    ·
                      refine ⟨2705995808974272694414141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3607994411965696925885521 2705995808974272694414141)
                      ·
                        rfl

theorem cell23_5269908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_5269908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269908 prefixEnd_5269908 := by exact prefixLift 5269908
  have htrace : WordTrace (prefixWord ++ tailWord_5269908) baseStart_5269908 baseEnd_5269908 := by
    simpa [prefixWord, tailWord_5269908, baseEnd_5269908] using wordTrace_append hprefix tailTrace_5269908
  have hstable : (prefixWord ++ tailWord_5269908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269908).length < 2 ^ (prefixWord ++ tailWord_5269908).sum := by decide
  have hdescent : baseEnd_5269908 < baseStart_5269908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269923 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 2, 6]
def baseStart_5269923 : Nat := 118140960795 + 5269923 * 2 ^ 59
def prefixEnd_5269923 : Nat := 4983230072969 + 3 ^ 40 * 5269923 * 2
def baseEnd_5269923 : Nat := 902001170394696711908857

theorem tailTrace_5269923 : CollatzResearch.WordTrace tailWord_5269923 prefixEnd_5269923 902001170394696711908857 := by
  unfold tailWord_5269923
  simp only [CollatzResearch.WordTrace]
  refine ⟨192209882486976477038366423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128139921657984318025577615 192209882486976477038366423)
  ·
    refine ⟨288314823730464715557549635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192209882486976477038366423 288314823730464715557549635)
    ·
      refine ⟨432472235595697073336324453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288314823730464715557549635 432472235595697073336324453)
      ·
        refine ⟨81088544174193201250560835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 432472235595697073336324453 81088544174193201250560835)
        ·
          refine ⟨121632816261289801875841253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81088544174193201250560835 121632816261289801875841253)
          ·
            refine ⟨22806153048991837851720235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121632816261289801875841253 22806153048991837851720235)
            ·
              refine ⟨34209229573487756777580353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22806153048991837851720235 34209229573487756777580353)
              ·
                refine ⟨25656922180115817583185265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34209229573487756777580353 25656922180115817583185265)
                ·
                  refine ⟨19242691635086863187388949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25656922180115817583185265 19242691635086863187388949)
                  ·
                    refine ⟨902001170394696711908857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19242691635086863187388949 902001170394696711908857)
                    ·
                      rfl

theorem cell23_5269923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 6].length) (baseStart_5269923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269923 prefixEnd_5269923 := by exact prefixLift 5269923
  have htrace : WordTrace (prefixWord ++ tailWord_5269923) baseStart_5269923 baseEnd_5269923 := by
    simpa [prefixWord, tailWord_5269923, baseEnd_5269923] using wordTrace_append hprefix tailTrace_5269923
  have hstable : (prefixWord ++ tailWord_5269923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269923).length < 2 ^ (prefixWord ++ tailWord_5269923).sum := by decide
  have hdescent : baseEnd_5269923 < baseStart_5269923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269941 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_5269941 : Nat := 118140960795 + 5269941 * 2 ^ 59
def prefixEnd_5269941 : Nat := 4983230072969 + 3 ^ 40 * 5269941 * 2
def baseEnd_5269941 : Nat := 2706012753835871065301489

theorem tailTrace_5269941 : CollatzResearch.WordTrace tailWord_5269941 prefixEnd_5269941 2706012753835871065301489 := by
  unfold tailWord_5269941
  simp only [CollatzResearch.WordTrace]
  refine ⟨192210539000911266112521677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128140359333940844075014451 192210539000911266112521677)
  ·
    refine ⟨72078952125341724792195629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192210539000911266112521677 72078952125341724792195629)
    ·
      refine ⟨27029607047003146797073361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72078952125341724792195629 27029607047003146797073361)
      ·
        refine ⟨20272205285252360097805021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27029607047003146797073361 20272205285252360097805021)
        ·
          refine ⟨7602076981969635036676883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20272205285252360097805021 7602076981969635036676883)
          ·
            refine ⟨11403115472954452555015325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7602076981969635036676883 11403115472954452555015325)
            ·
              refine ⟨4276168302357919708130747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11403115472954452555015325 4276168302357919708130747)
              ·
                refine ⟨6414252453536879562196121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276168302357919708130747 6414252453536879562196121)
                ·
                  refine ⟨4810689340152659671647091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414252453536879562196121 4810689340152659671647091)
                  ·
                    refine ⟨7216034010228989507470637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810689340152659671647091 7216034010228989507470637)
                    ·
                      refine ⟨2706012753835871065301489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7216034010228989507470637 2706012753835871065301489)
                      ·
                        rfl

theorem cell23_5269941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_5269941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269941 prefixEnd_5269941 := by exact prefixLift 5269941
  have htrace : WordTrace (prefixWord ++ tailWord_5269941) baseStart_5269941 baseEnd_5269941 := by
    simpa [prefixWord, tailWord_5269941, baseEnd_5269941] using wordTrace_append hprefix tailTrace_5269941
  have hstable : (prefixWord ++ tailWord_5269941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269941).length < 2 ^ (prefixWord ++ tailWord_5269941).sum := by decide
  have hdescent : baseEnd_5269941 < baseStart_5269941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269950 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_5269950 : Nat := 118140960795 + 5269950 * 2 ^ 59
def prefixEnd_5269950 : Nat := 4983230072969 + 3 ^ 40 * 5269950 * 2
def baseEnd_5269950 : Nat := 2706017375161761530088947

theorem tailTrace_5269950 : CollatzResearch.WordTrace tailWord_5269950 prefixEnd_5269950 2706017375161761530088947 := by
  unfold tailWord_5269950
  simp only [CollatzResearch.WordTrace]
  refine ⟨24026358407234832581199913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128140578171919107099732869 24026358407234832581199913)
  ·
    refine ⟨18019768805426124435899935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24026358407234832581199913 18019768805426124435899935)
    ·
      refine ⟨27029653208139186653849903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18019768805426124435899935 27029653208139186653849903)
      ·
        refine ⟨40544479812208779980774855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27029653208139186653849903 40544479812208779980774855)
        ·
          refine ⟨60816719718313169971162283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40544479812208779980774855 60816719718313169971162283)
          ·
            refine ⟨91225079577469754956743425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60816719718313169971162283 91225079577469754956743425)
            ·
              refine ⟨68418809683102316217557569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91225079577469754956743425 68418809683102316217557569)
              ·
                refine ⟨51314107262326737163168177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68418809683102316217557569 51314107262326737163168177)
                ·
                  refine ⟨38485580446745052872376133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51314107262326737163168177 38485580446745052872376133)
                  ·
                    refine ⟨7216046333764697413570525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38485580446745052872376133 7216046333764697413570525)
                    ·
                      refine ⟨2706017375161761530088947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7216046333764697413570525 2706017375161761530088947)
                      ·
                        rfl

theorem cell23_5269950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_5269950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269950 prefixEnd_5269950 := by exact prefixLift 5269950
  have htrace : WordTrace (prefixWord ++ tailWord_5269950) baseStart_5269950 baseEnd_5269950 := by
    simpa [prefixWord, tailWord_5269950, baseEnd_5269950] using wordTrace_append hprefix tailTrace_5269950
  have hstable : (prefixWord ++ tailWord_5269950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269950).length < 2 ^ (prefixWord ++ tailWord_5269950).sum := by decide
  have hdescent : baseEnd_5269950 < baseStart_5269950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269987 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 7]
def baseStart_5269987 : Nat := 118140960795 + 5269987 * 2 ^ 59
def prefixEnd_5269987 : Nat := 4983230072969 + 3 ^ 40 * 5269987 * 2
def baseEnd_5269987 : Nat := 300670708216219765036253

theorem tailTrace_5269987 : CollatzResearch.WordTrace tailWord_5269987 prefixEnd_5269987 300670708216219765036253 := by
  unfold tailWord_5269987
  simp only [CollatzResearch.WordTrace]
  refine ⟨192212216758744615968696215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128141477839163077312464143 192212216758744615968696215)
  ·
    refine ⟨288318325138116923953044323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192212216758744615968696215 288318325138116923953044323)
    ·
      refine ⟨432477487707175385929566485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288318325138116923953044323 432477487707175385929566485)
      ·
        refine ⟨20272382236273846215448429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 432477487707175385929566485 20272382236273846215448429)
        ·
          refine ⟨7602143338602692330793161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20272382236273846215448429 7602143338602692330793161)
          ·
            refine ⟨5701607503952019248094871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7602143338602692330793161 5701607503952019248094871)
            ·
              refine ⟨8552411255928028872142307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701607503952019248094871 8552411255928028872142307)
              ·
                refine ⟨12828616883892043308213461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8552411255928028872142307 12828616883892043308213461)
                ·
                  refine ⟨300670708216219765036253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12828616883892043308213461 300670708216219765036253)
                  ·
                    rfl

theorem cell23_5269987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 7].length) (baseStart_5269987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269987 prefixEnd_5269987 := by exact prefixLift 5269987
  have htrace : WordTrace (prefixWord ++ tailWord_5269987) baseStart_5269987 baseEnd_5269987 := by
    simpa [prefixWord, tailWord_5269987, baseEnd_5269987] using wordTrace_append hprefix tailTrace_5269987
  have hstable : (prefixWord ++ tailWord_5269987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269987).length < 2 ^ (prefixWord ++ tailWord_5269987).sum := by decide
  have hdescent : baseEnd_5269987 < baseStart_5269987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5269998 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_5269998 : Nat := 118140960795 + 5269998 * 2 ^ 59
def prefixEnd_5269998 : Nat := 4983230072969 + 3 ^ 40 * 5269998 * 2
def baseEnd_5269998 : Nat := 2706042022233177342288727

theorem tailTrace_5269998 : CollatzResearch.WordTrace tailWord_5269998 prefixEnd_5269998 2706042022233177342288727 := by
  unfold tailWord_5269998
  simp only [CollatzResearch.WordTrace]
  refine ⟨24026577245213095605918331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128141745307803176564897765 24026577245213095605918331)
  ·
    refine ⟨36039865867819643408877497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24026577245213095605918331 36039865867819643408877497)
    ·
      refine ⟨27029899400864732556658123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36039865867819643408877497 27029899400864732556658123)
      ·
        refine ⟨40544849101297098834987185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27029899400864732556658123 40544849101297098834987185)
        ·
          refine ⟨30408636825972824126240389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40544849101297098834987185 30408636825972824126240389)
          ·
            refine ⟨5701619404869904523670073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30408636825972824126240389 5701619404869904523670073)
            ·
              refine ⟨4276214553652428392752555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701619404869904523670073 4276214553652428392752555)
              ·
                refine ⟨6414321830478642589128833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276214553652428392752555 6414321830478642589128833)
                ·
                  refine ⟨4810741372858981941846625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414321830478642589128833 4810741372858981941846625)
                  ·
                    refine ⟨3608056029644236456384969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810741372858981941846625 3608056029644236456384969)
                    ·
                      refine ⟨2706042022233177342288727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608056029644236456384969 2706042022233177342288727)
                      ·
                        rfl

theorem cell23_5269998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_5269998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5269998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5269998 prefixEnd_5269998 := by exact prefixLift 5269998
  have htrace : WordTrace (prefixWord ++ tailWord_5269998) baseStart_5269998 baseEnd_5269998 := by
    simpa [prefixWord, tailWord_5269998, baseEnd_5269998] using wordTrace_append hprefix tailTrace_5269998
  have hstable : (prefixWord ++ tailWord_5269998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5269998).length < 2 ^ (prefixWord ++ tailWord_5269998).sum := by decide
  have hdescent : baseEnd_5269998 < baseStart_5269998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5269998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270017 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 2, 5]
def baseStart_5270017 : Nat := 118140960795 + 5270017 * 2 ^ 59
def prefixEnd_5270017 : Nat := 4983230072969 + 3 ^ 40 * 5270017 * 2
def baseEnd_5270017 : Nat := 902017259455204255983713

theorem tailTrace_5270017 : CollatzResearch.WordTrace tailWord_5270017 prefixEnd_5270017 902017259455204255983713 := by
  unfold tailWord_5270017
  simp only [CollatzResearch.WordTrace]
  refine ⟨192213310948635931092288305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128142207299090620728192203 192213310948635931092288305)
  ·
    refine ⟨144159983211476948319216229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192213310948635931092288305 144159983211476948319216229)
    ·
      refine ⟨27029996852151927809853043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144159983211476948319216229 27029996852151927809853043)
      ·
        refine ⟨40544995278227891714779565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27029996852151927809853043 40544995278227891714779565)
        ·
          refine ⟨15204373229335459393042337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40544995278227891714779565 15204373229335459393042337)
          ·
            refine ⟨11403279922001594544781753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15204373229335459393042337 11403279922001594544781753)
            ·
              refine ⟨8552459941501195908586315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11403279922001594544781753 8552459941501195908586315)
              ·
                refine ⟨12828689912251793862879473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8552459941501195908586315 12828689912251793862879473)
                ·
                  refine ⟨9621517434188845397159605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12828689912251793862879473 9621517434188845397159605)
                  ·
                    refine ⟨902017259455204255983713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9621517434188845397159605 902017259455204255983713)
                    ·
                      rfl

theorem cell23_5270017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_5270017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270017 prefixEnd_5270017 := by exact prefixLift 5270017
  have htrace : WordTrace (prefixWord ++ tailWord_5270017) baseStart_5270017 baseEnd_5270017 := by
    simpa [prefixWord, tailWord_5270017, baseEnd_5270017] using wordTrace_append hprefix tailTrace_5270017
  have hstable : (prefixWord ++ tailWord_5270017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270017).length < 2 ^ (prefixWord ++ tailWord_5270017).sum := by decide
  have hdescent : baseEnd_5270017 < baseStart_5270017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270037 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_5270037 : Nat := 118140960795 + 5270037 * 2 ^ 59
def prefixEnd_5270037 : Nat := 4983230072969 + 3 ^ 40 * 5270037 * 2
def baseEnd_5270037 : Nat := 2706062047978702689701047

theorem tailTrace_5270037 : CollatzResearch.WordTrace tailWord_5270037 prefixEnd_5270037 2706062047978702689701047 := by
  unfold tailWord_5270037
  simp only [CollatzResearch.WordTrace]
  refine ⟨192214040408563474508016365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128142693605708983005344243 192214040408563474508016365)
  ·
    refine ⟨72080265153211302940506137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192214040408563474508016365 72080265153211302940506137)
    ·
      refine ⟨54060198864908477205379603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72080265153211302940506137 54060198864908477205379603)
      ·
        refine ⟨81090298297362715808069405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54060198864908477205379603 81090298297362715808069405)
        ·
          refine ⟨30408861861511018428026027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81090298297362715808069405 30408861861511018428026027)
          ·
            refine ⟨45613292792266527642039041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30408861861511018428026027 45613292792266527642039041)
            ·
              refine ⟨34209969594199895731529281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45613292792266527642039041 34209969594199895731529281)
              ·
                refine ⟨25657477195649921798646961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34209969594199895731529281 25657477195649921798646961)
                ·
                  refine ⟨19243107896737441348985221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25657477195649921798646961 19243107896737441348985221)
                  ·
                    refine ⟨3608082730638270252934729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19243107896737441348985221 3608082730638270252934729)
                    ·
                      refine ⟨2706062047978702689701047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608082730638270252934729 2706062047978702689701047)
                      ·
                        rfl

theorem cell23_5270037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_5270037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270037 prefixEnd_5270037 := by exact prefixLift 5270037
  have htrace : WordTrace (prefixWord ++ tailWord_5270037) baseStart_5270037 baseEnd_5270037 := by
    simpa [prefixWord, tailWord_5270037, baseEnd_5270037] using wordTrace_append hprefix tailTrace_5270037
  have hstable : (prefixWord ++ tailWord_5270037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270037).length < 2 ^ (prefixWord ++ tailWord_5270037).sum := by decide
  have hdescent : baseEnd_5270037 < baseStart_5270037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270050 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_5270050 : Nat := 118140960795 + 5270050 * 2 ^ 59
def prefixEnd_5270050 : Nat := 4983230072969 + 3 ^ 40 * 5270050 * 2
def baseEnd_5270050 : Nat := 2706068723227211138838487

theorem tailTrace_5270050 : CollatzResearch.WordTrace tailWord_5270050 prefixEnd_5270050 2706068723227211138838487 := by
  unfold tailWord_5270050
  simp only [CollatzResearch.WordTrace]
  refine ⟨48053628639379094432059901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128143009705010918485493069 48053628639379094432059901)
  ·
    refine ⟨18020110739767160412022463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48053628639379094432059901 18020110739767160412022463)
    ·
      refine ⟨27030166109650740618033695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18020110739767160412022463 27030166109650740618033695)
      ·
        refine ⟨40545249164476110927050543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27030166109650740618033695 40545249164476110927050543)
        ·
          refine ⟨60817873746714166390575815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40545249164476110927050543 60817873746714166390575815)
          ·
            refine ⟨91226810620071249585863723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60817873746714166390575815 91226810620071249585863723)
            ·
              refine ⟨136840215930106874378795585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91226810620071249585863723 136840215930106874378795585)
              ·
                refine ⟨102630161947580155784096689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136840215930106874378795585 102630161947580155784096689)
                ·
                  refine ⟨76972621460685116838072517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102630161947580155784096689 76972621460685116838072517)
                  ·
                    refine ⟨14432366523878459407138597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76972621460685116838072517 14432366523878459407138597)
                    ·
                      refine ⟨2706068723227211138838487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14432366523878459407138597 2706068723227211138838487)
                      ·
                        rfl

theorem cell23_5270050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_5270050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270050 prefixEnd_5270050 := by exact prefixLift 5270050
  have htrace : WordTrace (prefixWord ++ tailWord_5270050) baseStart_5270050 baseEnd_5270050 := by
    simpa [prefixWord, tailWord_5270050, baseEnd_5270050] using wordTrace_append hprefix tailTrace_5270050
  have hstable : (prefixWord ++ tailWord_5270050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270050).length < 2 ^ (prefixWord ++ tailWord_5270050).sum := by decide
  have hdescent : baseEnd_5270050 < baseStart_5270050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270068 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_5270068 : Nat := 118140960795 + 5270068 * 2 ^ 59
def prefixEnd_5270068 : Nat := 4983230072969 + 3 ^ 40 * 5270068 * 2
def baseEnd_5270068 : Nat := 902025988626330689471135

theorem tailTrace_5270068 : CollatzResearch.WordTrace tailWord_5270068 prefixEnd_5270068 902025988626330689471135 := by
  unfold tailWord_5270068
  simp only [CollatzResearch.WordTrace]
  refine ⟨96107585535725583401197429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128143447380967444534929905 96107585535725583401197429)
  ·
    refine ⟨9010086143974273443862259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96107585535725583401197429 9010086143974273443862259)
    ·
      refine ⟨13515129215961410165793389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9010086143974273443862259 13515129215961410165793389)
      ·
        refine ⟨5068173455985528812172521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13515129215961410165793389 5068173455985528812172521)
        ·
          refine ⟨3801130091989146609129391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5068173455985528812172521 3801130091989146609129391)
          ·
            refine ⟨5701695137983719913694087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801130091989146609129391 5701695137983719913694087)
            ·
              refine ⟨8552542706975579870541131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701695137983719913694087 8552542706975579870541131)
              ·
                refine ⟨12828814060463369805811697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8552542706975579870541131 12828814060463369805811697)
                ·
                  refine ⟨9621610545347527354358773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12828814060463369805811697 9621610545347527354358773)
                  ·
                    refine ⟨902025988626330689471135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9621610545347527354358773 902025988626330689471135)
                    ·
                      rfl

theorem cell23_5270068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_5270068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270068 prefixEnd_5270068 := by exact prefixLift 5270068
  have htrace : WordTrace (prefixWord ++ tailWord_5270068) baseStart_5270068 baseEnd_5270068 := by
    simpa [prefixWord, tailWord_5270068, baseEnd_5270068] using wordTrace_append hprefix tailTrace_5270068
  have hstable : (prefixWord ++ tailWord_5270068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270068).length < 2 ^ (prefixWord ++ tailWord_5270068).sum := by decide
  have hdescent : baseEnd_5270068 < baseStart_5270068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270074 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_5270074 : Nat := 118140960795 + 5270074 * 2 ^ 59
def prefixEnd_5270074 : Nat := 4983230072969 + 3 ^ 40 * 5270074 * 2
def baseEnd_5270074 : Nat := 2706081046762919044938377

theorem tailTrace_5270074 : CollatzResearch.WordTrace tailWord_5270074 prefixEnd_5270074 2706081046762919044938377 := by
  unfold tailWord_5270074
  simp only [CollatzResearch.WordTrace]
  refine ⟨48053847477357357456778319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128143593272952953218075517 48053847477357357456778319)
  ·
    refine ⟨72080771216036036185167479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48053847477357357456778319 72080771216036036185167479)
    ·
      refine ⟨108121156824054054277751219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72080771216036036185167479 108121156824054054277751219)
      ·
        refine ⟨162181735236081081416626829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108121156824054054277751219 162181735236081081416626829)
        ·
          refine ⟨60818150713530405531235061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162181735236081081416626829 60818150713530405531235061)
          ·
            refine ⟨5701701629393475518553287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60818150713530405531235061 5701701629393475518553287)
            ·
              refine ⟨8552552444090213277829931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701701629393475518553287 8552552444090213277829931)
              ·
                refine ⟨12828828666135319916744897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8552552444090213277829931 12828828666135319916744897)
                ·
                  refine ⟨9621621499601489937558673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12828828666135319916744897 9621621499601489937558673)
                  ·
                    refine ⟨7216216124701117453169005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9621621499601489937558673 7216216124701117453169005)
                    ·
                      refine ⟨2706081046762919044938377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7216216124701117453169005 2706081046762919044938377)
                      ·
                        rfl

theorem cell23_5270074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_5270074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270074 prefixEnd_5270074 := by exact prefixLift 5270074
  have htrace : WordTrace (prefixWord ++ tailWord_5270074) baseStart_5270074 baseEnd_5270074 := by
    simpa [prefixWord, tailWord_5270074, baseEnd_5270074] using wordTrace_append hprefix tailTrace_5270074
  have hstable : (prefixWord ++ tailWord_5270074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270074).length < 2 ^ (prefixWord ++ tailWord_5270074).sum := by decide
  have hdescent : baseEnd_5270074 < baseStart_5270074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270081 : List Nat := [1, 2, 5, 1, 1, 3, 2, 3, 1, 4]
def baseStart_5270081 : Nat := 118140960795 + 5270081 * 2 ^ 59
def prefixEnd_5270081 : Nat := 4983230072969 + 3 ^ 40 * 5270081 * 2
def baseEnd_5270081 : Nat := 902028213709166839183615

theorem tailTrace_5270081 : CollatzResearch.WordTrace tailWord_5270081 prefixEnd_5270081 902028213709166839183615 := by
  unfold tailWord_5270081
  simp only [CollatzResearch.WordTrace]
  refine ⟨192215645220404070022618097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128143763480269380015078731 192215645220404070022618097)
  ·
    refine ⟨144161733915303052516963573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192215645220404070022618097 144161733915303052516963573)
    ·
      refine ⟨13515162554559661173465335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144161733915303052516963573 13515162554559661173465335)
      ·
        refine ⟨20272743831839491760198003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13515162554559661173465335 20272743831839491760198003)
        ·
          refine ⟨30409115747759237640297005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20272743831839491760198003 30409115747759237640297005)
          ·
            refine ⟨11403418405409714115111377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30409115747759237640297005 11403418405409714115111377)
            ·
              refine ⟨8552563804057285586333533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11403418405409714115111377 8552563804057285586333533)
              ·
                refine ⟨3207211426521482094875075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8552563804057285586333533 3207211426521482094875075)
                ·
                  refine ⟨4810817139782223142312613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207211426521482094875075 4810817139782223142312613)
                  ·
                    refine ⟨902028213709166839183615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810817139782223142312613 902028213709166839183615)
                    ·
                      rfl

theorem cell23_5270081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_5270081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270081 prefixEnd_5270081 := by exact prefixLift 5270081
  have htrace : WordTrace (prefixWord ++ tailWord_5270081) baseStart_5270081 baseEnd_5270081 := by
    simpa [prefixWord, tailWord_5270081, baseEnd_5270081] using wordTrace_append hprefix tailTrace_5270081
  have hstable : (prefixWord ++ tailWord_5270081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270081).length < 2 ^ (prefixWord ++ tailWord_5270081).sum := by decide
  have hdescent : baseEnd_5270081 < baseStart_5270081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270127 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 4]
def baseStart_5270127 : Nat := 118140960795 + 5270127 * 2 ^ 59
def prefixEnd_5270127 : Nat := 4983230072969 + 3 ^ 40 * 5270127 * 2
def baseEnd_5270127 : Nat := 2706108261237607337575633

theorem tailTrace_5270127 : CollatzResearch.WordTrace tailWord_5270127 prefixEnd_5270127 2706108261237607337575633 := by
  unfold tailWord_5270127
  simp only [CollatzResearch.WordTrace]
  refine ⟨192217322978237419878792635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128144881985491613252528423 192217322978237419878792635)
  ·
    refine ⟨288325984467356129818188953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192217322978237419878792635 288325984467356129818188953)
    ·
      refine ⟨216244488350517097363641715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288325984467356129818188953 216244488350517097363641715)
      ·
        refine ⟨324366732525775646045462573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216244488350517097363641715 324366732525775646045462573)
        ·
          refine ⟨121637524697165867267048465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324366732525775646045462573 121637524697165867267048465)
          ·
            refine ⟨91228143522874400450286349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121637524697165867267048465 91228143522874400450286349)
            ·
              refine ⟨34210553821077900168857381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91228143522874400450286349 34210553821077900168857381)
              ·
                refine ⟨6414478841452106281660759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34210553821077900168857381 6414478841452106281660759)
                ·
                  refine ⟨9621718262178159422491139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414478841452106281660759 9621718262178159422491139)
                  ·
                    refine ⟨14432577393267239133736709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9621718262178159422491139 14432577393267239133736709)
                    ·
                      refine ⟨2706108261237607337575633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14432577393267239133736709 2706108261237607337575633)
                      ·
                        rfl

theorem cell23_5270127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 4].length) (baseStart_5270127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270127 prefixEnd_5270127 := by exact prefixLift 5270127
  have htrace : WordTrace (prefixWord ++ tailWord_5270127) baseStart_5270127 baseEnd_5270127 := by
    simpa [prefixWord, tailWord_5270127, baseEnd_5270127] using wordTrace_append hprefix tailTrace_5270127
  have hstable : (prefixWord ++ tailWord_5270127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270127).length < 2 ^ (prefixWord ++ tailWord_5270127).sum := by decide
  have hdescent : baseEnd_5270127 < baseStart_5270127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270137 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 4, 4]
def baseStart_5270137 : Nat := 118140960795 + 5270137 * 2 ^ 59
def prefixEnd_5270137 : Nat := 4983230072969 + 3 ^ 40 * 5270137 * 2
def baseEnd_5270137 : Nat := 902037798681384099483529

theorem tailTrace_5270137 : CollatzResearch.WordTrace tailWord_5270137 prefixEnd_5270137 902037798681384099483529 := by
  unfold tailWord_5270137
  simp only [CollatzResearch.WordTrace]
  refine ⟨192217687708201191586656665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128145125138800794391104443 192217687708201191586656665)
  ·
    refine ⟨144163265781150893689992499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192217687708201191586656665 144163265781150893689992499)
    ·
      refine ⟨216244898671726340534988749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144163265781150893689992499 216244898671726340534988749)
      ·
        refine ⟨81091837001897377700620781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216244898671726340534988749 81091837001897377700620781)
        ·
          refine ⟨30409438875711516637732793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81091837001897377700620781 30409438875711516637732793)
          ·
            refine ⟨22807079156783637478299595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30409438875711516637732793 22807079156783637478299595)
            ·
              refine ⟨34210618735175456217449393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22807079156783637478299595 34210618735175456217449393)
              ·
                refine ⟨25657964051381592163087045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34210618735175456217449393 25657964051381592163087045)
                ·
                  refine ⟨4810868259634048530578821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25657964051381592163087045 4810868259634048530578821)
                  ·
                    refine ⟨902037798681384099483529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810868259634048530578821 902037798681384099483529)
                    ·
                      rfl

theorem cell23_5270137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 4].length) (baseStart_5270137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270137 prefixEnd_5270137 := by exact prefixLift 5270137
  have htrace : WordTrace (prefixWord ++ tailWord_5270137) baseStart_5270137 baseEnd_5270137 := by
    simpa [prefixWord, tailWord_5270137, baseEnd_5270137] using wordTrace_append hprefix tailTrace_5270137
  have hstable : (prefixWord ++ tailWord_5270137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270137).length < 2 ^ (prefixWord ++ tailWord_5270137).sum := by decide
  have hdescent : baseEnd_5270137 < baseStart_5270137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270164 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5270164 : Nat := 118140960795 + 5270164 * 2 ^ 59
def prefixEnd_5270164 : Nat := 4983230072969 + 3 ^ 40 * 5270164 * 2
def baseEnd_5270164 : Nat := 2706127260021823692812963

theorem tailTrace_5270164 : CollatzResearch.WordTrace tailWord_5270164 prefixEnd_5270164 2706127260021823692812963 := by
  unfold tailWord_5270164
  simp only [CollatzResearch.WordTrace]
  refine ⟨96109336239551687598944773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128145781652735583465259697 96109336239551687598944773)
  ·
    refine ⟨18020500544915941424802145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96109336239551687598944773 18020500544915941424802145)
    ·
      refine ⟨13515375408686956068601609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18020500544915941424802145 13515375408686956068601609)
      ·
        refine ⟨10136531556515217051451207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13515375408686956068601609 10136531556515217051451207)
        ·
          refine ⟨15204797334772825577176811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10136531556515217051451207 15204797334772825577176811)
          ·
            refine ⟨22807196002159238365765217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15204797334772825577176811 22807196002159238365765217)
            ·
              refine ⟨17105397001619428774323913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22807196002159238365765217 17105397001619428774323913)
              ·
                refine ⟨12829047751214571580742935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17105397001619428774323913 12829047751214571580742935)
                ·
                  refine ⟨19243571626821857371114403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12829047751214571580742935 19243571626821857371114403)
                  ·
                    refine ⟨28865357440232786056671605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19243571626821857371114403 28865357440232786056671605)
                    ·
                      refine ⟨2706127260021823692812963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28865357440232786056671605 2706127260021823692812963)
                      ·
                        rfl

theorem cell23_5270164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5270164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270164 prefixEnd_5270164 := by exact prefixLift 5270164
  have htrace : WordTrace (prefixWord ++ tailWord_5270164) baseStart_5270164 baseEnd_5270164 := by
    simpa [prefixWord, tailWord_5270164, baseEnd_5270164] using wordTrace_append hprefix tailTrace_5270164
  have hstable : (prefixWord ++ tailWord_5270164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270164).length < 2 ^ (prefixWord ++ tailWord_5270164).sum := by decide
  have hdescent : baseEnd_5270164 < baseStart_5270164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270174 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5270174 : Nat := 118140960795 + 5270174 * 2 ^ 59
def prefixEnd_5270174 : Nat := 4983230072969 + 3 ^ 40 * 5270174 * 2
def baseEnd_5270174 : Nat := 2706132394828368653687917

theorem tailTrace_5270174 : CollatzResearch.WordTrace tailWord_5270174 prefixEnd_5270174 2706132394828368653687917 := by
  unfold tailWord_5270174
  simp only [CollatzResearch.WordTrace]
  refine ⟨24027379651133393363219197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128146024806044764603835717 24027379651133393363219197)
  ·
    refine ⟨9010267369175022511207199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24027379651133393363219197 9010267369175022511207199)
    ·
      refine ⟨13515401053762533766810799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9010267369175022511207199 13515401053762533766810799)
      ·
        refine ⟨20273101580643800650216199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13515401053762533766810799 20273101580643800650216199)
        ·
          refine ⟨30409652370965700975324299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20273101580643800650216199 30409652370965700975324299)
          ·
            refine ⟨45614478556448551462986449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30409652370965700975324299 45614478556448551462986449)
            ·
              refine ⟨34210858917336413597239837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45614478556448551462986449 34210858917336413597239837)
              ·
                refine ⟨12829072094001155098964939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34210858917336413597239837 12829072094001155098964939)
                ·
                  refine ⟨19243608141001732648447409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12829072094001155098964939 19243608141001732648447409)
                  ·
                    refine ⟨14432706105751299486335557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19243608141001732648447409 14432706105751299486335557)
                    ·
                      refine ⟨2706132394828368653687917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14432706105751299486335557 2706132394828368653687917)
                      ·
                        rfl

theorem cell23_5270174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5270174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270174 prefixEnd_5270174 := by exact prefixLift 5270174
  have htrace : WordTrace (prefixWord ++ tailWord_5270174) baseStart_5270174 baseEnd_5270174 := by
    simpa [prefixWord, tailWord_5270174, baseEnd_5270174] using wordTrace_append hprefix tailTrace_5270174
  have hstable : (prefixWord ++ tailWord_5270174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270174).length < 2 ^ (prefixWord ++ tailWord_5270174).sum := by decide
  have hdescent : baseEnd_5270174 < baseStart_5270174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270198 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5270198 : Nat := 118140960795 + 5270198 * 2 ^ 59
def prefixEnd_5270198 : Nat := 4983230072969 + 3 ^ 40 * 5270198 * 2
def baseEnd_5270198 : Nat := 2706144718364076559787807

theorem tailTrace_5270198 : CollatzResearch.WordTrace tailWord_5270198 prefixEnd_5270198 2706144718364076559787807 := by
  unfold tailWord_5270198
  simp only [CollatzResearch.WordTrace]
  refine ⟨12013744535061262437789203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128146608373986799336418165 12013744535061262437789203)
  ·
    refine ⟨18020616802591893656683805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12013744535061262437789203 18020616802591893656683805)
    ·
      refine ⟨6757731300971960121256427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18020616802591893656683805 6757731300971960121256427)
      ·
        refine ⟨10136596951457940181884641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6757731300971960121256427 10136596951457940181884641)
        ·
          refine ⟨7602447713593455136413481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10136596951457940181884641 7602447713593455136413481)
          ·
            refine ⟨5701835785195091352310111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7602447713593455136413481 5701835785195091352310111)
            ·
              refine ⟨8552753677792637028465167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701835785195091352310111 8552753677792637028465167)
              ·
                refine ⟨12829130516688955542697751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8552753677792637028465167 12829130516688955542697751)
                ·
                  refine ⟨19243695775033433314046627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12829130516688955542697751 19243695775033433314046627)
                  ·
                    refine ⟨28865543662550149971069941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19243695775033433314046627 28865543662550149971069941)
                    ·
                      refine ⟨2706144718364076559787807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28865543662550149971069941 2706144718364076559787807)
                      ·
                        rfl

theorem cell23_5270198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5270198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270198 prefixEnd_5270198 := by exact prefixLift 5270198
  have htrace : WordTrace (prefixWord ++ tailWord_5270198) baseStart_5270198 baseEnd_5270198 := by
    simpa [prefixWord, tailWord_5270198, baseEnd_5270198] using wordTrace_append hprefix tailTrace_5270198
  have hstable : (prefixWord ++ tailWord_5270198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270198).length < 2 ^ (prefixWord ++ tailWord_5270198).sum := by decide
  have hdescent : baseEnd_5270198 < baseStart_5270198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270212 : List Nat := [2, 3, 3, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_5270212 : Nat := 118140960795 + 5270212 * 2 ^ 59
def prefixEnd_5270212 : Nat := 4983230072969 + 3 ^ 40 * 5270212 * 2
def baseEnd_5270212 : Nat := 2706151907093239505012743

theorem tailTrace_5270212 : CollatzResearch.WordTrace tailWord_5270212 prefixEnd_5270212 2706151907093239505012743 := by
  unfold tailWord_5270212
  simp only [CollatzResearch.WordTrace]
  refine ⟨96110211591464739697818445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128146948788619652930424593 96110211591464739697818445)
  ·
    refine ⟨36041329346799277386681917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96110211591464739697818445 36041329346799277386681917)
    ·
      refine ⟨13515498505049729020005719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36041329346799277386681917 13515498505049729020005719)
      ·
        refine ⟨20273247757574593530008579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13515498505049729020005719 20273247757574593530008579)
        ·
          refine ⟨30409871636361890295012869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20273247757574593530008579 30409871636361890295012869)
          ·
            refine ⟨5701850931817854430314913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30409871636361890295012869 5701850931817854430314913)
            ·
              refine ⟨4276388198863390822736185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701850931817854430314913 4276388198863390822736185)
              ·
                refine ⟨3207291149147543117052139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4276388198863390822736185 3207291149147543117052139)
                ·
                  refine ⟨4810936723721314675578209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207291149147543117052139 4810936723721314675578209)
                  ·
                    refine ⟨3608202542790986006683657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810936723721314675578209 3608202542790986006683657)
                    ·
                      refine ⟨2706151907093239505012743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608202542790986006683657 2706151907093239505012743)
                      ·
                        rfl

theorem cell23_5270212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_5270212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270212 prefixEnd_5270212 := by exact prefixLift 5270212
  have htrace : WordTrace (prefixWord ++ tailWord_5270212) baseStart_5270212 baseEnd_5270212 := by
    simpa [prefixWord, tailWord_5270212, baseEnd_5270212] using wordTrace_append hprefix tailTrace_5270212
  have hstable : (prefixWord ++ tailWord_5270212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270212).length < 2 ^ (prefixWord ++ tailWord_5270212).sum := by decide
  have hdescent : baseEnd_5270212 < baseStart_5270212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270268 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_5270268 : Nat := 118140960795 + 5270268 * 2 ^ 59
def prefixEnd_5270268 : Nat := 4983230072969 + 3 ^ 40 * 5270268 * 2
def baseEnd_5270268 : Nat := 2706180662009891285912485

theorem tailTrace_5270268 : CollatzResearch.WordTrace tailWord_5270268 prefixEnd_5270268 2706180662009891285912485 := by
  unfold tailWord_5270268
  simp only [CollatzResearch.WordTrace]
  refine ⟨96111232835363300479837729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128148310447151067306450305 96111232835363300479837729)
  ·
    refine ⟨72083424626522475359878297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96111232835363300479837729 72083424626522475359878297)
    ·
      refine ⟨54062568469891856519908723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72083424626522475359878297 54062568469891856519908723)
      ·
        refine ⟨81093852704837784779863085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54062568469891856519908723 81093852704837784779863085)
        ·
          refine ⟨30410194764314169292448657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81093852704837784779863085 30410194764314169292448657)
          ·
            refine ⟨22807646073235626969336493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30410194764314169292448657 22807646073235626969336493)
            ·
              refine ⟨8552867277463360113501185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22807646073235626969336493 8552867277463360113501185)
              ·
                refine ⟨6414650458097520085125889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8552867277463360113501185 6414650458097520085125889)
                ·
                  refine ⟨4810987843573140063844417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414650458097520085125889 4810987843573140063844417)
                  ·
                    refine ⟨3608240882679855047883313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4810987843573140063844417 3608240882679855047883313)
                    ·
                      refine ⟨2706180662009891285912485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608240882679855047883313 2706180662009891285912485)
                      ·
                        rfl

theorem cell23_5270268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_5270268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270268 prefixEnd_5270268 := by exact prefixLift 5270268
  have htrace : WordTrace (prefixWord ++ tailWord_5270268) baseStart_5270268 baseEnd_5270268 := by
    simpa [prefixWord, tailWord_5270268, baseEnd_5270268] using wordTrace_append hprefix tailTrace_5270268
  have hstable : (prefixWord ++ tailWord_5270268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270268).length < 2 ^ (prefixWord ++ tailWord_5270268).sum := by decide
  have hdescent : baseEnd_5270268 < baseStart_5270268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270274 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 7]
def baseStart_5270274 : Nat := 118140960795 + 5270274 * 2 ^ 59
def prefixEnd_5270274 : Nat := 4983230072969 + 3 ^ 40 * 5270274 * 2
def baseEnd_5270274 : Nat := 300687082543757584715273

theorem tailTrace_5270274 : CollatzResearch.WordTrace tailWord_5270274 prefixEnd_5270274 300687082543757584715273 := by
  unfold tailWord_5270274
  simp only [CollatzResearch.WordTrace]
  refine ⟨48055671127176215996098469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128148456339136575989595917 48055671127176215996098469)
  ·
    refine ⟨9010438336345540499268463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48055671127176215996098469 9010438336345540499268463)
    ·
      refine ⟨13515657504518310748902695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9010438336345540499268463 13515657504518310748902695)
      ·
        refine ⟨20273486256777466123354043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13515657504518310748902695 20273486256777466123354043)
        ·
          refine ⟨30410229385166199185031065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20273486256777466123354043 30410229385166199185031065)
          ·
            refine ⟨22807672038874649388773299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30410229385166199185031065 22807672038874649388773299)
            ·
              refine ⟨34211508058311974083159949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22807672038874649388773299 34211508058311974083159949)
              ·
                refine ⟨12829315521866990281184981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34211508058311974083159949 12829315521866990281184981)
                ·
                  refine ⟨300687082543757584715273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12829315521866990281184981 300687082543757584715273)
                  ·
                    rfl

theorem cell23_5270274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_5270274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270274 prefixEnd_5270274 := by exact prefixLift 5270274
  have htrace : WordTrace (prefixWord ++ tailWord_5270274) baseStart_5270274 baseEnd_5270274 := by
    simpa [prefixWord, tailWord_5270274, baseEnd_5270274] using wordTrace_append hprefix tailTrace_5270274
  have hstable : (prefixWord ++ tailWord_5270274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270274).length < 2 ^ (prefixWord ++ tailWord_5270274).sum := by decide
  have hdescent : baseEnd_5270274 < baseStart_5270274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270308 : List Nat := [2, 3, 1, 3, 3, 2, 1, 3, 5]
def baseStart_5270308 : Nat := 118140960795 + 5270308 * 2 ^ 59
def prefixEnd_5270308 : Nat := 4983230072969 + 3 ^ 40 * 5270308 * 2
def baseEnd_5270308 : Nat := 300689022359563458823589

theorem tailTrace_5270308 : CollatzResearch.WordTrace tailWord_5270308 prefixEnd_5270308 300689022359563458823589 := by
  unfold tailWord_5270308
  simp only [CollatzResearch.WordTrace]
  refine ⟨96111962295290843895565789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128149283060387791860754385 96111962295290843895565789)
  ·
    refine ⟨36041985860734066460837171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96111962295290843895565789 36041985860734066460837171)
    ·
      refine ⟨54062978791101099691255757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36041985860734066460837171 54062978791101099691255757)
      ·
        refine ⟨20273617046662912384220909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54062978791101099691255757 20273617046662912384220909)
        ·
          refine ⟨7602606392498592144082841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20273617046662912384220909 7602606392498592144082841)
          ·
            refine ⟨5701954794373944108062131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7602606392498592144082841 5701954794373944108062131)
            ·
              refine ⟨8552932191560916162093197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5701954794373944108062131 8552932191560916162093197)
              ·
                refine ⟨3207349571835343560784949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8552932191560916162093197 3207349571835343560784949)
                ·
                  refine ⟨300689022359563458823589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207349571835343560784949 300689022359563458823589)
                  ·
                    rfl

theorem cell23_5270308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_5270308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270308 prefixEnd_5270308 := by exact prefixLift 5270308
  have htrace : WordTrace (prefixWord ++ tailWord_5270308) baseStart_5270308 baseEnd_5270308 := by
    simpa [prefixWord, tailWord_5270308, baseEnd_5270308] using wordTrace_append hprefix tailTrace_5270308
  have hstable : (prefixWord ++ tailWord_5270308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270308).length < 2 ^ (prefixWord ++ tailWord_5270308).sum := by decide
  have hdescent : baseEnd_5270308 < baseStart_5270308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270344 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_5270344 : Nat := 118140960795 + 5270344 * 2 ^ 59
def prefixEnd_5270344 : Nat := 4983230072969 + 3 ^ 40 * 5270344 * 2
def baseEnd_5270344 : Nat := 2706219686539632988562135

theorem tailTrace_5270344 : CollatzResearch.WordTrace tailWord_5270344 prefixEnd_5270344 2706219686539632988562135 := by
  unfold tailWord_5270344
  simp only [CollatzResearch.WordTrace]
  refine ⟨96112618809225632969721043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128150158412300843959628057 96112618809225632969721043)
  ·
    refine ⟨144168928213838449454581565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96112618809225632969721043 144168928213838449454581565)
    ·
      refine ⟨54063348080189418545468087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144168928213838449454581565 54063348080189418545468087)
      ·
        refine ⟨81095022120284127818202131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54063348080189418545468087 81095022120284127818202131)
        ·
          refine ⟨121642533180426191727303197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81095022120284127818202131 121642533180426191727303197)
          ·
            refine ⟨45615949942659821897738699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121642533180426191727303197 45615949942659821897738699)
            ·
              refine ⟨68423924913989732846608049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45615949942659821897738699 68423924913989732846608049)
              ·
                refine ⟨51317943685492299634956037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68423924913989732846608049 51317943685492299634956037)
                ·
                  refine ⟨9622114441029806181554257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51317943685492299634956037 9622114441029806181554257)
                  ·
                    refine ⟨7216585830772354636165693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9622114441029806181554257 7216585830772354636165693)
                    ·
                      refine ⟨2706219686539632988562135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7216585830772354636165693 2706219686539632988562135)
                      ·
                        rfl

theorem cell23_5270344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_5270344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270344 prefixEnd_5270344 := by exact prefixLift 5270344
  have htrace : WordTrace (prefixWord ++ tailWord_5270344) baseStart_5270344 baseEnd_5270344 := by
    simpa [prefixWord, tailWord_5270344, baseEnd_5270344] using wordTrace_append hprefix tailTrace_5270344
  have hstable : (prefixWord ++ tailWord_5270344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270344).length < 2 ^ (prefixWord ++ tailWord_5270344).sum := by decide
  have hdescent : baseEnd_5270344 < baseStart_5270344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270361 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 3]
def baseStart_5270361 : Nat := 118140960795 + 5270361 * 2 ^ 59
def prefixEnd_5270361 : Nat := 4983230072969 + 3 ^ 40 * 5270361 * 2
def baseEnd_5270361 : Nat := 2706228415710759422049557

theorem tailTrace_5270361 : CollatzResearch.WordTrace tailWord_5270361 prefixEnd_5270361 2706228415710759422049557 := by
  unfold tailWord_5270361
  simp only [CollatzResearch.WordTrace]
  refine ⟨192225857659389677842810937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128150571772926451895207291 192225857659389677842810937)
  ·
    refine ⟨144169393244542258382108203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192225857659389677842810937 144169393244542258382108203)
    ·
      refine ⟨216254089866813387573162305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144169393244542258382108203 216254089866813387573162305)
      ·
        refine ⟨162190567400110040679871729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216254089866813387573162305 162190567400110040679871729)
        ·
          refine ⟨121642925550082530509903797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162190567400110040679871729 121642925550082530509903797)
          ·
            refine ⟨11404024270320237235303481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121642925550082530509903797 11404024270320237235303481)
            ·
              refine ⟨8553018202740177926477611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11404024270320237235303481 8553018202740177926477611)
              ·
                refine ⟨12829527304110266889716417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8553018202740177926477611 12829527304110266889716417)
                ·
                  refine ⟨9622145478082700167287313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12829527304110266889716417 9622145478082700167287313)
                  ·
                    refine ⟨7216609108562025125465485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9622145478082700167287313 7216609108562025125465485)
                    ·
                      refine ⟨2706228415710759422049557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7216609108562025125465485 2706228415710759422049557)
                      ·
                        rfl

theorem cell23_5270361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_5270361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270361 prefixEnd_5270361 := by exact prefixLift 5270361
  have htrace : WordTrace (prefixWord ++ tailWord_5270361) baseStart_5270361 baseEnd_5270361 := by
    simpa [prefixWord, tailWord_5270361, baseEnd_5270361] using wordTrace_append hprefix tailTrace_5270361
  have hstable : (prefixWord ++ tailWord_5270361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270361).length < 2 ^ (prefixWord ++ tailWord_5270361).sum := by decide
  have hdescent : baseEnd_5270361 < baseStart_5270361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270385 : List Nat := [1, 2, 2, 2, 1, 6, 2, 2, 1, 4]
def baseStart_5270385 : Nat := 118140960795 + 5270385 * 2 ^ 59
def prefixEnd_5270385 : Nat := 4983230072969 + 3 ^ 40 * 5270385 * 2
def baseEnd_5270385 : Nat := 902080246415489109383149

theorem tailTrace_5270385 : CollatzResearch.WordTrace tailWord_5270385 prefixEnd_5270385 902080246415489109383149 := by
  unfold tailWord_5270385
  simp only [CollatzResearch.WordTrace]
  refine ⟨192226733011302729941684609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128151155340868486627789739 192226733011302729941684609)
  ·
    refine ⟨144170049758477047456263457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192226733011302729941684609 144170049758477047456263457)
    ·
      refine ⟨108127537318857785592197593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144170049758477047456263457 108127537318857785592197593)
      ·
        refine ⟨81095652989143339194148195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108127537318857785592197593 81095652989143339194148195)
        ·
          refine ⟨121643479483715008791222293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81095652989143339194148195 121643479483715008791222293)
          ·
            refine ⟨5702038100799141037088545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121643479483715008791222293 5702038100799141037088545)
            ·
              refine ⟨4276528575599355777816409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5702038100799141037088545 4276528575599355777816409)
              ·
                refine ⟨3207396431699516833362307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4276528575599355777816409 3207396431699516833362307)
                ·
                  refine ⟨4811094647549275250043461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207396431699516833362307 4811094647549275250043461)
                  ·
                    refine ⟨902080246415489109383149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4811094647549275250043461 902080246415489109383149)
                    ·
                      rfl

theorem cell23_5270385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_5270385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270385 prefixEnd_5270385 := by exact prefixLift 5270385
  have htrace : WordTrace (prefixWord ++ tailWord_5270385) baseStart_5270385 baseEnd_5270385 := by
    simpa [prefixWord, tailWord_5270385, baseEnd_5270385] using wordTrace_append hprefix tailTrace_5270385
  have hstable : (prefixWord ++ tailWord_5270385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270385).length < 2 ^ (prefixWord ++ tailWord_5270385).sum := by decide
  have hdescent : baseEnd_5270385 < baseStart_5270385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270408 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_5270408 : Nat := 118140960795 + 5270408 * 2 ^ 59
def prefixEnd_5270408 : Nat := 4983230072969 + 3 ^ 40 * 5270408 * 2
def baseEnd_5270408 : Nat := 2706252549301520738161841

theorem tailTrace_5270408 : CollatzResearch.WordTrace tailWord_5270408 prefixEnd_5270408 2706252549301520738161841 := by
  unfold tailWord_5270408
  simp only [CollatzResearch.WordTrace]
  refine ⟨96113785945109702434885939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128151714593479603246514585 96113785945109702434885939)
  ·
    refine ⟨144170678917664553652328909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96113785945109702434885939 144170678917664553652328909)
    ·
      refine ⟨54064004594124207619623341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144170678917664553652328909 54064004594124207619623341)
      ·
        refine ⟨20274001722796577857358753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54064004594124207619623341 20274001722796577857358753)
        ·
          refine ⟨15205501292097433393019065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20274001722796577857358753 15205501292097433393019065)
          ·
            refine ⟨11404125969073075044764299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15205501292097433393019065 11404125969073075044764299)
            ·
              refine ⟨17106188953609612567146449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11404125969073075044764299 17106188953609612567146449)
              ·
                refine ⟨12829641715207209425359837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17106188953609612567146449 12829641715207209425359837)
                ·
                  refine ⟨4811115643202703534509939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12829641715207209425359837 4811115643202703534509939)
                  ·
                    refine ⟨7216673464804055301764909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4811115643202703534509939 7216673464804055301764909)
                    ·
                      refine ⟨2706252549301520738161841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7216673464804055301764909 2706252549301520738161841)
                      ·
                        rfl

theorem cell23_5270408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_5270408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270408 prefixEnd_5270408 := by exact prefixLift 5270408
  have htrace : WordTrace (prefixWord ++ tailWord_5270408) baseStart_5270408 baseEnd_5270408 := by
    simpa [prefixWord, tailWord_5270408, baseEnd_5270408] using wordTrace_append hprefix tailTrace_5270408
  have hstable : (prefixWord ++ tailWord_5270408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270408).length < 2 ^ (prefixWord ++ tailWord_5270408).sum := by decide
  have hdescent : baseEnd_5270408 < baseStart_5270408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270427 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 6]
def baseStart_5270427 : Nat := 118140960795 + 5270427 * 2 ^ 59
def prefixEnd_5270427 : Nat := 4983230072969 + 3 ^ 40 * 5270427 * 2
def baseEnd_5270427 : Nat := 2706262305433956163824253

theorem tailTrace_5270427 : CollatzResearch.WordTrace tailWord_5270427 prefixEnd_5270427 2706262305433956163824253 := by
  unfold tailWord_5270427
  simp only [CollatzResearch.WordTrace]
  refine ⟨192228264877150571114713535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128152176584767047409809023 192228264877150571114713535)
  ·
    refine ⟨288342397315725856672070303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192228264877150571114713535 288342397315725856672070303)
    ·
      refine ⟨432513595973588785008105455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288342397315725856672070303 432513595973588785008105455)
      ·
        refine ⟨648770393960383177512158183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432513595973588785008105455 648770393960383177512158183)
        ·
          refine ⟨973155590940574766268237275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648770393960383177512158183 973155590940574766268237275)
          ·
            refine ⟨1459733386410862149402355913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973155590940574766268237275 1459733386410862149402355913)
            ·
              refine ⟨1094800039808146612051766935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459733386410862149402355913 1094800039808146612051766935)
              ·
                refine ⟨1642200059712219918077650403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094800039808146612051766935 1642200059712219918077650403)
                ·
                  refine ⟨2463300089568329877116475605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642200059712219918077650403 2463300089568329877116475605)
                  ·
                    refine ⟨57733595849257731494917397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2463300089568329877116475605 57733595849257731494917397)
                    ·
                      refine ⟨2706262305433956163824253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57733595849257731494917397 2706262305433956163824253)
                      ·
                        rfl

theorem cell23_5270427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_5270427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270427 prefixEnd_5270427 := by exact prefixLift 5270427
  have htrace : WordTrace (prefixWord ++ tailWord_5270427) baseStart_5270427 baseEnd_5270427 := by
    simpa [prefixWord, tailWord_5270427, baseEnd_5270427] using wordTrace_append hprefix tailTrace_5270427
  have hstable : (prefixWord ++ tailWord_5270427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270427).length < 2 ^ (prefixWord ++ tailWord_5270427).sum := by decide
  have hdescent : baseEnd_5270427 < baseStart_5270427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270428 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_5270428 : Nat := 118140960795 + 5270428 * 2 ^ 59
def prefixEnd_5270428 : Nat := 4983230072969 + 3 ^ 40 * 5270428 * 2
def baseEnd_5270428 : Nat := 902087606304870219970583

theorem tailTrace_5270428 : CollatzResearch.WordTrace tailWord_5270428 prefixEnd_5270428 902087606304870219970583 := by
  unfold tailWord_5270428
  simp only [CollatzResearch.WordTrace]
  refine ⟨96114150675073474142749969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128152200900097965523666625 96114150675073474142749969)
  ·
    refine ⟨72085613006305105607062477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96114150675073474142749969 72085613006305105607062477)
    ·
      refine ⟨27032104877364414602648429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72085613006305105607062477 27032104877364414602648429)
      ·
        refine ⟨10137039329011655475993161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27032104877364414602648429 10137039329011655475993161)
        ·
          refine ⟨7602779496758741606994871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10137039329011655475993161 7602779496758741606994871)
          ·
            refine ⟨11404169245138112410492307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7602779496758741606994871 11404169245138112410492307)
            ·
              refine ⟨17106253867707168615738461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11404169245138112410492307 17106253867707168615738461)
              ·
                refine ⟨6414845200390188230901923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17106253867707168615738461 6414845200390188230901923)
                ·
                  refine ⟨9622267800585282346352885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414845200390188230901923 9622267800585282346352885)
                  ·
                    refine ⟨902087606304870219970583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9622267800585282346352885 902087606304870219970583)
                    ·
                      rfl

theorem cell23_5270428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_5270428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270428 prefixEnd_5270428 := by exact prefixLift 5270428
  have htrace : WordTrace (prefixWord ++ tailWord_5270428) baseStart_5270428 baseEnd_5270428 := by
    simpa [prefixWord, tailWord_5270428, baseEnd_5270428] using wordTrace_append hprefix tailTrace_5270428
  have hstable : (prefixWord ++ tailWord_5270428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270428).length < 2 ^ (prefixWord ++ tailWord_5270428).sum := by decide
  have hdescent : baseEnd_5270428 < baseStart_5270428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270458 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_5270458 : Nat := 118140960795 + 5270458 * 2 ^ 59
def prefixEnd_5270458 : Nat := 4983230072969 + 3 ^ 40 * 5270458 * 2
def baseEnd_5270458 : Nat := 902092741111415180845537

theorem tailTrace_5270458 : CollatzResearch.WordTrace tailWord_5270458 prefixEnd_5270458 902092741111415180845537 := by
  unfold tailWord_5270458
  simp only [CollatzResearch.WordTrace]
  refine ⟨48057348885009565852273007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128152930360025508939394685 48057348885009565852273007)
  ·
    refine ⟨72086023327514348778409511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48057348885009565852273007 72086023327514348778409511)
    ·
      refine ⟨108129034991271523167614267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72086023327514348778409511 108129034991271523167614267)
      ·
        refine ⟨162193552486907284751421401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108129034991271523167614267 162193552486907284751421401)
        ·
          refine ⟨121645164365180463563566051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162193552486907284751421401 121645164365180463563566051)
          ·
            refine ⟨182467746547770695345349077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121645164365180463563566051 182467746547770695345349077)
            ·
              refine ⟨4276587809713375672156619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182467746547770695345349077 4276587809713375672156619)
              ·
                refine ⟨6414881714570063508234929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276587809713375672156619 6414881714570063508234929)
                ·
                  refine ⟨4811161285927547631176197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414881714570063508234929 4811161285927547631176197)
                  ·
                    refine ⟨902092741111415180845537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4811161285927547631176197 902092741111415180845537)
                    ·
                      rfl

theorem cell23_5270458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_5270458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270458 prefixEnd_5270458 := by exact prefixLift 5270458
  have htrace : WordTrace (prefixWord ++ tailWord_5270458) baseStart_5270458 baseEnd_5270458 := by
    simpa [prefixWord, tailWord_5270458, baseEnd_5270458] using wordTrace_append hprefix tailTrace_5270458
  have hstable : (prefixWord ++ tailWord_5270458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270458).length < 2 ^ (prefixWord ++ tailWord_5270458).sum := by decide
  have hdescent : baseEnd_5270458 < baseStart_5270458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270461 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_5270461 : Nat := 118140960795 + 5270461 * 2 ^ 59
def prefixEnd_5270461 : Nat := 4983230072969 + 3 ^ 40 * 5270461 * 2
def baseEnd_5270461 : Nat := 2706279763776209030799097

theorem tailTrace_5270461 : CollatzResearch.WordTrace tailWord_5270461 prefixEnd_5270461 2706279763776209030799097 := by
  unfold tailWord_5270461
  simp only [CollatzResearch.WordTrace]
  refine ⟨192229504959027394921451237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128153003306018263280967491 192229504959027394921451237)
  ·
    refine ⟨36043032179817636547772107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192229504959027394921451237 36043032179817636547772107)
    ·
      refine ⟨54064548269726454821658161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36043032179817636547772107 54064548269726454821658161)
      ·
        refine ⟨40548411202294841116243621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54064548269726454821658161 40548411202294841116243621)
        ·
          refine ⟨7602827100430282709295679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40548411202294841116243621 7602827100430282709295679)
          ·
            refine ⟨11404240650645424063943519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7602827100430282709295679 11404240650645424063943519)
            ·
              refine ⟨17106360975968136095915279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11404240650645424063943519 17106360975968136095915279)
              ·
                refine ⟨25659541463952204143872919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17106360975968136095915279 25659541463952204143872919)
                ·
                  refine ⟨38489312195928306215809379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25659541463952204143872919 38489312195928306215809379)
                  ·
                    refine ⟨57733968293892459323714069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38489312195928306215809379 57733968293892459323714069)
                    ·
                      refine ⟨2706279763776209030799097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57733968293892459323714069 2706279763776209030799097)
                      ·
                        rfl

theorem cell23_5270461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_5270461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270461 prefixEnd_5270461 := by exact prefixLift 5270461
  have htrace : WordTrace (prefixWord ++ tailWord_5270461) baseStart_5270461 baseEnd_5270461 := by
    simpa [prefixWord, tailWord_5270461, baseEnd_5270461] using wordTrace_append hprefix tailTrace_5270461
  have hstable : (prefixWord ++ tailWord_5270461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270461).length < 2 ^ (prefixWord ++ tailWord_5270461).sum := by decide
  have hdescent : baseEnd_5270461 < baseStart_5270461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270481 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_5270481 : Nat := 118140960795 + 5270481 * 2 ^ 59
def prefixEnd_5270481 : Nat := 4983230072969 + 3 ^ 40 * 5270481 * 2
def baseEnd_5270481 : Nat := 2706290033389298952549005

theorem tailTrace_5270481 : CollatzResearch.WordTrace tailWord_5270481 prefixEnd_5270481 2706290033389298952549005 := by
  unfold tailWord_5270481
  simp only [CollatzResearch.WordTrace]
  refine ⟨192230234418954938337179297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128153489612636625558119531 192230234418954938337179297)
  ·
    refine ⟨144172675814216203752884473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192230234418954938337179297 144172675814216203752884473)
    ·
      refine ⟨108129506860662152814663355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144172675814216203752884473 108129506860662152814663355)
      ·
        refine ⟨162194260290993229221995033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108129506860662152814663355 162194260290993229221995033)
        ·
          refine ⟨121645695218244921916496275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162194260290993229221995033 121645695218244921916496275)
          ·
            refine ⟨182468542827367382874744413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121645695218244921916496275 182468542827367382874744413)
            ·
              refine ⟨68425703560262768578029155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182468542827367382874744413 68425703560262768578029155)
              ·
                refine ⟨102638555340394152867043733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68425703560262768578029155 102638555340394152867043733)
                ·
                  refine ⟨4811182281580975915642675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102638555340394152867043733 4811182281580975915642675)
                  ·
                    refine ⟨7216773422371463873464013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4811182281580975915642675 7216773422371463873464013)
                    ·
                      refine ⟨2706290033389298952549005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7216773422371463873464013 2706290033389298952549005)
                      ·
                        rfl

theorem cell23_5270481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_5270481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270481 prefixEnd_5270481 := by exact prefixLift 5270481
  have htrace : WordTrace (prefixWord ++ tailWord_5270481) baseStart_5270481 baseEnd_5270481 := by
    simpa [prefixWord, tailWord_5270481, baseEnd_5270481] using wordTrace_append hprefix tailTrace_5270481
  have hstable : (prefixWord ++ tailWord_5270481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270481).length < 2 ^ (prefixWord ++ tailWord_5270481).sum := by decide
  have hdescent : baseEnd_5270481 < baseStart_5270481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270516 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5270516 : Nat := 118140960795 + 5270516 * 2 ^ 59
def prefixEnd_5270516 : Nat := 4983230072969 + 3 ^ 40 * 5270516 * 2
def baseEnd_5270516 : Nat := 2706308005212206315611345

theorem tailTrace_5270516 : CollatzResearch.WordTrace tailWord_5270516 prefixEnd_5270516 2706308005212206315611345 := by
  unfold tailWord_5270516
  simp only [CollatzResearch.WordTrace]
  refine ⟨96115755486914069657351701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128154340649218759543135601 96115755486914069657351701)
  ·
    refine ⟨4505426038449097015188361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96115755486914069657351701 4505426038449097015188361)
    ·
      refine ⟨3379069528836822761391271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4505426038449097015188361 3379069528836822761391271)
      ·
        refine ⟨5068604293255234142086907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379069528836822761391271 5068604293255234142086907)
        ·
          refine ⟨7602906439882851213130361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5068604293255234142086907 7602906439882851213130361)
          ·
            refine ⟨5702179829912138409847771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7602906439882851213130361 5702179829912138409847771)
            ·
              refine ⟨8553269744868207614771657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702179829912138409847771 8553269744868207614771657)
              ·
                refine ⟨6414952308651155711078743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8553269744868207614771657 6414952308651155711078743)
                ·
                  refine ⟨9622428462976733566618115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414952308651155711078743 9622428462976733566618115)
                  ·
                    refine ⟨14433642694465100349927173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9622428462976733566618115 14433642694465100349927173)
                    ·
                      refine ⟨2706308005212206315611345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14433642694465100349927173 2706308005212206315611345)
                      ·
                        rfl

theorem cell23_5270516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5270516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270516 prefixEnd_5270516 := by exact prefixLift 5270516
  have htrace : WordTrace (prefixWord ++ tailWord_5270516) baseStart_5270516 baseEnd_5270516 := by
    simpa [prefixWord, tailWord_5270516, baseEnd_5270516] using wordTrace_append hprefix tailTrace_5270516
  have hstable : (prefixWord ++ tailWord_5270516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270516).length < 2 ^ (prefixWord ++ tailWord_5270516).sum := by decide
  have hdescent : baseEnd_5270516 < baseStart_5270516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270538 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_5270538 : Nat := 118140960795 + 5270538 * 2 ^ 59
def prefixEnd_5270538 : Nat := 4983230072969 + 3 ^ 40 * 5270538 * 2
def baseEnd_5270538 : Nat := 2706319301786605229536243

theorem tailTrace_5270538 : CollatzResearch.WordTrace tailWord_5270538 prefixEnd_5270538 2706319301786605229536243 := by
  unfold tailWord_5270538
  simp only [CollatzResearch.WordTrace]
  refine ⟨48058078344937109268001067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128154875586498958048002845 48058078344937109268001067)
  ·
    refine ⟨72087117517405663902001601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48058078344937109268001067 72087117517405663902001601)
    ·
      refine ⟨54065338138054247926501201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72087117517405663902001601 54065338138054247926501201)
      ·
        refine ⟨40549003603540685944875901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54065338138054247926501201 40549003603540685944875901)
        ·
          refine ⟨15205876351327757229328463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40549003603540685944875901 15205876351327757229328463)
          ·
            refine ⟨22808814526991635843992695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15205876351327757229328463 22808814526991635843992695)
            ·
              refine ⟨34213221790487453765989043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22808814526991635843992695 34213221790487453765989043)
              ·
                refine ⟨51319832685731180648983565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34213221790487453765989043 51319832685731180648983565)
                ·
                  refine ⟨19244937257149192743368837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51319832685731180648983565 19244937257149192743368837)
                  ·
                    refine ⟨3608425735715473639381657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19244937257149192743368837 3608425735715473639381657)
                    ·
                      refine ⟨2706319301786605229536243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608425735715473639381657 2706319301786605229536243)
                      ·
                        rfl

theorem cell23_5270538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_5270538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270538 prefixEnd_5270538 := by exact prefixLift 5270538
  have htrace : WordTrace (prefixWord ++ tailWord_5270538) baseStart_5270538 baseEnd_5270538 := by
    simpa [prefixWord, tailWord_5270538, baseEnd_5270538] using wordTrace_append hprefix tailTrace_5270538
  have hstable : (prefixWord ++ tailWord_5270538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270538).length < 2 ^ (prefixWord ++ tailWord_5270538).sum := by decide
  have hdescent : baseEnd_5270538 < baseStart_5270538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270542 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_5270542 : Nat := 118140960795 + 5270542 * 2 ^ 59
def prefixEnd_5270542 : Nat := 4983230072969 + 3 ^ 40 * 5270542 * 2
def baseEnd_5270542 : Nat := 2706321355709223213886225

theorem tailTrace_5270542 : CollatzResearch.WordTrace tailWord_5270542 prefixEnd_5270542 2706321355709223213886225 := by
  unfold tailWord_5270542
  simp only [CollatzResearch.WordTrace]
  refine ⟨24029057408966743219393735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128154972847822630503433253 24029057408966743219393735)
  ·
    refine ⟨36043586113450114829090603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24029057408966743219393735 36043586113450114829090603)
    ·
      refine ⟨54065379170175172243635905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36043586113450114829090603 54065379170175172243635905)
      ·
        refine ⟨40549034377631379182726929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54065379170175172243635905 40549034377631379182726929)
        ·
          refine ⟨30411775783223534387045197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40549034377631379182726929 30411775783223534387045197)
          ·
            refine ⟨11404415918708825395141949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30411775783223534387045197 11404415918708825395141949)
            ·
              refine ⟨4276655969515809523178231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11404415918708825395141949 4276655969515809523178231)
              ·
                refine ⟨6414983954273714284767347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276655969515809523178231 6414983954273714284767347)
                ·
                  refine ⟨9622475931410571427151021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414983954273714284767347 9622475931410571427151021)
                  ·
                    refine ⟨3608428474278964285181633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9622475931410571427151021 3608428474278964285181633)
                    ·
                      refine ⟨2706321355709223213886225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608428474278964285181633 2706321355709223213886225)
                      ·
                        rfl

theorem cell23_5270542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_5270542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270542 prefixEnd_5270542 := by exact prefixLift 5270542
  have htrace : WordTrace (prefixWord ++ tailWord_5270542) baseStart_5270542 baseEnd_5270542 := by
    simpa [prefixWord, tailWord_5270542, baseEnd_5270542] using wordTrace_append hprefix tailTrace_5270542
  have hstable : (prefixWord ++ tailWord_5270542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270542).length < 2 ^ (prefixWord ++ tailWord_5270542).sum := by decide
  have hdescent : baseEnd_5270542 < baseStart_5270542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270571 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 3]
def baseStart_5270571 : Nat := 118140960795 + 5270571 * 2 ^ 59
def prefixEnd_5270571 : Nat := 4983230072969 + 3 ^ 40 * 5270571 * 2
def baseEnd_5270571 : Nat := 2706336246648203600423591

theorem tailTrace_5270571 : CollatzResearch.WordTrace tailWord_5270571 prefixEnd_5270571 2706336246648203600423591 := by
  unfold tailWord_5270571
  simp only [CollatzResearch.WordTrace]
  refine ⟨192233516988628883707955567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128155677992419255805303711 192233516988628883707955567)
  ·
    refine ⟨288350275482943325561933351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192233516988628883707955567 288350275482943325561933351)
    ·
      refine ⟨432525413224414988342900027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288350275482943325561933351 432525413224414988342900027)
      ·
        refine ⟨648788119836622482514350041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432525413224414988342900027 648788119836622482514350041)
        ·
          refine ⟨486591089877466861885762531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648788119836622482514350041 486591089877466861885762531)
          ·
            refine ⟨729886634816200292828643797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486591089877466861885762531 729886634816200292828643797)
            ·
              refine ⟨17106718003504694363171339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 729886634816200292828643797 17106718003504694363171339)
              ·
                refine ⟨25660077005257041544757009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17106718003504694363171339 25660077005257041544757009)
                ·
                  refine ⟨19245057753942781158567757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25660077005257041544757009 19245057753942781158567757)
                  ·
                    refine ⟨7216896657728542934462909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19245057753942781158567757 7216896657728542934462909)
                    ·
                      refine ⟨2706336246648203600423591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7216896657728542934462909 2706336246648203600423591)
                      ·
                        rfl

theorem cell23_5270571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 3].length) (baseStart_5270571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270571 prefixEnd_5270571 := by exact prefixLift 5270571
  have htrace : WordTrace (prefixWord ++ tailWord_5270571) baseStart_5270571 baseEnd_5270571 := by
    simpa [prefixWord, tailWord_5270571, baseEnd_5270571] using wordTrace_append hprefix tailTrace_5270571
  have hstable : (prefixWord ++ tailWord_5270571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270571).length < 2 ^ (prefixWord ++ tailWord_5270571).sum := by decide
  have hdescent : baseEnd_5270571 < baseStart_5270571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270622 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_5270622 : Nat := 118140960795 + 5270622 * 2 ^ 59
def prefixEnd_5270622 : Nat := 4983230072969 + 3 ^ 40 * 5270622 * 2
def baseEnd_5270622 : Nat := 2706362434161582900885857

theorem tailTrace_5270622 : CollatzResearch.WordTrace tailWord_5270622 prefixEnd_5270622 2706362434161582900885857 := by
  unfold tailWord_5270622
  simp only [CollatzResearch.WordTrace]
  refine ⟨24029422138930514927257765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128156918074296079612041413 24029422138930514927257765)
  ·
    refine ⟨4505516651049471548860831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24029422138930514927257765 4505516651049471548860831)
    ·
      refine ⟨6758274976574207323291247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4505516651049471548860831 6758274976574207323291247)
      ·
        refine ⟨10137412464861310984936871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758274976574207323291247 10137412464861310984936871)
        ·
          refine ⟨15206118697291966477405307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10137412464861310984936871 15206118697291966477405307)
          ·
            refine ⟨22809178045937949716107961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15206118697291966477405307 22809178045937949716107961)
            ·
              refine ⟨17106883534453462287080971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22809178045937949716107961 17106883534453462287080971)
              ·
                refine ⟨25660325301680193430621457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17106883534453462287080971 25660325301680193430621457)
                ·
                  refine ⟨19245243976260145072966093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25660325301680193430621457 19245243976260145072966093)
                  ·
                    refine ⟨7216966491097554402362285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19245243976260145072966093 7216966491097554402362285)
                    ·
                      refine ⟨2706362434161582900885857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7216966491097554402362285 2706362434161582900885857)
                      ·
                        rfl

theorem cell23_5270622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_5270622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270622 prefixEnd_5270622 := by exact prefixLift 5270622
  have htrace : WordTrace (prefixWord ++ tailWord_5270622) baseStart_5270622 baseEnd_5270622 := by
    simpa [prefixWord, tailWord_5270622, baseEnd_5270622] using wordTrace_append hprefix tailTrace_5270622
  have hstable : (prefixWord ++ tailWord_5270622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270622).length < 2 ^ (prefixWord ++ tailWord_5270622).sum := by decide
  have hdescent : baseEnd_5270622 < baseStart_5270622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270728 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 4, 4]
def baseStart_5270728 : Nat := 118140960795 + 5270728 * 2 ^ 59
def prefixEnd_5270728 : Nat := 4983230072969 + 3 ^ 40 * 5270728 * 2
def baseEnd_5270728 : Nat := 902138954370319828720123

theorem tailTrace_5270728 : CollatzResearch.WordTrace tailWord_5270728 prefixEnd_5270728 902138954370319828720123 := by
  unfold tailWord_5270728
  simp only [CollatzResearch.WordTrace]
  refine ⟨96119621624530049760710419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128159495499373399680947225 96119621624530049760710419)
  ·
    refine ⟨144179432436795074641065629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96119621624530049760710419 144179432436795074641065629)
    ·
      refine ⟨54067287163798152990399611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144179432436795074641065629 54067287163798152990399611)
      ·
        refine ⟨81100930745697229485599417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54067287163798152990399611 81100930745697229485599417)
        ·
          refine ⟨60825698059272922114199563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81100930745697229485599417 60825698059272922114199563)
          ·
            refine ⟨91238547088909383171299345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60825698059272922114199563 91238547088909383171299345)
            ·
              refine ⟨68428910316682037378474509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91238547088909383171299345 68428910316682037378474509)
              ·
                refine ⟨25660841368755764016927941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68428910316682037378474509 25660841368755764016927941)
                ·
                  refine ⟨4811407756641705753173989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25660841368755764016927941 4811407756641705753173989)
                  ·
                    refine ⟨902138954370319828720123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4811407756641705753173989 902138954370319828720123)
                    ·
                      rfl

theorem cell23_5270728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_5270728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270728 prefixEnd_5270728 := by exact prefixLift 5270728
  have htrace : WordTrace (prefixWord ++ tailWord_5270728) baseStart_5270728 baseEnd_5270728 := by
    simpa [prefixWord, tailWord_5270728, baseEnd_5270728] using wordTrace_append hprefix tailTrace_5270728
  have hstable : (prefixWord ++ tailWord_5270728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270728).length < 2 ^ (prefixWord ++ tailWord_5270728).sum := by decide
  have hdescent : baseEnd_5270728 < baseStart_5270728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270731 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 6]
def baseStart_5270731 : Nat := 118140960795 + 5270731 * 2 ^ 59
def prefixEnd_5270731 : Nat := 4983230072969 + 3 ^ 40 * 5270731 * 2
def baseEnd_5270731 : Nat := 2706418403552922974422855

theorem tailTrace_5270731 : CollatzResearch.WordTrace tailWord_5270731 prefixEnd_5270731 2706418403552922974422855 := by
  unfold tailWord_5270731
  simp only [CollatzResearch.WordTrace]
  refine ⟨192239352668049231033780047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128159568445366154022520031 192239352668049231033780047)
  ·
    refine ⟨288359029002073846550670071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192239352668049231033780047 288359029002073846550670071)
    ·
      refine ⟨432538543503110769826005107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288359029002073846550670071 432538543503110769826005107)
      ·
        refine ⟨648807815254666154739007661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432538543503110769826005107 648807815254666154739007661)
        ·
          refine ⟨243302930720499808027127873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 648807815254666154739007661 243302930720499808027127873)
          ·
            refine ⟨182477198040374856020345905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243302930720499808027127873 182477198040374856020345905)
            ·
              refine ⟨136857898530281142015259429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182477198040374856020345905 136857898530281142015259429)
              ·
                refine ⟨25660855974427714127861143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136857898530281142015259429 25660855974427714127861143)
                ·
                  refine ⟨38491283961641571191791715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25660855974427714127861143 38491283961641571191791715)
                  ·
                    refine ⟨57736925942462356787687573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38491283961641571191791715 57736925942462356787687573)
                    ·
                      refine ⟨2706418403552922974422855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57736925942462356787687573 2706418403552922974422855)
                      ·
                        rfl

theorem cell23_5270731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_5270731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270731 prefixEnd_5270731 := by exact prefixLift 5270731
  have htrace : WordTrace (prefixWord ++ tailWord_5270731) baseStart_5270731 baseEnd_5270731 := by
    simpa [prefixWord, tailWord_5270731, baseEnd_5270731] using wordTrace_append hprefix tailTrace_5270731
  have hstable : (prefixWord ++ tailWord_5270731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270731).length < 2 ^ (prefixWord ++ tailWord_5270731).sum := by decide
  have hdescent : baseEnd_5270731 < baseStart_5270731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270738 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_5270738 : Nat := 118140960795 + 5270738 * 2 ^ 59
def prefixEnd_5270738 : Nat := 4983230072969 + 3 ^ 40 * 5270738 * 2
def baseEnd_5270738 : Nat := 2706421997917504447035323

theorem tailTrace_5270738 : CollatzResearch.WordTrace tailWord_5270738 prefixEnd_5270738 2706421997917504447035323 := by
  unfold tailWord_5270738
  simp only [CollatzResearch.WordTrace]
  refine ⟨48059901994755967807321217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128159738652682580819523245 48059901994755967807321217)
  ·
    refine ⟨36044926496066975855490913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48059901994755967807321217 36044926496066975855490913)
    ·
      refine ⟨27033694872050231891618185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36044926496066975855490913 27033694872050231891618185)
      ·
        refine ⟨20275271154037673918713639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27033694872050231891618185 20275271154037673918713639)
        ·
          refine ⟨30412906731056510878070459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20275271154037673918713639 30412906731056510878070459)
          ·
            refine ⟨45619360096584766317105689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30412906731056510878070459 45619360096584766317105689)
            ·
              refine ⟨34214520072438574737829267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45619360096584766317105689 34214520072438574737829267)
              ·
                refine ⟨51321780108657862106743901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34214520072438574737829267 51321780108657862106743901)
                ·
                  refine ⟨19245667540746698290028963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51321780108657862106743901 19245667540746698290028963)
                  ·
                    refine ⟨28868501311120047435043445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19245667540746698290028963 28868501311120047435043445)
                    ·
                      refine ⟨2706421997917504447035323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28868501311120047435043445 2706421997917504447035323)
                      ·
                        rfl

theorem cell23_5270738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_5270738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270738 prefixEnd_5270738 := by exact prefixLift 5270738
  have htrace : WordTrace (prefixWord ++ tailWord_5270738) baseStart_5270738 baseEnd_5270738 := by
    simpa [prefixWord, tailWord_5270738, baseEnd_5270738] using wordTrace_append hprefix tailTrace_5270738
  have hstable : (prefixWord ++ tailWord_5270738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270738).length < 2 ^ (prefixWord ++ tailWord_5270738).sum := by decide
  have hdescent : baseEnd_5270738 < baseStart_5270738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270752 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 3, 2, 2]
def baseStart_5270752 : Nat := 118140960795 + 5270752 * 2 ^ 59
def prefixEnd_5270752 : Nat := 4983230072969 + 3 ^ 40 * 5270752 * 2
def baseEnd_5270752 : Nat := 2706429186646667392260259

theorem tailTrace_5270752 : CollatzResearch.WordTrace tailWord_5270752 prefixEnd_5270752 2706429186646667392260259 := by
  unfold tailWord_5270752
  simp only [CollatzResearch.WordTrace]
  refine ⟨96120059300486575810147255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128160079067315434413529673 96120059300486575810147255)
  ·
    refine ⟨144180088950729863715220883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96120059300486575810147255 144180088950729863715220883)
    ·
      refine ⟨216270133426094795572831325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144180088950729863715220883 216270133426094795572831325)
      ·
        refine ⟨81101300034785548339811747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216270133426094795572831325 81101300034785548339811747)
        ·
          refine ⟨121651950052178322509717621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81101300034785548339811747 121651950052178322509717621)
          ·
            refine ⟨11404870317391717735286027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121651950052178322509717621 11404870317391717735286027)
            ·
              refine ⟨17107305476087576602929041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11404870317391717735286027 17107305476087576602929041)
              ·
                refine ⟨12830479107065682452196781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17107305476087576602929041 12830479107065682452196781)
                ·
                  refine ⟨4811429665149630919573793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12830479107065682452196781 4811429665149630919573793)
                  ·
                    refine ⟨3608572248862223189680345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4811429665149630919573793 3608572248862223189680345)
                    ·
                      refine ⟨2706429186646667392260259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608572248862223189680345 2706429186646667392260259)
                      ·
                        rfl

theorem cell23_5270752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_5270752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270752 prefixEnd_5270752 := by exact prefixLift 5270752
  have htrace : WordTrace (prefixWord ++ tailWord_5270752) baseStart_5270752 baseEnd_5270752 := by
    simpa [prefixWord, tailWord_5270752, baseEnd_5270752] using wordTrace_append hprefix tailTrace_5270752
  have hstable : (prefixWord ++ tailWord_5270752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270752).length < 2 ^ (prefixWord ++ tailWord_5270752).sum := by decide
  have hdescent : baseEnd_5270752 < baseStart_5270752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270765 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5270765 : Nat := 118140960795 + 5270765 * 2 ^ 59
def prefixEnd_5270765 : Nat := 4983230072969 + 3 ^ 40 * 5270765 * 2
def baseEnd_5270765 : Nat := 2706435861895175841397699

theorem tailTrace_5270765 : CollatzResearch.WordTrace tailWord_5270765 prefixEnd_5270765 2706435861895175841397699 := by
  unfold tailWord_5270765
  simp only [CollatzResearch.WordTrace]
  refine ⟨192240592749926054840517749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128160395166617369893678499 192240592749926054840517749)
  ·
    refine ⟨18022555570305567641298539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192240592749926054840517749 18022555570305567641298539)
    ·
      refine ⟨27033833355458351461947809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18022555570305567641298539 27033833355458351461947809)
      ·
        refine ⟨20275375016593763596460857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27033833355458351461947809 20275375016593763596460857)
        ·
          refine ⟨15206531262445322697345643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20275375016593763596460857 15206531262445322697345643)
          ·
            refine ⟨22809796893667984046018465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15206531262445322697345643 22809796893667984046018465)
            ·
              refine ⟨17107347670250988034513849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22809796893667984046018465 17107347670250988034513849)
              ·
                refine ⟨12830510752688241025885387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17107347670250988034513849 12830510752688241025885387)
                ·
                  refine ⟨19245766129032361538828081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12830510752688241025885387 19245766129032361538828081)
                  ·
                    refine ⟨14434324596774271154121061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19245766129032361538828081 14434324596774271154121061)
                    ·
                      refine ⟨2706435861895175841397699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14434324596774271154121061 2706435861895175841397699)
                      ·
                        rfl

theorem cell23_5270765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5270765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270765 prefixEnd_5270765 := by exact prefixLift 5270765
  have htrace : WordTrace (prefixWord ++ tailWord_5270765) baseStart_5270765 baseEnd_5270765 := by
    simpa [prefixWord, tailWord_5270765, baseEnd_5270765] using wordTrace_append hprefix tailTrace_5270765
  have hstable : (prefixWord ++ tailWord_5270765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270765).length < 2 ^ (prefixWord ++ tailWord_5270765).sum := by decide
  have hdescent : baseEnd_5270765 < baseStart_5270765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270786 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_5270786 : Nat := 118140960795 + 5270786 * 2 ^ 59
def prefixEnd_5270786 : Nat := 4983230072969 + 3 ^ 40 * 5270786 * 2
def baseEnd_5270786 : Nat := 2706446644988920259235103

theorem tailTrace_5270786 : CollatzResearch.WordTrace tailWord_5270786 prefixEnd_5270786 2706446644988920259235103 := by
  unfold tailWord_5270786
  simp only [CollatzResearch.WordTrace]
  refine ⟨48060339670712493856758053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128160905788566650284688141 48060339670712493856758053)
  ·
    refine ⟨9011313688258592598142135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48060339670712493856758053 9011313688258592598142135)
    ·
      refine ⟨13516970532387888897213203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9011313688258592598142135 13516970532387888897213203)
      ·
        refine ⟨20275455798581833345819805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13516970532387888897213203 20275455798581833345819805)
        ·
          refine ⟨7603295924468187504682427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20275455798581833345819805 7603295924468187504682427)
          ·
            refine ⟨11404943886702281257023641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7603295924468187504682427 11404943886702281257023641)
            ·
              refine ⟨8553707915026710942767731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11404943886702281257023641 8553707915026710942767731)
              ·
                refine ⟨12830561872540066414151597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8553707915026710942767731 12830561872540066414151597)
                ·
                  refine ⟨4811460702202524905306849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12830561872540066414151597 4811460702202524905306849)
                  ·
                    refine ⟨3608595526651893678980137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4811460702202524905306849 3608595526651893678980137)
                    ·
                      refine ⟨2706446644988920259235103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608595526651893678980137 2706446644988920259235103)
                      ·
                        rfl

theorem cell23_5270786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_5270786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270786 prefixEnd_5270786 := by exact prefixLift 5270786
  have htrace : WordTrace (prefixWord ++ tailWord_5270786) baseStart_5270786 baseEnd_5270786 := by
    simpa [prefixWord, tailWord_5270786, baseEnd_5270786] using wordTrace_append hprefix tailTrace_5270786
  have hstable : (prefixWord ++ tailWord_5270786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270786).length < 2 ^ (prefixWord ++ tailWord_5270786).sum := by decide
  have hdescent : baseEnd_5270786 < baseStart_5270786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270812 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_5270812 : Nat := 118140960795 + 5270812 * 2 ^ 59
def prefixEnd_5270812 : Nat := 4983230072969 + 3 ^ 40 * 5270812 * 2
def baseEnd_5270812 : Nat := 2706459995485937157509983

theorem tailTrace_5270812 : CollatzResearch.WordTrace tailWord_5270812 prefixEnd_5270812 2706459995485937157509983 := by
  unfold tailWord_5270812
  simp only [CollatzResearch.WordTrace]
  refine ⟨96121153490377890933739345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128161537987170521244985793 96121153490377890933739345)
  ·
    refine ⟨72090865117783418200304509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96121153490377890933739345 72090865117783418200304509)
    ·
      refine ⟨27034074419168781825114191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72090865117783418200304509 27034074419168781825114191)
      ·
        refine ⟨40551111628753172737671287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27034074419168781825114191 40551111628753172737671287)
        ·
          refine ⟨60826667443129759106506931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40551111628753172737671287 60826667443129759106506931)
          ·
            refine ⟨91240001164694638659760397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60826667443129759106506931 91240001164694638659760397)
            ·
              refine ⟨34215000436760489497410149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91240001164694638659760397 34215000436760489497410149)
              ·
                refine ⟨6415312581892591780764403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34215000436760489497410149 6415312581892591780764403)
                ·
                  refine ⟨9622968872838887671146605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6415312581892591780764403 9622968872838887671146605)
                  ·
                    refine ⟨3608613327314582876679977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9622968872838887671146605 3608613327314582876679977)
                    ·
                      refine ⟨2706459995485937157509983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608613327314582876679977 2706459995485937157509983)
                      ·
                        rfl

theorem cell23_5270812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_5270812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270812 prefixEnd_5270812 := by exact prefixLift 5270812
  have htrace : WordTrace (prefixWord ++ tailWord_5270812) baseStart_5270812 baseEnd_5270812 := by
    simpa [prefixWord, tailWord_5270812, baseEnd_5270812] using wordTrace_append hprefix tailTrace_5270812
  have hstable : (prefixWord ++ tailWord_5270812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270812).length < 2 ^ (prefixWord ++ tailWord_5270812).sum := by decide
  have hdescent : baseEnd_5270812 < baseStart_5270812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270828 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_5270828 : Nat := 118140960795 + 5270828 * 2 ^ 59
def prefixEnd_5270828 : Nat := 4983230072969 + 3 ^ 40 * 5270828 * 2
def baseEnd_5270828 : Nat := 2706468211176409094909909

theorem tailTrace_5270828 : CollatzResearch.WordTrace tailWord_5270828 prefixEnd_5270828 2706468211176409094909909 := by
  unfold tailWord_5270828
  simp only [CollatzResearch.WordTrace]
  refine ⟨96121445274348908300030569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128161927032465211066707425 96121445274348908300030569)
  ·
    refine ⟨72091083955761681225022927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96121445274348908300030569 72091083955761681225022927)
    ·
      refine ⟨108136625933642521837534391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72091083955761681225022927 108136625933642521837534391)
      ·
        refine ⟨162204938900463782756301587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108136625933642521837534391 162204938900463782756301587)
        ·
          refine ⟨243307408350695674134452381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162204938900463782756301587 243307408350695674134452381)
          ·
            refine ⟨91240278131510877800419643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243307408350695674134452381 91240278131510877800419643)
            ·
              refine ⟨136860417197266316700629465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91240278131510877800419643 136860417197266316700629465)
              ·
                refine ⟨102645312897949737525472099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136860417197266316700629465 102645312897949737525472099)
                ·
                  refine ⟨153967969346924606288208149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102645312897949737525472099 153967969346924606288208149)
                  ·
                    refine ⟨7217248563137090919759757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 153967969346924606288208149 7217248563137090919759757)
                    ·
                      refine ⟨2706468211176409094909909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7217248563137090919759757 2706468211176409094909909)
                      ·
                        rfl

theorem cell23_5270828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_5270828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270828 prefixEnd_5270828 := by exact prefixLift 5270828
  have htrace : WordTrace (prefixWord ++ tailWord_5270828) baseStart_5270828 baseEnd_5270828 := by
    simpa [prefixWord, tailWord_5270828, baseEnd_5270828] using wordTrace_append hprefix tailTrace_5270828
  have hstable : (prefixWord ++ tailWord_5270828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270828).length < 2 ^ (prefixWord ++ tailWord_5270828).sum := by decide
  have hdescent : baseEnd_5270828 < baseStart_5270828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270842 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2]
def baseStart_5270842 : Nat := 118140960795 + 5270842 * 2 ^ 59
def prefixEnd_5270842 : Nat := 4983230072969 + 3 ^ 40 * 5270842 * 2
def baseEnd_5270842 : Nat := 2706475399905572040134845

theorem tailTrace_5270842 : CollatzResearch.WordTrace tailWord_5270842 prefixEnd_5270842 2706475399905572040134845 := by
  unfold tailWord_5270842
  simp only [CollatzResearch.WordTrace]
  refine ⟨48060850292661774247767695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128162267447098064660713853 48060850292661774247767695)
  ·
    refine ⟨72091275438992661371651543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48060850292661774247767695 72091275438992661371651543)
    ·
      refine ⟨108136913158488992057477315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72091275438992661371651543 108136913158488992057477315)
      ·
        refine ⟨162205369737733488086215973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108136913158488992057477315 162205369737733488086215973)
        ·
          refine ⟨30413506825825029016165495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162205369737733488086215973 30413506825825029016165495)
          ·
            refine ⟨45620260238737543524248243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30413506825825029016165495 45620260238737543524248243)
            ·
              refine ⟨68430390358106315286372365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45620260238737543524248243 68430390358106315286372365)
              ·
                refine ⟨25661396384289868232389637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68430390358106315286372365 25661396384289868232389637)
                ·
                  refine ⟨4811511822054350293573057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25661396384289868232389637 4811511822054350293573057)
                  ·
                    refine ⟨3608633866540762720179793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4811511822054350293573057 3608633866540762720179793)
                    ·
                      refine ⟨2706475399905572040134845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608633866540762720179793 2706475399905572040134845)
                      ·
                        rfl

theorem cell23_5270842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_5270842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270842 prefixEnd_5270842 := by exact prefixLift 5270842
  have htrace : WordTrace (prefixWord ++ tailWord_5270842) baseStart_5270842 baseEnd_5270842 := by
    simpa [prefixWord, tailWord_5270842, baseEnd_5270842] using wordTrace_append hprefix tailTrace_5270842
  have hstable : (prefixWord ++ tailWord_5270842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270842).length < 2 ^ (prefixWord ++ tailWord_5270842).sum := by decide
  have hdescent : baseEnd_5270842 < baseStart_5270842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270882 : List Nat := [3, 3, 2, 1, 1, 1, 2, 5, 5]
def baseStart_5270882 : Nat := 118140960795 + 5270882 * 2 ^ 59
def prefixEnd_5270882 : Nat := 4983230072969 + 3 ^ 40 * 5270882 * 2
def baseEnd_5270882 : Nat := 300721771014639098181629

theorem tailTrace_5270882 : CollatzResearch.WordTrace tailWord_5270882 prefixEnd_5270882 300721771014639098181629 := by
  unfold tailWord_5270882
  simp only [CollatzResearch.WordTrace]
  refine ⟨48061215022625545955631725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128163240060334789215017933 48061215022625545955631725)
  ·
    refine ⟨18022955633484579733361897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48061215022625545955631725 18022955633484579733361897)
    ·
      refine ⟨13517216725113434800021423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18022955633484579733361897 13517216725113434800021423)
      ·
        refine ⟨20275825087670152200032135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13517216725113434800021423 20275825087670152200032135)
        ·
          refine ⟨30413737631505228300048203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20275825087670152200032135 30413737631505228300048203)
          ·
            refine ⟨45620606447257842450072305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30413737631505228300048203 45620606447257842450072305)
            ·
              refine ⟨34215454835443381837554229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45620606447257842450072305 34215454835443381837554229)
              ·
                refine ⟨3207698890822817047270709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34215454835443381837554229 3207698890822817047270709)
                ·
                  refine ⟨300721771014639098181629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207698890822817047270709 300721771014639098181629)
                  ·
                    rfl

theorem cell23_5270882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_5270882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270882 prefixEnd_5270882 := by exact prefixLift 5270882
  have htrace : WordTrace (prefixWord ++ tailWord_5270882) baseStart_5270882 baseEnd_5270882 := by
    simpa [prefixWord, tailWord_5270882, baseEnd_5270882] using wordTrace_append hprefix tailTrace_5270882
  have hstable : (prefixWord ++ tailWord_5270882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270882).length < 2 ^ (prefixWord ++ tailWord_5270882).sum := by decide
  have hdescent : baseEnd_5270882 < baseStart_5270882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5270932 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5270932 : Nat := 118140960795 + 5270932 * 2 ^ 59
def prefixEnd_5270932 : Nat := 4983230072969 + 3 ^ 40 * 5270932 * 2
def baseEnd_5270932 : Nat := 2706521613164476688009431

theorem tailTrace_5270932 : CollatzResearch.WordTrace tailWord_5270932 prefixEnd_5270932 2706521613164476688009431 := by
  unfold tailWord_5270932
  simp only [CollatzResearch.WordTrace]
  refine ⟨96123341870160521180923525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128164455826880694907898033 96123341870160521180923525)
  ·
    refine ⟨18023126600655097721423161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96123341870160521180923525 18023126600655097721423161)
    ·
      refine ⟨13517344950491323291067371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18023126600655097721423161 13517344950491323291067371)
      ·
        refine ⟨20276017425736984936601057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13517344950491323291067371 20276017425736984936601057)
        ·
          refine ⟨15207013069302738702450793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20276017425736984936601057 15207013069302738702450793)
          ·
            refine ⟨11405259801977054026838095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15207013069302738702450793 11405259801977054026838095)
            ·
              refine ⟨17107889702965581040257143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11405259801977054026838095 17107889702965581040257143)
              ·
                refine ⟨25661834554448371560385715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17107889702965581040257143 25661834554448371560385715)
                ·
                  refine ⟨38492751831672557340578573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25661834554448371560385715 38492751831672557340578573)
                  ·
                    refine ⟨14434781936877209002716965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38492751831672557340578573 14434781936877209002716965)
                    ·
                      refine ⟨2706521613164476688009431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14434781936877209002716965 2706521613164476688009431)
                      ·
                        rfl

theorem cell23_5270932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5270932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5270932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5270932 prefixEnd_5270932 := by exact prefixLift 5270932
  have htrace : WordTrace (prefixWord ++ tailWord_5270932) baseStart_5270932 baseEnd_5270932 := by
    simpa [prefixWord, tailWord_5270932, baseEnd_5270932] using wordTrace_append hprefix tailTrace_5270932
  have hstable : (prefixWord ++ tailWord_5270932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5270932).length < 2 ^ (prefixWord ++ tailWord_5270932).sum := by decide
  have hdescent : baseEnd_5270932 < baseStart_5270932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5270932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271002 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_5271002 : Nat := 118140960795 + 5271002 * 2 ^ 59
def prefixEnd_5271002 : Nat := 4983230072969 + 3 ^ 40 * 5271002 * 2
def baseEnd_5271002 : Nat := 902185852270097138044703

theorem tailTrace_5271002 : CollatzResearch.WordTrace tailWord_5271002 prefixEnd_5271002 902185852270097138044703 := by
  unfold tailWord_5271002
  simp only [CollatzResearch.WordTrace]
  refine ⟨48062309212516861079223815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128166157900044962877930173 48062309212516861079223815)
  ·
    refine ⟨72093463818775291618835723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48062309212516861079223815 72093463818775291618835723)
    ·
      refine ⟨108140195728162937428253585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72093463818775291618835723 108140195728162937428253585)
      ·
        refine ⟨81105146796122203071190189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108140195728162937428253585 81105146796122203071190189)
        ·
          refine ⟨30414430048545826151696321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81105146796122203071190189 30414430048545826151696321)
          ·
            refine ⟨22810822536409369613772241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30414430048545826151696321 22810822536409369613772241)
            ·
              refine ⟨17108116902307027210329181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22810822536409369613772241 17108116902307027210329181)
              ·
                refine ⟨6415543838365135203873443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17108116902307027210329181 6415543838365135203873443)
                ·
                  refine ⟨9623315757547702805810165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6415543838365135203873443 9623315757547702805810165)
                  ·
                    refine ⟨902185852270097138044703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9623315757547702805810165 902185852270097138044703)
                    ·
                      rfl

theorem cell23_5271002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_5271002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271002 prefixEnd_5271002 := by exact prefixLift 5271002
  have htrace : WordTrace (prefixWord ++ tailWord_5271002) baseStart_5271002 baseEnd_5271002 := by
    simpa [prefixWord, tailWord_5271002, baseEnd_5271002] using wordTrace_append hprefix tailTrace_5271002
  have hstable : (prefixWord ++ tailWord_5271002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271002).length < 2 ^ (prefixWord ++ tailWord_5271002).sum := by decide
  have hdescent : baseEnd_5271002 < baseStart_5271002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271009 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_5271009 : Nat := 118140960795 + 5271009 * 2 ^ 59
def prefixEnd_5271009 : Nat := 4983230072969 + 3 ^ 40 * 5271009 * 2
def baseEnd_5271009 : Nat := 2706561151174872886746577

theorem tailTrace_5271009 : CollatzResearch.WordTrace tailWord_5271009 prefixEnd_5271009 2706561151174872886746577 := by
  unfold tailWord_5271009
  simp only [CollatzResearch.WordTrace]
  refine ⟨192249492161042084512400081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128166328107361389674933387 192249492161042084512400081)
  ·
    refine ⟨144187119120781563384300061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192249492161042084512400081 144187119120781563384300061)
    ·
      refine ⟨54070169670293086269112523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144187119120781563384300061 54070169670293086269112523)
      ·
        refine ⟨81105254505439629403668785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54070169670293086269112523 81105254505439629403668785)
        ·
          refine ⟨60828940879079722052751589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81105254505439629403668785 60828940879079722052751589)
          ·
            refine ⟨11405426414827447884890923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60828940879079722052751589 11405426414827447884890923)
            ·
              refine ⟨17108139622241171827336385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11405426414827447884890923 17108139622241171827336385)
              ·
                refine ⟨12831104716680878870502289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17108139622241171827336385 12831104716680878870502289)
                ·
                  refine ⟨9623328537510659152876717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12831104716680878870502289 9623328537510659152876717)
                  ·
                    refine ⟨3608748201566497182328769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9623328537510659152876717 3608748201566497182328769)
                    ·
                      refine ⟨2706561151174872886746577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608748201566497182328769 2706561151174872886746577)
                      ·
                        rfl

theorem cell23_5271009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_5271009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271009 prefixEnd_5271009 := by exact prefixLift 5271009
  have htrace : WordTrace (prefixWord ++ tailWord_5271009) baseStart_5271009 baseEnd_5271009 := by
    simpa [prefixWord, tailWord_5271009, baseEnd_5271009] using wordTrace_append hprefix tailTrace_5271009
  have hstable : (prefixWord ++ tailWord_5271009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271009).length < 2 ^ (prefixWord ++ tailWord_5271009).sum := by decide
  have hdescent : baseEnd_5271009 < baseStart_5271009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271022 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_5271022 : Nat := 118140960795 + 5271022 * 2 ^ 59
def prefixEnd_5271022 : Nat := 4983230072969 + 3 ^ 40 * 5271022 * 2
def baseEnd_5271022 : Nat := 2706567826423381335884017

theorem tailTrace_5271022 : CollatzResearch.WordTrace tailWord_5271022 prefixEnd_5271022 2706567826423381335884017 := by
  unfold tailWord_5271022
  simp only [CollatzResearch.WordTrace]
  refine ⟨24031245788749373466577915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128166644206663325155082213 24031245788749373466577915)
  ·
    refine ⟨36046868683124060199866873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24031245788749373466577915 36046868683124060199866873)
    ·
      refine ⟨27035151512343045149900155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36046868683124060199866873 27035151512343045149900155)
      ·
        refine ⟨40552727268514567724850233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27035151512343045149900155 40552727268514567724850233)
        ·
          refine ⟨30414545451385925793637675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40552727268514567724850233 30414545451385925793637675)
          ·
            refine ⟨45621818177078888690456513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30414545451385925793637675 45621818177078888690456513)
            ·
              refine ⟨34216363632809166517842385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45621818177078888690456513 34216363632809166517842385)
              ·
                refine ⟨25662272724606874888381789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34216363632809166517842385 25662272724606874888381789)
                ·
                  refine ⟨9623352271727578083143171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25662272724606874888381789 9623352271727578083143171)
                  ·
                    refine ⟨14435028407591367124714757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9623352271727578083143171 14435028407591367124714757)
                    ·
                      refine ⟨2706567826423381335884017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14435028407591367124714757 2706567826423381335884017)
                      ·
                        rfl

theorem cell23_5271022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_5271022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271022 prefixEnd_5271022 := by exact prefixLift 5271022
  have htrace : WordTrace (prefixWord ++ tailWord_5271022) baseStart_5271022 baseEnd_5271022 := by
    simpa [prefixWord, tailWord_5271022, baseEnd_5271022] using wordTrace_append hprefix tailTrace_5271022
  have hstable : (prefixWord ++ tailWord_5271022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271022).length < 2 ^ (prefixWord ++ tailWord_5271022).sum := by decide
  have hdescent : baseEnd_5271022 < baseStart_5271022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271055 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 3]
def baseStart_5271055 : Nat := 118140960795 + 5271055 * 2 ^ 59
def prefixEnd_5271055 : Nat := 4983230072969 + 3 ^ 40 * 5271055 * 2
def baseEnd_5271055 : Nat := 2706584771284979706771365

theorem tailTrace_5271055 : CollatzResearch.WordTrace tailWord_5271055 prefixEnd_5271055 2706584771284979706771365 := by
  unfold tailWord_5271055
  simp only [CollatzResearch.WordTrace]
  refine ⟨192251169918875434368574619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128167446612583622912383079 192251169918875434368574619)
  ·
    refine ⟨288376754878313151552861929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192251169918875434368574619 288376754878313151552861929)
    ·
      refine ⟨216282566158734863664646447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288376754878313151552861929 216282566158734863664646447)
      ·
        refine ⟨324423849238102295496969671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216282566158734863664646447 324423849238102295496969671)
        ·
          refine ⟨486635773857153443245454507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324423849238102295496969671 486635773857153443245454507)
          ·
            refine ⟨729953660785730164868181761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486635773857153443245454507 729953660785730164868181761)
            ·
              refine ⟨547465245589297623651136321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729953660785730164868181761 547465245589297623651136321)
              ·
                refine ⟨410598934191973217738352241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547465245589297623651136321 410598934191973217738352241)
                ·
                  refine ⟨307949200643979913303764181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410598934191973217738352241 307949200643979913303764181)
                  ·
                    refine ⟨7217559390093279218056973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 307949200643979913303764181 7217559390093279218056973)
                    ·
                      refine ⟨2706584771284979706771365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7217559390093279218056973 2706584771284979706771365)
                      ·
                        rfl

theorem cell23_5271055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_5271055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271055 prefixEnd_5271055 := by exact prefixLift 5271055
  have htrace : WordTrace (prefixWord ++ tailWord_5271055) baseStart_5271055 baseEnd_5271055 := by
    simpa [prefixWord, tailWord_5271055, baseEnd_5271055] using wordTrace_append hprefix tailTrace_5271055
  have hstable : (prefixWord ++ tailWord_5271055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271055).length < 2 ^ (prefixWord ++ tailWord_5271055).sum := by decide
  have hdescent : baseEnd_5271055 < baseStart_5271055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271073 : List Nat := [1, 2, 3, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_5271073 : Nat := 118140960795 + 5271073 * 2 ^ 59
def prefixEnd_5271073 : Nat := 4983230072969 + 3 ^ 40 * 5271073 * 2
def baseEnd_5271073 : Nat := 2706594013936760636346283

theorem tailTrace_5271073 : CollatzResearch.WordTrace tailWord_5271073 prefixEnd_5271073 2706594013936760636346283 := by
  unfold tailWord_5271073
  simp only [CollatzResearch.WordTrace]
  refine ⟨192251826432810223442729873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128167884288540148961819915 192251826432810223442729873)
  ·
    refine ⟨144188869824607667582047405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192251826432810223442729873 144188869824607667582047405)
    ·
      refine ⟨54070826184227875343267777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144188869824607667582047405 54070826184227875343267777)
      ·
        refine ⟨40553119638170906507450833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54070826184227875343267777 40553119638170906507450833)
        ·
          refine ⟨30414839728628179880588125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40553119638170906507450833 30414839728628179880588125)
          ·
            refine ⟨11405564898235567455220547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30414839728628179880588125 11405564898235567455220547)
            ·
              refine ⟨17108347347353351182830821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11405564898235567455220547 17108347347353351182830821)
              ·
                refine ⟨3207815127628753346780779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17108347347353351182830821 3207815127628753346780779)
                ·
                  refine ⟨4811722691443130020171169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207815127628753346780779 4811722691443130020171169)
                  ·
                    refine ⟨3608792018582347515128377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4811722691443130020171169 3608792018582347515128377)
                    ·
                      refine ⟨2706594013936760636346283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608792018582347515128377 2706594013936760636346283)
                      ·
                        rfl

theorem cell23_5271073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_5271073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271073 prefixEnd_5271073 := by exact prefixLift 5271073
  have htrace : WordTrace (prefixWord ++ tailWord_5271073) baseStart_5271073 baseEnd_5271073 := by
    simpa [prefixWord, tailWord_5271073, baseEnd_5271073] using wordTrace_append hprefix tailTrace_5271073
  have hstable : (prefixWord ++ tailWord_5271073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271073).length < 2 ^ (prefixWord ++ tailWord_5271073).sum := by decide
  have hdescent : baseEnd_5271073 < baseStart_5271073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271115 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 5]
def baseStart_5271115 : Nat := 118140960795 + 5271115 * 2 ^ 59
def prefixEnd_5271115 : Nat := 4983230072969 + 3 ^ 40 * 5271115 * 2
def baseEnd_5271115 : Nat := 2706615580124249472021089

theorem tailTrace_5271115 : CollatzResearch.WordTrace tailWord_5271115 prefixEnd_5271115 2706615580124249472021089 := by
  unfold tailWord_5271115
  simp only [CollatzResearch.WordTrace]
  refine ⟨192253358298658064615758799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128168905532438709743839199 192253358298658064615758799)
  ·
    refine ⟨288380037447987096923638199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192253358298658064615758799 288380037447987096923638199)
    ·
      refine ⟨432570056171980645385457299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288380037447987096923638199 432570056171980645385457299)
      ·
        refine ⟨648855084257970968078185949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432570056171980645385457299 648855084257970968078185949)
        ·
          refine ⟨243320656596739113029319731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 648855084257970968078185949 243320656596739113029319731)
          ·
            refine ⟨364980984895108669543979597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243320656596739113029319731 364980984895108669543979597)
            ·
              refine ⟨136867869335665751078992349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364980984895108669543979597 136867869335665751078992349)
              ·
                refine ⟨51325451000874656654622131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136867869335665751078992349 51325451000874656654622131)
                ·
                  refine ⟨76988176501311984981933197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51325451000874656654622131 76988176501311984981933197)
                  ·
                    refine ⟨28870566187991994368224949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76988176501311984981933197 28870566187991994368224949)
                    ·
                      refine ⟨2706615580124249472021089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28870566187991994368224949 2706615580124249472021089)
                      ·
                        rfl

theorem cell23_5271115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_5271115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271115 prefixEnd_5271115 := by exact prefixLift 5271115
  have htrace : WordTrace (prefixWord ++ tailWord_5271115) baseStart_5271115 baseEnd_5271115 := by
    simpa [prefixWord, tailWord_5271115, baseEnd_5271115] using wordTrace_append hprefix tailTrace_5271115
  have hstable : (prefixWord ++ tailWord_5271115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271115).length < 2 ^ (prefixWord ++ tailWord_5271115).sum := by decide
  have hdescent : baseEnd_5271115 < baseStart_5271115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271116 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 1, 3, 2]
def baseStart_5271116 : Nat := 118140960795 + 5271116 * 2 ^ 59
def prefixEnd_5271116 : Nat := 4983230072969 + 3 ^ 40 * 5271116 * 2
def baseEnd_5271116 : Nat := 2706616093604903968108585

theorem tailTrace_5271116 : CollatzResearch.WordTrace tailWord_5271116 prefixEnd_5271116 2706616093604903968108585 := by
  unfold tailWord_5271116
  simp only [CollatzResearch.WordTrace]
  refine ⟨96126697385827220893272601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128168929847769627857696801 96126697385827220893272601)
  ·
    refine ⟨72095023039370415669954451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96126697385827220893272601 72095023039370415669954451)
    ·
      refine ⟨108142534559055623504931677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72095023039370415669954451 108142534559055623504931677)
      ·
        refine ⟨40553450459645858814349379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108142534559055623504931677 40553450459645858814349379)
        ·
          refine ⟨60830175689468788221524069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40553450459645858814349379 60830175689468788221524069)
          ·
            refine ⟨11405657941775397791535763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60830175689468788221524069 11405657941775397791535763)
            ·
              refine ⟨17108486912663096687303645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11405657941775397791535763 17108486912663096687303645)
              ·
                refine ⟨6415682592248661257738867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17108486912663096687303645 6415682592248661257738867)
                ·
                  refine ⟨9623523888372991886608301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6415682592248661257738867 9623523888372991886608301)
                  ·
                    refine ⟨3608821458139871957478113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9623523888372991886608301 3608821458139871957478113)
                    ·
                      refine ⟨2706616093604903968108585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608821458139871957478113 2706616093604903968108585)
                      ·
                        rfl

theorem cell23_5271116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_5271116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271116 prefixEnd_5271116 := by exact prefixLift 5271116
  have htrace : WordTrace (prefixWord ++ tailWord_5271116) baseStart_5271116 baseEnd_5271116 := by
    simpa [prefixWord, tailWord_5271116, baseEnd_5271116] using wordTrace_append hprefix tailTrace_5271116
  have hstable : (prefixWord ++ tailWord_5271116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271116).length < 2 ^ (prefixWord ++ tailWord_5271116).sum := by decide
  have hdescent : baseEnd_5271116 < baseStart_5271116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271122 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_5271122 : Nat := 118140960795 + 5271122 * 2 ^ 59
def prefixEnd_5271122 : Nat := 4983230072969 + 3 ^ 40 * 5271122 * 2
def baseEnd_5271122 : Nat := 902206391496276981544519

theorem tailTrace_5271122 : CollatzResearch.WordTrace tailWord_5271122 prefixEnd_5271122 902206391496276981544519 := by
  unfold tailWord_5271122
  simp only [CollatzResearch.WordTrace]
  refine ⟨48063403402408176202815905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128169075739755136540842413 48063403402408176202815905)
  ·
    refine ⟨36047552551806132152111929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48063403402408176202815905 36047552551806132152111929)
    ·
      refine ⟨27035664413854599114083947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36047552551806132152111929 27035664413854599114083947)
      ·
        refine ⟨40553496620781898671125921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27035664413854599114083947 40553496620781898671125921)
        ·
          refine ⟨30415122465586424003344441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40553496620781898671125921 30415122465586424003344441)
          ·
            refine ⟨22811341849189818002508331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30415122465586424003344441 22811341849189818002508331)
            ·
              refine ⟨34217012773784727003762497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22811341849189818002508331 34217012773784727003762497)
              ·
                refine ⟨25662759580338545252821873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34217012773784727003762497 25662759580338545252821873)
                ·
                  refine ⟨19247069685253908939616405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25662759580338545252821873 19247069685253908939616405)
                  ·
                    refine ⟨902206391496276981544519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19247069685253908939616405 902206391496276981544519)
                    ·
                      rfl

theorem cell23_5271122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_5271122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271122 prefixEnd_5271122 := by exact prefixLift 5271122
  have htrace : WordTrace (prefixWord ++ tailWord_5271122) baseStart_5271122 baseEnd_5271122 := by
    simpa [prefixWord, tailWord_5271122, baseEnd_5271122] using wordTrace_append hprefix tailTrace_5271122
  have hstable : (prefixWord ++ tailWord_5271122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271122).length < 2 ^ (prefixWord ++ tailWord_5271122).sum := by decide
  have hdescent : baseEnd_5271122 < baseStart_5271122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271146 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_5271146 : Nat := 118140960795 + 5271146 * 2 ^ 59
def prefixEnd_5271146 : Nat := 4983230072969 + 3 ^ 40 * 5271146 * 2
def baseEnd_5271146 : Nat := 2706631498024538850733447

theorem tailTrace_5271146 : CollatzResearch.WordTrace tailWord_5271146 prefixEnd_5271146 2706631498024538850733447 := by
  unfold tailWord_5271146
  simp only [CollatzResearch.WordTrace]
  refine ⟨48063622240386439227534323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128169659307697171273424861 48063622240386439227534323)
  ·
    refine ⟨72095433360579658841301485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48063622240386439227534323 72095433360579658841301485)
    ·
      refine ⟨27035787510217372065488057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72095433360579658841301485 27035787510217372065488057)
      ·
        refine ⟨20276840632663029049116043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27035787510217372065488057 20276840632663029049116043)
        ·
          refine ⟨30415260948994543573674065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20276840632663029049116043 30415260948994543573674065)
          ·
            refine ⟨22811445711745907680255549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30415260948994543573674065 22811445711745907680255549)
            ·
              refine ⟨8554292141904715380095831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22811445711745907680255549 8554292141904715380095831)
              ·
                refine ⟨12831438212857073070143747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8554292141904715380095831 12831438212857073070143747)
                ·
                  refine ⟨19247157319285609605215621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12831438212857073070143747 19247157319285609605215621)
                  ·
                    refine ⟨3608841997366051800977929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19247157319285609605215621 3608841997366051800977929)
                    ·
                      refine ⟨2706631498024538850733447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608841997366051800977929 2706631498024538850733447)
                      ·
                        rfl

theorem cell23_5271146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_5271146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271146 prefixEnd_5271146 := by exact prefixLift 5271146
  have htrace : WordTrace (prefixWord ++ tailWord_5271146) baseStart_5271146 baseEnd_5271146 := by
    simpa [prefixWord, tailWord_5271146, baseEnd_5271146] using wordTrace_append hprefix tailTrace_5271146
  have hstable : (prefixWord ++ tailWord_5271146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271146).length < 2 ^ (prefixWord ++ tailWord_5271146).sum := by decide
  have hdescent : baseEnd_5271146 < baseStart_5271146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271152 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 7]
def baseStart_5271152 : Nat := 118140960795 + 5271152 * 2 ^ 59
def prefixEnd_5271152 : Nat := 4983230072969 + 3 ^ 40 * 5271152 * 2
def baseEnd_5271152 : Nat := 300737175434273980806491

theorem tailTrace_5271152 : CollatzResearch.WordTrace tailWord_5271152 prefixEnd_5271152 300737175434273980806491 := by
  unfold tailWord_5271152
  simp only [CollatzResearch.WordTrace]
  refine ⟨96127353899762009967427855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128169805199682679956570473 96127353899762009967427855)
  ·
    refine ⟨144191030849643014951141783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96127353899762009967427855 144191030849643014951141783)
    ·
      refine ⟨216286546274464522426712675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144191030849643014951141783 216286546274464522426712675)
      ·
        refine ⟨324429819411696783640069013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216286546274464522426712675 324429819411696783640069013)
        ·
          refine ⟨15207647784923286733128235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 324429819411696783640069013 15207647784923286733128235)
          ·
            refine ⟨22811471677384930099692353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15207647784923286733128235 22811471677384930099692353)
            ·
              refine ⟨17108603758038697574769265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22811471677384930099692353 17108603758038697574769265)
              ·
                refine ⟨12831452818529023181076949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17108603758038697574769265 12831452818529023181076949)
                ·
                  refine ⟨300737175434273980806491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12831452818529023181076949 300737175434273980806491)
                  ·
                    rfl

theorem cell23_5271152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 7].length) (baseStart_5271152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271152 prefixEnd_5271152 := by exact prefixLift 5271152
  have htrace : WordTrace (prefixWord ++ tailWord_5271152) baseStart_5271152 baseEnd_5271152 := by
    simpa [prefixWord, tailWord_5271152, baseEnd_5271152] using wordTrace_append hprefix tailTrace_5271152
  have hstable : (prefixWord ++ tailWord_5271152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271152).length < 2 ^ (prefixWord ++ tailWord_5271152).sum := by decide
  have hdescent : baseEnd_5271152 < baseStart_5271152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271155 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 6]
def baseStart_5271155 : Nat := 118140960795 + 5271155 * 2 ^ 59
def prefixEnd_5271155 : Nat := 4983230072969 + 3 ^ 40 * 5271155 * 2
def baseEnd_5271155 : Nat := 2706636119350429315520905

theorem tailTrace_5271155 : CollatzResearch.WordTrace tailWord_5271155 prefixEnd_5271155 2706636119350429315520905 := by
  unfold tailWord_5271155
  simp only [CollatzResearch.WordTrace]
  refine ⟨192254817218513151447214919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128169878145675434298143279 192254817218513151447214919)
  ·
    refine ⟨288382225827769727170822379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192254817218513151447214919 288382225827769727170822379)
    ·
      refine ⟨432573338741654590756233569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288382225827769727170822379 432573338741654590756233569)
      ·
        refine ⟨324430004056240943067175177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432573338741654590756233569 324430004056240943067175177)
        ·
          refine ⟨243322503042180707300381383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324430004056240943067175177 243322503042180707300381383)
          ·
            refine ⟨364983754563271060950572075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243322503042180707300381383 364983754563271060950572075)
            ·
              refine ⟨547475631844906591425858113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364983754563271060950572075 547475631844906591425858113)
              ·
                refine ⟨410606723883679943569393585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547475631844906591425858113 410606723883679943569393585)
                ·
                  refine ⟨307955042912759957677045189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410606723883679943569393585 307955042912759957677045189)
                  ·
                    refine ⟨57741570546142492064445973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307955042912759957677045189 57741570546142492064445973)
                    ·
                      refine ⟨2706636119350429315520905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57741570546142492064445973 2706636119350429315520905)
                      ·
                        rfl

theorem cell23_5271155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_5271155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271155 prefixEnd_5271155 := by exact prefixLift 5271155
  have htrace : WordTrace (prefixWord ++ tailWord_5271155) baseStart_5271155 baseEnd_5271155 := by
    simpa [prefixWord, tailWord_5271155, baseEnd_5271155] using wordTrace_append hprefix tailTrace_5271155
  have hstable : (prefixWord ++ tailWord_5271155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271155).length < 2 ^ (prefixWord ++ tailWord_5271155).sum := by decide
  have hdescent : baseEnd_5271155 < baseStart_5271155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271162 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_5271162 : Nat := 118140960795 + 5271162 * 2 ^ 59
def prefixEnd_5271162 : Nat := 4983230072969 + 3 ^ 40 * 5271162 * 2
def baseEnd_5271162 : Nat := 2706639713715010788133373

theorem tailTrace_5271162 : CollatzResearch.WordTrace tailWord_5271162 prefixEnd_5271162 2706639713715010788133373 := by
  unfold tailWord_5271162
  simp only [CollatzResearch.WordTrace]
  refine ⟨48063768132371947910679935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128170048352991861095146493 48063768132371947910679935)
  ·
    refine ⟨72095652198557921866019903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48063768132371947910679935 72095652198557921866019903)
    ·
      refine ⟨108143478297836882799029855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72095652198557921866019903 108143478297836882799029855)
      ·
        refine ⟨162215217446755324198544783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108143478297836882799029855 162215217446755324198544783)
        ·
          refine ⟨243322826170132986297817175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162215217446755324198544783 243322826170132986297817175)
          ·
            refine ⟨364984239255199479446725763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243322826170132986297817175 364984239255199479446725763)
            ·
              refine ⟨547476358882799219170088645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364984239255199479446725763 547476358882799219170088645)
              ·
                refine ⟨102651817290524853594391621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547476358882799219170088645 102651817290524853594391621)
                ·
                  refine ⟨19247215741973410048948429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102651817290524853594391621 19247215741973410048948429)
                  ·
                    refine ⟨7217705903240028768355661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19247215741973410048948429 7217705903240028768355661)
                    ·
                      refine ⟨2706639713715010788133373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7217705903240028768355661 2706639713715010788133373)
                      ·
                        rfl

theorem cell23_5271162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_5271162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271162 prefixEnd_5271162 := by exact prefixLift 5271162
  have htrace : WordTrace (prefixWord ++ tailWord_5271162) baseStart_5271162 baseEnd_5271162 := by
    simpa [prefixWord, tailWord_5271162, baseEnd_5271162] using wordTrace_append hprefix tailTrace_5271162
  have hstable : (prefixWord ++ tailWord_5271162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271162).length < 2 ^ (prefixWord ++ tailWord_5271162).sum := by decide
  have hdescent : baseEnd_5271162 < baseStart_5271162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271186 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 7]
def baseStart_5271186 : Nat := 118140960795 + 5271186 * 2 ^ 59
def prefixEnd_5271186 : Nat := 4983230072969 + 3 ^ 40 * 5271186 * 2
def baseEnd_5271186 : Nat := 300739115250079854914807

theorem tailTrace_5271186 : CollatzResearch.WordTrace tailWord_5271186 prefixEnd_5271186 300739115250079854914807 := by
  unfold tailWord_5271186
  simp only [CollatzResearch.WordTrace]
  refine ⟨48063986970350210935398353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128170631920933895827728941 48063986970350210935398353)
  ·
    refine ⟨36047990227762658201548765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48063986970350210935398353 36047990227762658201548765)
    ·
      refine ⟨13517996335410996825580787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36047990227762658201548765 13517996335410996825580787)
      ·
        refine ⟨20276994503116495238371181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13517996335410996825580787 20276994503116495238371181)
        ·
          refine ⟨7603872938668685714389193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20276994503116495238371181 7603872938668685714389193)
          ·
            refine ⟨5702904704001514285791895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7603872938668685714389193 5702904704001514285791895)
            ·
              refine ⟨8554357056002271428687843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702904704001514285791895 8554357056002271428687843)
              ·
                refine ⟨12831535584003407143031765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8554357056002271428687843 12831535584003407143031765)
                ·
                  refine ⟨300739115250079854914807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12831535584003407143031765 300739115250079854914807)
                  ·
                    rfl

theorem cell23_5271186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_5271186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271186 prefixEnd_5271186 := by exact prefixLift 5271186
  have htrace : WordTrace (prefixWord ++ tailWord_5271186) baseStart_5271186 baseEnd_5271186 := by
    simpa [prefixWord, tailWord_5271186, baseEnd_5271186] using wordTrace_append hprefix tailTrace_5271186
  have hstable : (prefixWord ++ tailWord_5271186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271186).length < 2 ^ (prefixWord ++ tailWord_5271186).sum := by decide
  have hdescent : baseEnd_5271186 < baseStart_5271186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271192 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5271192 : Nat := 118140960795 + 5271192 * 2 ^ 59
def prefixEnd_5271192 : Nat := 4983230072969 + 3 ^ 40 * 5271192 * 2
def baseEnd_5271192 : Nat := 2706655118134645670758235

theorem tailTrace_5271192 : CollatzResearch.WordTrace tailWord_5271192 prefixEnd_5271192 2706655118134645670758235 := by
  unfold tailWord_5271192
  simp only [CollatzResearch.WordTrace]
  refine ⟨96128083359689553383155915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128170777812919404510874553 96128083359689553383155915)
  ·
    refine ⟨144192125039534330074733873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96128083359689553383155915 144192125039534330074733873)
    ·
      refine ⟨108144093779650747556050405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144192125039534330074733873 108144093779650747556050405)
      ·
        refine ⟨20277017583684515166759451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108144093779650747556050405 20277017583684515166759451)
        ·
          refine ⟨30415526375526772750139177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20277017583684515166759451 30415526375526772750139177)
          ·
            refine ⟨22811644781645079562604383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30415526375526772750139177 22811644781645079562604383)
            ·
              refine ⟨34217467172467619343906575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22811644781645079562604383 34217467172467619343906575)
              ·
                refine ⟨51326200758701429015859863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34217467172467619343906575 51326200758701429015859863)
                ·
                  refine ⟨76989301138052143523789795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51326200758701429015859863 76989301138052143523789795)
                  ·
                    refine ⟨115483951707078215285684693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76989301138052143523789795 115483951707078215285684693)
                    ·
                      refine ⟨2706655118134645670758235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115483951707078215285684693 2706655118134645670758235)
                      ·
                        rfl

theorem cell23_5271192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5271192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271192 prefixEnd_5271192 := by exact prefixLift 5271192
  have htrace : WordTrace (prefixWord ++ tailWord_5271192) baseStart_5271192 baseEnd_5271192 := by
    simpa [prefixWord, tailWord_5271192, baseEnd_5271192] using wordTrace_append hprefix tailTrace_5271192
  have hstable : (prefixWord ++ tailWord_5271192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271192).length < 2 ^ (prefixWord ++ tailWord_5271192).sum := by decide
  have hdescent : baseEnd_5271192 < baseStart_5271192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271219 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 4]
def baseStart_5271219 : Nat := 118140960795 + 5271219 * 2 ^ 59
def prefixEnd_5271219 : Nat := 4983230072969 + 3 ^ 40 * 5271219 * 2
def baseEnd_5271219 : Nat := 2706668982112317065120611

theorem tailTrace_5271219 : CollatzResearch.WordTrace tailWord_5271219 prefixEnd_5271219 2706668982112317065120611 := by
  unfold tailWord_5271219
  simp only [CollatzResearch.WordTrace]
  refine ⟨192257151490281290377544711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128171434326854193585029807 192257151490281290377544711)
  ·
    refine ⟨288385727235421935566317067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192257151490281290377544711 288385727235421935566317067)
    ·
      refine ⟨432578590853132903349475601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288385727235421935566317067 432578590853132903349475601)
      ·
        refine ⟨324433943139849677512106701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432578590853132903349475601 324433943139849677512106701)
        ·
          refine ⟨121662728677443629067040013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324433943139849677512106701 121662728677443629067040013)
          ·
            refine ⟨45623523254041360900140005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121662728677443629067040013 45623523254041360900140005)
            ·
              refine ⟨8554410610132755168776251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45623523254041360900140005 8554410610132755168776251)
              ·
                refine ⟨12831615915199132753164377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8554410610132755168776251 12831615915199132753164377)
                ·
                  refine ⟨9623711936399349564873283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12831615915199132753164377 9623711936399349564873283)
                  ·
                    refine ⟨14435567904599024347309925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9623711936399349564873283 14435567904599024347309925)
                    ·
                      refine ⟨2706668982112317065120611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14435567904599024347309925 2706668982112317065120611)
                      ·
                        rfl

theorem cell23_5271219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_5271219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271219 prefixEnd_5271219 := by exact prefixLift 5271219
  have htrace : WordTrace (prefixWord ++ tailWord_5271219) baseStart_5271219 baseEnd_5271219 := by
    simpa [prefixWord, tailWord_5271219, baseEnd_5271219] using wordTrace_append hprefix tailTrace_5271219
  have hstable : (prefixWord ++ tailWord_5271219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271219).length < 2 ^ (prefixWord ++ tailWord_5271219).sum := by decide
  have hdescent : baseEnd_5271219 < baseStart_5271219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271232 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_5271232 : Nat := 118140960795 + 5271232 * 2 ^ 59
def prefixEnd_5271232 : Nat := 4983230072969 + 3 ^ 40 * 5271232 * 2
def baseEnd_5271232 : Nat := 2706675657360825514258051

theorem tailTrace_5271232 : CollatzResearch.WordTrace tailWord_5271232 prefixEnd_5271232 2706675657360825514258051 := by
  unfold tailWord_5271232
  simp only [CollatzResearch.WordTrace]
  refine ⟨96128812819617096798883975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128171750426156129065178633 96128812819617096798883975)
  ·
    refine ⟨144193219229425645198325963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96128812819617096798883975 144193219229425645198325963)
    ·
      refine ⟨216289828844138467797488945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144193219229425645198325963 216289828844138467797488945)
      ·
        refine ⟨162217371633103850848116709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216289828844138467797488945 162217371633103850848116709)
        ·
          refine ⟨30415757181206972034021883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162217371633103850848116709 30415757181206972034021883)
          ·
            refine ⟨45623635771810458051032825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30415757181206972034021883 45623635771810458051032825)
            ·
              refine ⟨34217726828857843538274619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45623635771810458051032825 34217726828857843538274619)
              ·
                refine ⟨51326590243286765307411929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34217726828857843538274619 51326590243286765307411929)
                ·
                  refine ⟨38494942682465073980558947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51326590243286765307411929 38494942682465073980558947)
                  ·
                    refine ⟨57742414023697610970838421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38494942682465073980558947 57742414023697610970838421)
                    ·
                      refine ⟨2706675657360825514258051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57742414023697610970838421 2706675657360825514258051)
                      ·
                        rfl

theorem cell23_5271232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_5271232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271232 prefixEnd_5271232 := by exact prefixLift 5271232
  have htrace : WordTrace (prefixWord ++ tailWord_5271232) baseStart_5271232 baseEnd_5271232 := by
    simpa [prefixWord, tailWord_5271232, baseEnd_5271232] using wordTrace_append hprefix tailTrace_5271232
  have hstable : (prefixWord ++ tailWord_5271232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271232).length < 2 ^ (prefixWord ++ tailWord_5271232).sum := by decide
  have hdescent : baseEnd_5271232 < baseStart_5271232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271236 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_5271236 : Nat := 118140960795 + 5271236 * 2 ^ 59
def prefixEnd_5271236 : Nat := 4983230072969 + 3 ^ 40 * 5271236 * 2
def baseEnd_5271236 : Nat := 2706677711283443498608033

theorem tailTrace_5271236 : CollatzResearch.WordTrace tailWord_5271236 prefixEnd_5271236 2706677711283443498608033 := by
  unfold tailWord_5271236
  simp only [CollatzResearch.WordTrace]
  refine ⟨96128885765609851140456781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128171847687479801520609041 96128885765609851140456781)
  ·
    refine ⟨36048332162103694177671293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96128885765609851140456781 36048332162103694177671293)
    ·
      refine ⟨13518124560788885316626735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36048332162103694177671293 13518124560788885316626735)
      ·
        refine ⟨20277186841183327974940103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13518124560788885316626735 20277186841183327974940103)
        ·
          refine ⟨30415780261774991962410155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20277186841183327974940103 30415780261774991962410155)
          ·
            refine ⟨45623670392662487943615233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30415780261774991962410155 45623670392662487943615233)
            ·
              refine ⟨34217752794496865957711425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45623670392662487943615233 34217752794496865957711425)
              ·
                refine ⟨25663314595872649468283569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34217752794496865957711425 25663314595872649468283569)
                ·
                  refine ⟨19247485946904487101212677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25663314595872649468283569 19247485946904487101212677)
                  ·
                    refine ⟨3608903615044591331477377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19247485946904487101212677 3608903615044591331477377)
                    ·
                      refine ⟨2706677711283443498608033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3608903615044591331477377 2706677711283443498608033)
                      ·
                        rfl

theorem cell23_5271236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_5271236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271236 prefixEnd_5271236 := by exact prefixLift 5271236
  have htrace : WordTrace (prefixWord ++ tailWord_5271236) baseStart_5271236 baseEnd_5271236 := by
    simpa [prefixWord, tailWord_5271236, baseEnd_5271236] using wordTrace_append hprefix tailTrace_5271236
  have hstable : (prefixWord ++ tailWord_5271236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271236).length < 2 ^ (prefixWord ++ tailWord_5271236).sum := by decide
  have hdescent : baseEnd_5271236 < baseStart_5271236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271239 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_5271239 : Nat := 118140960795 + 5271239 * 2 ^ 59
def prefixEnd_5271239 : Nat := 4983230072969 + 3 ^ 40 * 5271239 * 2
def baseEnd_5271239 : Nat := 2706679251725406986870519

theorem tailTrace_5271239 : CollatzResearch.WordTrace tailWord_5271239 prefixEnd_5271239 2706679251725406986870519 := by
  unfold tailWord_5271239
  simp only [CollatzResearch.WordTrace]
  refine ⟨192257880950208833793272771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128171920633472555862181847 192257880950208833793272771)
  ·
    refine ⟨288386821425313250689909157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192257880950208833793272771 288386821425313250689909157)
    ·
      refine ⟨54072529017246234504357967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288386821425313250689909157 54072529017246234504357967)
      ·
        refine ⟨81108793525869351756536951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54072529017246234504357967 81108793525869351756536951)
        ·
          refine ⟨121663190288804027634805427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81108793525869351756536951 121663190288804027634805427)
          ·
            refine ⟨182494785433206041452208141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121663190288804027634805427 182494785433206041452208141)
            ·
              refine ⟨68435544537452265544578053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182494785433206041452208141 68435544537452265544578053)
              ·
                refine ⟨12831664600772299789608385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68435544537452265544578053 12831664600772299789608385)
                ·
                  refine ⟨9623748450579224842206289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12831664600772299789608385 9623748450579224842206289)
                  ·
                    refine ⟨7217811337934418631654717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9623748450579224842206289 7217811337934418631654717)
                    ·
                      refine ⟨2706679251725406986870519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7217811337934418631654717 2706679251725406986870519)
                      ·
                        rfl

theorem cell23_5271239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_5271239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271239 prefixEnd_5271239 := by exact prefixLift 5271239
  have htrace : WordTrace (prefixWord ++ tailWord_5271239) baseStart_5271239 baseEnd_5271239 := by
    simpa [prefixWord, tailWord_5271239, baseEnd_5271239] using wordTrace_append hprefix tailTrace_5271239
  have hstable : (prefixWord ++ tailWord_5271239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271239).length < 2 ^ (prefixWord ++ tailWord_5271239).sum := by decide
  have hdescent : baseEnd_5271239 < baseStart_5271239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271336 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 4, 4]
def baseStart_5271336 : Nat := 118140960795 + 5271336 * 2 ^ 59
def prefixEnd_5271336 : Nat := 4983230072969 + 3 ^ 40 * 5271336 * 2
def baseEnd_5271336 : Nat := 902243019782964369119191

theorem tailTrace_5271336 : CollatzResearch.WordTrace tailWord_5271336 prefixEnd_5271336 902243019782964369119191 := by
  unfold tailWord_5271336
  simp only [CollatzResearch.WordTrace]
  refine ⟨96130709415428709679776931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128174279220571612906369241 96130709415428709679776931)
  ·
    refine ⟨144196064123143064519665397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96130709415428709679776931 144196064123143064519665397)
    ·
      refine ⟨13518381011544662298718631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144196064123143064519665397 13518381011544662298718631)
      ·
        refine ⟨20277571517316993448077947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13518381011544662298718631 20277571517316993448077947)
        ·
          refine ⟨30416357275975490172116921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20277571517316993448077947 30416357275975490172116921)
          ·
            refine ⟨22812267956981617629087691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30416357275975490172116921 22812267956981617629087691)
            ·
              refine ⟨34218401935472426443631537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22812267956981617629087691 34218401935472426443631537)
              ·
                refine ⟨25663801451604319832723653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34218401935472426443631537 25663801451604319832723653)
                ·
                  refine ⟨4811962772175809968635685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25663801451604319832723653 4811962772175809968635685)
                  ·
                    refine ⟨902243019782964369119191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4811962772175809968635685 902243019782964369119191)
                    ·
                      rfl

theorem cell23_5271336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_5271336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271336 prefixEnd_5271336 := by exact prefixLift 5271336
  have htrace : WordTrace (prefixWord ++ tailWord_5271336) baseStart_5271336 baseEnd_5271336 := by
    simpa [prefixWord, tailWord_5271336, baseEnd_5271336] using wordTrace_append hprefix tailTrace_5271336
  have hstable : (prefixWord ++ tailWord_5271336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271336).length < 2 ^ (prefixWord ++ tailWord_5271336).sum := by decide
  have hdescent : baseEnd_5271336 < baseStart_5271336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271346 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_5271346 : Nat := 118140960795 + 5271346 * 2 ^ 59
def prefixEnd_5271346 : Nat := 4983230072969 + 3 ^ 40 * 5271346 * 2
def baseEnd_5271346 : Nat := 2706734194155438068232527

theorem tailTrace_5271346 : CollatzResearch.WordTrace tailWord_5271346 prefixEnd_5271346 2706734194155438068232527 := by
  unfold tailWord_5271346
  simp only [CollatzResearch.WordTrace]
  refine ⟨48065445890205297766854473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128174522373880794044945261 48065445890205297766854473)
  ·
    refine ⟨36049084417653973325140855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48065445890205297766854473 36049084417653973325140855)
    ·
      refine ⟨54073626626480959987711283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36049084417653973325140855 54073626626480959987711283)
      ·
        refine ⟨81110439939721439981566925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54073626626480959987711283 81110439939721439981566925)
        ·
          refine ⟨30416414977395539993087597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81110439939721439981566925 30416414977395539993087597)
          ·
            refine ⟨11406155616523327497407849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30416414977395539993087597 11406155616523327497407849)
            ·
              refine ⟨8554616712392495623055887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11406155616523327497407849 8554616712392495623055887)
              ·
                refine ⟨12831925068588743434583831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8554616712392495623055887 12831925068588743434583831)
                ·
                  refine ⟨19247887602883115151875747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12831925068588743434583831 19247887602883115151875747)
                  ·
                    refine ⟨28871831404324672727813621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19247887602883115151875747 28871831404324672727813621)
                    ·
                      refine ⟨2706734194155438068232527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28871831404324672727813621 2706734194155438068232527)
                      ·
                        rfl

theorem cell23_5271346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_5271346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271346 prefixEnd_5271346 := by exact prefixLift 5271346
  have htrace : WordTrace (prefixWord ++ tailWord_5271346) baseStart_5271346 baseEnd_5271346 := by
    simpa [prefixWord, tailWord_5271346, baseEnd_5271346] using wordTrace_append hprefix tailTrace_5271346
  have hstable : (prefixWord ++ tailWord_5271346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271346).length < 2 ^ (prefixWord ++ tailWord_5271346).sum := by decide
  have hdescent : baseEnd_5271346 < baseStart_5271346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271380 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_5271380 : Nat := 118140960795 + 5271380 * 2 ^ 59
def prefixEnd_5271380 : Nat := 4983230072969 + 3 ^ 40 * 5271380 * 2
def baseEnd_5271380 : Nat := 2706751652497690935207371

theorem tailTrace_5271380 : CollatzResearch.WordTrace tailWord_5271380 prefixEnd_5271380 2706751652497690935207371 := by
  unfold tailWord_5271380
  simp only [CollatzResearch.WordTrace]
  refine ⟨96131511821349007437077797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128175349095132009916103729 96131511821349007437077797)
  ·
    refine ⟨18024658466502938894452087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96131511821349007437077797 18024658466502938894452087)
    ·
      refine ⟨27036987699754408341678131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18024658466502938894452087 27036987699754408341678131)
      ·
        refine ⟨40555481549631612512517197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27036987699754408341678131 40555481549631612512517197)
        ·
          refine ⟨15208305581111854692193949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40555481549631612512517197 15208305581111854692193949)
          ·
            refine ⟨5703114592916945509572731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15208305581111854692193949 5703114592916945509572731)
            ·
              refine ⟨8554671889375418264359097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5703114592916945509572731 8554671889375418264359097)
              ·
                refine ⟨6416003917031563698269323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8554671889375418264359097 6416003917031563698269323)
                ·
                  refine ⟨9624005875547345547403985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6416003917031563698269323 9624005875547345547403985)
                  ·
                    refine ⟨7218004406660509160552989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9624005875547345547403985 7218004406660509160552989)
                    ·
                      refine ⟨2706751652497690935207371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7218004406660509160552989 2706751652497690935207371)
                      ·
                        rfl

theorem cell23_5271380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_5271380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271380 prefixEnd_5271380 := by exact prefixLift 5271380
  have htrace : WordTrace (prefixWord ++ tailWord_5271380) baseStart_5271380 baseEnd_5271380 := by
    simpa [prefixWord, tailWord_5271380, baseEnd_5271380] using wordTrace_append hprefix tailTrace_5271380
  have hstable : (prefixWord ++ tailWord_5271380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271380).length < 2 ^ (prefixWord ++ tailWord_5271380).sum := by decide
  have hdescent : baseEnd_5271380 < baseStart_5271380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271409 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 2, 6]
def baseStart_5271409 : Nat := 118140960795 + 5271409 * 2 ^ 59
def prefixEnd_5271409 : Nat := 4983230072969 + 3 ^ 40 * 5271409 * 2
def baseEnd_5271409 : Nat := 902255514478890440581579

theorem tailTrace_5271409 : CollatzResearch.WordTrace tailWord_5271409 prefixEnd_5271409 902255514478890440581579 := by
  unfold tailWord_5271409
  simp only [CollatzResearch.WordTrace]
  refine ⟨192264081359592952826961281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128176054239728635217974187 192264081359592952826961281)
  ·
    refine ⟨144198061019694714620220961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192264081359592952826961281 144198061019694714620220961)
    ·
      refine ⟨108148545764771035965165721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144198061019694714620220961 108148545764771035965165721)
      ·
        refine ⟨81111409323578276973874291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108148545764771035965165721 81111409323578276973874291)
        ·
          refine ⟨121667113985367415460811437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81111409323578276973874291 121667113985367415460811437)
          ·
            refine ⟨45625167744512780797804289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121667113985367415460811437 45625167744512780797804289)
            ·
              refine ⟨34218875808384585598353217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45625167744512780797804289 34218875808384585598353217)
              ·
                refine ⟨25664156856288439198764913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34218875808384585598353217 25664156856288439198764913)
                ·
                  refine ⟨19248117642216329399073685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25664156856288439198764913 19248117642216329399073685)
                  ·
                    refine ⟨902255514478890440581579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19248117642216329399073685 902255514478890440581579)
                    ·
                      rfl

theorem cell23_5271409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_5271409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271409 prefixEnd_5271409 := by exact prefixLift 5271409
  have htrace : WordTrace (prefixWord ++ tailWord_5271409) baseStart_5271409 baseEnd_5271409 := by
    simpa [prefixWord, tailWord_5271409, baseEnd_5271409] using wordTrace_append hprefix tailTrace_5271409
  have hstable : (prefixWord ++ tailWord_5271409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271409).length < 2 ^ (prefixWord ++ tailWord_5271409).sum := by decide
  have hdescent : baseEnd_5271409 < baseStart_5271409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271433 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 1, 4, 2]
def baseStart_5271433 : Nat := 118140960795 + 5271433 * 2 ^ 59
def prefixEnd_5271433 : Nat := 4983230072969 + 3 ^ 40 * 5271433 * 2
def baseEnd_5271433 : Nat := 2706778866972379227844627

theorem tailTrace_5271433 : CollatzResearch.WordTrace tailWord_5271433 prefixEnd_5271433 2706778866972379227844627 := by
  unfold tailWord_5271433
  simp only [CollatzResearch.WordTrace]
  refine ⟨192264956711506004925834953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128176637807670669950556635 192264956711506004925834953)
  ·
    refine ⟨144198717533629503694376215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192264956711506004925834953 144198717533629503694376215)
    ·
      refine ⟨216298076300444255541564323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144198717533629503694376215 216298076300444255541564323)
      ·
        refine ⟨324447114450666383312346485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216298076300444255541564323 324447114450666383312346485)
        ·
          refine ⟨30416916979749973435532483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 324447114450666383312346485 30416916979749973435532483)
          ·
            refine ⟨45625375469624960153298725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30416916979749973435532483 45625375469624960153298725)
            ·
              refine ⟨8554757900554680028743511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45625375469624960153298725 8554757900554680028743511)
              ·
                refine ⟨12832136850832020043115267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8554757900554680028743511 12832136850832020043115267)
                ·
                  refine ⟨19248205276248030064672901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12832136850832020043115267 19248205276248030064672901)
                  ·
                    refine ⟨3609038489296505637126169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19248205276248030064672901 3609038489296505637126169)
                    ·
                      refine ⟨2706778866972379227844627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609038489296505637126169 2706778866972379227844627)
                      ·
                        rfl

theorem cell23_5271433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 4, 2].length) (baseStart_5271433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271433 prefixEnd_5271433 := by exact prefixLift 5271433
  have htrace : WordTrace (prefixWord ++ tailWord_5271433) baseStart_5271433 baseEnd_5271433 := by
    simpa [prefixWord, tailWord_5271433, baseEnd_5271433] using wordTrace_append hprefix tailTrace_5271433
  have hstable : (prefixWord ++ tailWord_5271433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271433).length < 2 ^ (prefixWord ++ tailWord_5271433).sum := by decide
  have hdescent : baseEnd_5271433 < baseStart_5271433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271454 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5271454 : Nat := 118140960795 + 5271454 * 2 ^ 59
def prefixEnd_5271454 : Nat := 4983230072969 + 3 ^ 40 * 5271454 * 2
def baseEnd_5271454 : Nat := 2706789650066123645682031

theorem tailTrace_5271454 : CollatzResearch.WordTrace tailWord_5271454 prefixEnd_5271454 2706789650066123645682031 := by
  unfold tailWord_5271454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24033215330553740689043677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128177148429619950341566277 24033215330553740689043677)
  ·
    refine ⟨9012455748957652758391379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24033215330553740689043677 9012455748957652758391379)
    ·
      refine ⟨13518683623436479137587069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9012455748957652758391379 13518683623436479137587069)
      ·
        refine ⟨5069506358788679676595151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13518683623436479137587069 5069506358788679676595151)
        ·
          refine ⟨7604259538183019514892727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5069506358788679676595151 7604259538183019514892727)
          ·
            refine ⟨11406389307274529272339091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7604259538183019514892727 11406389307274529272339091)
            ·
              refine ⟨17109583960911793908508637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11406389307274529272339091 17109583960911793908508637)
              ·
                refine ⟨6416093985341922715690739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17109583960911793908508637 6416093985341922715690739)
                ·
                  refine ⟨9624140978012884073536109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6416093985341922715690739 9624140978012884073536109)
                  ·
                    refine ⟨3609052866754831527576041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9624140978012884073536109 3609052866754831527576041)
                    ·
                      refine ⟨2706789650066123645682031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609052866754831527576041 2706789650066123645682031)
                      ·
                        rfl

theorem cell23_5271454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5271454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271454 prefixEnd_5271454 := by exact prefixLift 5271454
  have htrace : WordTrace (prefixWord ++ tailWord_5271454) baseStart_5271454 baseEnd_5271454 := by
    simpa [prefixWord, tailWord_5271454, baseEnd_5271454] using wordTrace_append hprefix tailTrace_5271454
  have hstable : (prefixWord ++ tailWord_5271454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271454).length < 2 ^ (prefixWord ++ tailWord_5271454).sum := by decide
  have hdescent : baseEnd_5271454 < baseStart_5271454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271473 : List Nat := [1, 2, 2, 4, 2, 1, 2, 4, 5]
def baseStart_5271473 : Nat := 118140960795 + 5271473 * 2 ^ 59
def prefixEnd_5271473 : Nat := 4983230072969 + 3 ^ 40 * 5271473 * 2
def baseEnd_5271473 : Nat := 300755489577617674593827

theorem tailTrace_5271473 : CollatzResearch.WordTrace tailWord_5271473 prefixEnd_5271473 300755489577617674593827 := by
  unfold tailWord_5271473
  simp only [CollatzResearch.WordTrace]
  refine ⟨192266415631361091757291073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128177610420907394504860715 192266415631361091757291073)
  ·
    refine ⟨144199811723520818817968305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192266415631361091757291073 144199811723520818817968305)
    ·
      refine ⟨108149858792640614113476229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144199811723520818817968305 108149858792640614113476229)
      ·
        refine ⟨20278098523620115146276793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108149858792640614113476229 20278098523620115146276793)
        ·
          refine ⟨15208573892715086359707595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20278098523620115146276793 15208573892715086359707595)
          ·
            refine ⟨22812860839072629539561393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15208573892715086359707595 22812860839072629539561393)
            ·
              refine ⟨17109645629304472154671045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22812860839072629539561393 17109645629304472154671045)
              ·
                refine ⟨3208058555494588529000821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17109645629304472154671045 3208058555494588529000821)
                ·
                  refine ⟨300755489577617674593827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3208058555494588529000821 300755489577617674593827)
                  ·
                    rfl

theorem cell23_5271473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 5].length) (baseStart_5271473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271473 prefixEnd_5271473 := by exact prefixLift 5271473
  have htrace : WordTrace (prefixWord ++ tailWord_5271473) baseStart_5271473 baseEnd_5271473 := by
    simpa [prefixWord, tailWord_5271473, baseEnd_5271473] using wordTrace_append hprefix tailTrace_5271473
  have hstable : (prefixWord ++ tailWord_5271473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271473).length < 2 ^ (prefixWord ++ tailWord_5271473).sum := by decide
  have hdescent : baseEnd_5271473 < baseStart_5271473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271479 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_5271479 : Nat := 118140960795 + 5271479 * 2 ^ 59
def prefixEnd_5271479 : Nat := 4983230072969 + 3 ^ 40 * 5271479 * 2
def baseEnd_5271479 : Nat := 2706802487082486047869415

theorem tailTrace_5271479 : CollatzResearch.WordTrace tailWord_5271479 prefixEnd_5271479 2706802487082486047869415 := by
  unfold tailWord_5271479
  simp only [CollatzResearch.WordTrace]
  refine ⟨192266634469339354782009491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128177756312892903188006327 192266634469339354782009491)
  ·
    refine ⟨288399951704009032173014237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192266634469339354782009491 288399951704009032173014237)
    ·
      refine ⟨108149981889003387064880339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288399951704009032173014237 108149981889003387064880339)
      ·
        refine ⟨162224972833505080597320509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108149981889003387064880339 162224972833505080597320509)
        ·
          refine ⟨60834364812564405223995191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162224972833505080597320509 60834364812564405223995191)
          ·
            refine ⟨91251547218846607835992787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60834364812564405223995191 91251547218846607835992787)
            ·
              refine ⟨136877320828269911753989181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91251547218846607835992787 136877320828269911753989181)
              ·
                refine ⟨51328995310601216907745943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136877320828269911753989181 51328995310601216907745943)
                ·
                  refine ⟨76993492965901825361618915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51328995310601216907745943 76993492965901825361618915)
                  ·
                    refine ⟨115490239448852738042428373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76993492965901825361618915 115490239448852738042428373)
                    ·
                      refine ⟨2706802487082486047869415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115490239448852738042428373 2706802487082486047869415)
                      ·
                        rfl

theorem cell23_5271479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_5271479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271479 prefixEnd_5271479 := by exact prefixLift 5271479
  have htrace : WordTrace (prefixWord ++ tailWord_5271479) baseStart_5271479 baseEnd_5271479 := by
    simpa [prefixWord, tailWord_5271479, baseEnd_5271479] using wordTrace_append hprefix tailTrace_5271479
  have hstable : (prefixWord ++ tailWord_5271479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271479).length < 2 ^ (prefixWord ++ tailWord_5271479).sum := by decide
  have hdescent : baseEnd_5271479 < baseStart_5271479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271484 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5271484 : Nat := 118140960795 + 5271484 * 2 ^ 59
def prefixEnd_5271484 : Nat := 4983230072969 + 3 ^ 40 * 5271484 * 2
def baseEnd_5271484 : Nat := 2706805054485758528306893

theorem tailTrace_5271484 : CollatzResearch.WordTrace tailWord_5271484 prefixEnd_5271484 2706805054485758528306893 := by
  unfold tailWord_5271484
  simp only [CollatzResearch.WordTrace]
  refine ⟨96133408417160620317970753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128177877889547493757294337 96133408417160620317970753)
  ·
    refine ⟨72100056312870465238478065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96133408417160620317970753 72100056312870465238478065)
    ·
      refine ⟨54075042234652848928858549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72100056312870465238478065 54075042234652848928858549)
      ·
        refine ⟨5069535209498704587080489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54075042234652848928858549 5069535209498704587080489)
        ·
          refine ⟨3802151407124028440310367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5069535209498704587080489 3802151407124028440310367)
          ·
            refine ⟨5703227110686042660465551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3802151407124028440310367 5703227110686042660465551)
            ·
              refine ⟨8554840666029063990698327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5703227110686042660465551 8554840666029063990698327)
              ·
                refine ⟨12832260999043595986047491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8554840666029063990698327 12832260999043595986047491)
                ·
                  refine ⟨19248391498565393979071237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12832260999043595986047491 19248391498565393979071237)
                  ·
                    refine ⟨3609073405981011371075857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19248391498565393979071237 3609073405981011371075857)
                    ·
                      refine ⟨2706805054485758528306893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609073405981011371075857 2706805054485758528306893)
                      ·
                        rfl

theorem cell23_5271484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5271484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271484 prefixEnd_5271484 := by exact prefixLift 5271484
  have htrace : WordTrace (prefixWord ++ tailWord_5271484) baseStart_5271484 baseEnd_5271484 := by
    simpa [prefixWord, tailWord_5271484, baseEnd_5271484] using wordTrace_append hprefix tailTrace_5271484
  have hstable : (prefixWord ++ tailWord_5271484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271484).length < 2 ^ (prefixWord ++ tailWord_5271484).sum := by decide
  have hdescent : baseEnd_5271484 < baseStart_5271484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271486 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_5271486 : Nat := 118140960795 + 5271486 * 2 ^ 59
def prefixEnd_5271486 : Nat := 4983230072969 + 3 ^ 40 * 5271486 * 2
def baseEnd_5271486 : Nat := 902268693815689173493961

theorem tailTrace_5271486 : CollatzResearch.WordTrace tailWord_5271486 prefixEnd_5271486 902268693815689173493961 := by
  unfold tailWord_5271486
  simp only [CollatzResearch.WordTrace]
  refine ⟨24033361222539249372189289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128177926520209329985009541 24033361222539249372189289)
  ·
    refine ⟨18025020916904437029141967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24033361222539249372189289 18025020916904437029141967)
    ·
      refine ⟨27037531375356655543712951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18025020916904437029141967 27037531375356655543712951)
      ·
        refine ⟨40556297063034983315569427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27037531375356655543712951 40556297063034983315569427)
        ·
          refine ⟨60834445594552474973354141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40556297063034983315569427 60834445594552474973354141)
          ·
            refine ⟨22812917097957178115007803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60834445594552474973354141 22812917097957178115007803)
            ·
              refine ⟨34219375646935767172511705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22812917097957178115007803 34219375646935767172511705)
              ·
                refine ⟨25664531735201825379383779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34219375646935767172511705 25664531735201825379383779)
                ·
                  refine ⟨38496797602802738069075669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25664531735201825379383779 38496797602802738069075669)
                  ·
                    refine ⟨902268693815689173493961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38496797602802738069075669 902268693815689173493961)
                    ·
                      rfl

theorem cell23_5271486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_5271486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271486 prefixEnd_5271486 := by exact prefixLift 5271486
  have htrace : WordTrace (prefixWord ++ tailWord_5271486) baseStart_5271486 baseEnd_5271486 := by
    simpa [prefixWord, tailWord_5271486, baseEnd_5271486] using wordTrace_append hprefix tailTrace_5271486
  have hstable : (prefixWord ++ tailWord_5271486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271486).length < 2 ^ (prefixWord ++ tailWord_5271486).sum := by decide
  have hdescent : baseEnd_5271486 < baseStart_5271486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271499 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 2, 8]
def baseStart_5271499 : Nat := 118140960795 + 5271499 * 2 ^ 59
def prefixEnd_5271499 : Nat := 4983230072969 + 3 ^ 40 * 5271499 * 2
def baseEnd_5271499 : Nat := 902270918898525323206441

theorem tailTrace_5271499 : CollatzResearch.WordTrace tailWord_5271499 prefixEnd_5271499 902270918898525323206441 := by
  unfold tailWord_5271499
  simp only [CollatzResearch.WordTrace]
  refine ⟨192267363929266898197737551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128178242619511265465158367 192267363929266898197737551)
  ·
    refine ⟨288401045893900347296606327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192267363929266898197737551 288401045893900347296606327)
    ·
      refine ⟨432601568840850520944909491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288401045893900347296606327 432601568840850520944909491)
      ·
        refine ⟨648902353261275781417364237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432601568840850520944909491 648902353261275781417364237)
        ·
          refine ⟨243338382472978418031511589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 648902353261275781417364237 243338382472978418031511589)
          ·
            refine ⟨45625946713683453380908423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243338382472978418031511589 45625946713683453380908423)
            ·
              refine ⟨68438920070525180071362635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45625946713683453380908423 68438920070525180071362635)
              ·
                refine ⟨102658380105787770107043953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68438920070525180071362635 102658380105787770107043953)
                ·
                  refine ⟨76993785079340827580282965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102658380105787770107043953 76993785079340827580282965)
                  ·
                    refine ⟨902270918898525323206441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76993785079340827580282965 902270918898525323206441)
                    ·
                      rfl

theorem cell23_5271499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 8].length) (baseStart_5271499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271499 prefixEnd_5271499 := by exact prefixLift 5271499
  have htrace : WordTrace (prefixWord ++ tailWord_5271499) baseStart_5271499 baseEnd_5271499 := by
    simpa [prefixWord, tailWord_5271499, baseEnd_5271499] using wordTrace_append hprefix tailTrace_5271499
  have hstable : (prefixWord ++ tailWord_5271499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271499).length < 2 ^ (prefixWord ++ tailWord_5271499).sum := by decide
  have hdescent : baseEnd_5271499 < baseStart_5271499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271523 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 4]
def baseStart_5271523 : Nat := 118140960795 + 5271523 * 2 ^ 59
def prefixEnd_5271523 : Nat := 4983230072969 + 3 ^ 40 * 5271523 * 2
def baseEnd_5271523 : Nat := 2706825080231283875719213

theorem tailTrace_5271523 : CollatzResearch.WordTrace tailWord_5271523 prefixEnd_5271523 2706825080231283875719213 := by
  unfold tailWord_5271523
  simp only [CollatzResearch.WordTrace]
  refine ⟨192268239281179950296611223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128178826187453300197740815 192268239281179950296611223)
  ·
    refine ⟨288402358921769925444916835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192268239281179950296611223 288402358921769925444916835)
    ·
      refine ⟨432603538382654888167375253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288402358921769925444916835 432603538382654888167375253)
      ·
        refine ⟨20278290861686947882845715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 432603538382654888167375253 20278290861686947882845715)
        ·
          refine ⟨30417436292530421824268573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20278290861686947882845715 30417436292530421824268573)
          ·
            refine ⟨11406538609698908184100715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30417436292530421824268573 11406538609698908184100715)
            ·
              refine ⟨17109807914548362276151073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11406538609698908184100715 17109807914548362276151073)
              ·
                refine ⟨12832355935911271707113305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17109807914548362276151073 12832355935911271707113305)
                ·
                  refine ⟨9624266951933453780334979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12832355935911271707113305 9624266951933453780334979)
                  ·
                    refine ⟨14436400427900180670502469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9624266951933453780334979 14436400427900180670502469)
                    ·
                      refine ⟨2706825080231283875719213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14436400427900180670502469 2706825080231283875719213)
                      ·
                        rfl

theorem cell23_5271523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_5271523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271523 prefixEnd_5271523 := by exact prefixLift 5271523
  have htrace : WordTrace (prefixWord ++ tailWord_5271523) baseStart_5271523 baseEnd_5271523 := by
    simpa [prefixWord, tailWord_5271523, baseEnd_5271523] using wordTrace_append hprefix tailTrace_5271523
  have hstable : (prefixWord ++ tailWord_5271523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271523).length < 2 ^ (prefixWord ++ tailWord_5271523).sum := by decide
  have hdescent : baseEnd_5271523 < baseStart_5271523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271613 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_5271613 : Nat := 118140960795 + 5271613 * 2 ^ 59
def prefixEnd_5271613 : Nat := 4983230072969 + 3 ^ 40 * 5271613 * 2
def baseEnd_5271613 : Nat := 2706871293490188523593799

theorem tailTrace_5271613 : CollatzResearch.WordTrace tailWord_5271613 prefixEnd_5271613 2706871293490188523593799 := by
  unfold tailWord_5271613
  simp only [CollatzResearch.WordTrace]
  refine ⟨192271521850853895667387493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128181014567235930444924995 192271521850853895667387493)
  ·
    refine ⟨36050910347035105437635155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192271521850853895667387493 36050910347035105437635155)
    ·
      refine ⟨54076365520552658156452733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36050910347035105437635155 54076365520552658156452733)
      ·
        refine ⟨20278637070207246808669775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54076365520552658156452733 20278637070207246808669775)
        ·
          refine ⟨30417955605310870213004663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20278637070207246808669775 30417955605310870213004663)
          ·
            refine ⟨45626933407966305319506995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30417955605310870213004663 45626933407966305319506995)
            ·
              refine ⟨68440400111949457979260493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45626933407966305319506995 68440400111949457979260493)
              ·
                refine ⟨25665150041981046742222685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68440400111949457979260493 25665150041981046742222685)
                ·
                  refine ⟨9624431265742892528333507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25665150041981046742222685 9624431265742892528333507)
                  ·
                    refine ⟨14436646898614338792500261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9624431265742892528333507 14436646898614338792500261)
                    ·
                      refine ⟨2706871293490188523593799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14436646898614338792500261 2706871293490188523593799)
                      ·
                        rfl

theorem cell23_5271613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_5271613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271613 prefixEnd_5271613 := by exact prefixLift 5271613
  have htrace : WordTrace (prefixWord ++ tailWord_5271613) baseStart_5271613 baseEnd_5271613 := by
    simpa [prefixWord, tailWord_5271613, baseEnd_5271613] using wordTrace_append hprefix tailTrace_5271613
  have hstable : (prefixWord ++ tailWord_5271613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271613).length < 2 ^ (prefixWord ++ tailWord_5271613).sum := by decide
  have hdescent : baseEnd_5271613 < baseStart_5271613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271617 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_5271617 : Nat := 118140960795 + 5271617 * 2 ^ 59
def prefixEnd_5271617 : Nat := 4983230072969 + 3 ^ 40 * 5271617 * 2
def baseEnd_5271617 : Nat := 2706873347412806507943781

theorem tailTrace_5271617 : CollatzResearch.WordTrace tailWord_5271617 prefixEnd_5271617 2706873347412806507943781 := by
  unfold tailWord_5271617
  simp only [CollatzResearch.WordTrace]
  refine ⟨192271667742839404350533105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128181111828559602900355403 192271667742839404350533105)
  ·
    refine ⟨144203750807129553262899829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192271667742839404350533105 144203750807129553262899829)
    ·
      refine ⟨13519101638168395618396859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144203750807129553262899829 13519101638168395618396859)
      ·
        refine ⟨20278652457252593427595289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13519101638168395618396859 20278652457252593427595289)
        ·
          refine ⟨15208989342939445070696467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20278652457252593427595289 15208989342939445070696467)
          ·
            refine ⟨22813484014409167606044701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15208989342939445070696467 22813484014409167606044701)
            ·
              refine ⟨8555056505403437852266763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22813484014409167606044701 8555056505403437852266763)
              ·
                refine ⟨12832584758105156778400145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8555056505403437852266763 12832584758105156778400145)
                ·
                  refine ⟨9624438568578867583800109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12832584758105156778400145 9624438568578867583800109)
                  ·
                    refine ⟨3609164463217075343925041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9624438568578867583800109 3609164463217075343925041)
                    ·
                      refine ⟨2706873347412806507943781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609164463217075343925041 2706873347412806507943781)
                      ·
                        rfl

theorem cell23_5271617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_5271617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271617 prefixEnd_5271617 := by exact prefixLift 5271617
  have htrace : WordTrace (prefixWord ++ tailWord_5271617) baseStart_5271617 baseEnd_5271617 := by
    simpa [prefixWord, tailWord_5271617, baseEnd_5271617] using wordTrace_append hprefix tailTrace_5271617
  have hstable : (prefixWord ++ tailWord_5271617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271617).length < 2 ^ (prefixWord ++ tailWord_5271617).sum := by decide
  have hdescent : baseEnd_5271617 < baseStart_5271617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271623 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 4, 4]
def baseStart_5271623 : Nat := 118140960795 + 5271623 * 2 ^ 59
def prefixEnd_5271623 : Nat := 4983230072969 + 3 ^ 40 * 5271623 * 2
def baseEnd_5271623 : Nat := 902292142765577828156251

theorem tailTrace_5271623 : CollatzResearch.WordTrace tailWord_5271623 prefixEnd_5271623 902292142765577828156251 := by
  unfold tailWord_5271623
  simp only [CollatzResearch.WordTrace]
  refine ⟨192271886580817667375251523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128181257720545111583501015 192271886580817667375251523)
  ·
    refine ⟨288407829871226501062877285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192271886580817667375251523 288407829871226501062877285)
    ·
      refine ⟨54076468100854968949289491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288407829871226501062877285 54076468100854968949289491)
      ·
        refine ⟨81114702151282453423934237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54076468100854968949289491 81114702151282453423934237)
        ·
          refine ⟨30418013306730920033975339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81114702151282453423934237 30418013306730920033975339)
          ·
            refine ⟨45627019960096380050963009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30418013306730920033975339 45627019960096380050963009)
            ·
              refine ⟨34220264970072285038222257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45627019960096380050963009 34220264970072285038222257)
              ·
                refine ⟨25665198727554213778666693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34220264970072285038222257 25665198727554213778666693)
                ·
                  refine ⟨4812224761416415083500005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25665198727554213778666693 4812224761416415083500005)
                  ·
                    refine ⟨902292142765577828156251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4812224761416415083500005 902292142765577828156251)
                    ·
                      rfl

theorem cell23_5271623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_5271623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271623 prefixEnd_5271623 := by exact prefixLift 5271623
  have htrace : WordTrace (prefixWord ++ tailWord_5271623) baseStart_5271623 baseEnd_5271623 := by
    simpa [prefixWord, tailWord_5271623, baseEnd_5271623] using wordTrace_append hprefix tailTrace_5271623
  have hstable : (prefixWord ++ tailWord_5271623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271623).length < 2 ^ (prefixWord ++ tailWord_5271623).sum := by decide
  have hdescent : baseEnd_5271623 < baseStart_5271623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271626 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_5271626 : Nat := 118140960795 + 5271626 * 2 ^ 59
def prefixEnd_5271626 : Nat := 4983230072969 + 3 ^ 40 * 5271626 * 2
def baseEnd_5271626 : Nat := 2706877968738696972731239

theorem tailTrace_5271626 : CollatzResearch.WordTrace tailWord_5271626 prefixEnd_5271626 2706877968738696972731239 := by
  unfold tailWord_5271626
  simp only [CollatzResearch.WordTrace]
  refine ⟨48067998999951699721902683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128181330666537865925073821 48067998999951699721902683)
  ·
    refine ⟨72101998499927549582854025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48067998999951699721902683 72101998499927549582854025)
    ·
      refine ⟨54076498874945662187140519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72101998499927549582854025 54076498874945662187140519)
      ·
        refine ⟨81114748312418493280710779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54076498874945662187140519 81114748312418493280710779)
        ·
          refine ⟨121672122468627739921066169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81114748312418493280710779 121672122468627739921066169)
          ·
            refine ⟨91254091851470804940799627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121672122468627739921066169 91254091851470804940799627)
            ·
              refine ⟨136881137777206207411199441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91254091851470804940799627 136881137777206207411199441)
              ·
                refine ⟨102660853332904655558399581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136881137777206207411199441 102660853332904655558399581)
                ·
                  refine ⟨38497819999839245834399843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102660853332904655558399581 38497819999839245834399843)
                  ·
                    refine ⟨57746729999758868751599765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38497819999839245834399843 57746729999758868751599765)
                    ·
                      refine ⟨2706877968738696972731239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57746729999758868751599765 2706877968738696972731239)
                      ·
                        rfl

theorem cell23_5271626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_5271626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271626 prefixEnd_5271626 := by exact prefixLift 5271626
  have htrace : WordTrace (prefixWord ++ tailWord_5271626) baseStart_5271626 baseEnd_5271626 := by
    simpa [prefixWord, tailWord_5271626, baseEnd_5271626] using wordTrace_append hprefix tailTrace_5271626
  have hstable : (prefixWord ++ tailWord_5271626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271626).length < 2 ^ (prefixWord ++ tailWord_5271626).sum := by decide
  have hdescent : baseEnd_5271626 < baseStart_5271626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271630 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_5271630 : Nat := 118140960795 + 5271630 * 2 ^ 59
def prefixEnd_5271630 : Nat := 4983230072969 + 3 ^ 40 * 5271630 * 2
def baseEnd_5271630 : Nat := 2706880022661314957081221

theorem tailTrace_5271630 : CollatzResearch.WordTrace tailWord_5271630 prefixEnd_5271630 2706880022661314957081221 := by
  unfold tailWord_5271630
  simp only [CollatzResearch.WordTrace]
  refine ⟨24034017736474038446344543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128181427927861538380504229 24034017736474038446344543)
  ·
    refine ⟨36051026604711057669516815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24034017736474038446344543 36051026604711057669516815)
    ·
      refine ⟨54076539907066586504275223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36051026604711057669516815 54076539907066586504275223)
      ·
        refine ⟨81114809860599879756412835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54076539907066586504275223 81114809860599879756412835)
        ·
          refine ⟨121672214790899819634619253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81114809860599879756412835 121672214790899819634619253)
          ·
            refine ⟨11406770136646858090745555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121672214790899819634619253 11406770136646858090745555)
            ·
              refine ⟨17110155204970287136118333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11406770136646858090745555 17110155204970287136118333)
              ·
                refine ⟨6416308201863857676044375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17110155204970287136118333 6416308201863857676044375)
                ·
                  refine ⟨9624462302795786514066563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6416308201863857676044375 9624462302795786514066563)
                  ·
                    refine ⟨14436693454193679771099845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9624462302795786514066563 14436693454193679771099845)
                    ·
                      refine ⟨2706880022661314957081221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14436693454193679771099845 2706880022661314957081221)
                      ·
                        rfl

theorem cell23_5271630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_5271630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271630 prefixEnd_5271630 := by exact prefixLift 5271630
  have htrace : WordTrace (prefixWord ++ tailWord_5271630) baseStart_5271630 baseEnd_5271630 := by
    simpa [prefixWord, tailWord_5271630, baseEnd_5271630] using wordTrace_append hprefix tailTrace_5271630
  have hstable : (prefixWord ++ tailWord_5271630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271630).length < 2 ^ (prefixWord ++ tailWord_5271630).sum := by decide
  have hdescent : baseEnd_5271630 < baseStart_5271630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271640 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 2, 4]
def baseStart_5271640 : Nat := 118140960795 + 5271640 * 2 ^ 59
def prefixEnd_5271640 : Nat := 4983230072969 + 3 ^ 40 * 5271640 * 2
def baseEnd_5271640 : Nat := 902295052489286639318725

theorem tailTrace_5271640 : CollatzResearch.WordTrace tailWord_5271640 prefixEnd_5271640 902295052489286639318725 := by
  unfold tailWord_5271640
  simp only [CollatzResearch.WordTrace]
  refine ⟨96136253310878039639310187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128181671081170719519080249 96136253310878039639310187)
  ·
    refine ⟨144204379966317059458965281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96136253310878039639310187 144204379966317059458965281)
    ·
      refine ⟨108153284974737794594223961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144204379966317059458965281 108153284974737794594223961)
      ·
        refine ⟨81114963731053345945667971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108153284974737794594223961 81114963731053345945667971)
        ·
          refine ⟨121672445596580018918501957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81114963731053345945667971 121672445596580018918501957)
          ·
            refine ⟨22813583549358753547219117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121672445596580018918501957 22813583549358753547219117)
            ·
              refine ⟨8555093831009532580207169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22813583549358753547219117 8555093831009532580207169)
              ·
                refine ⟨6416320373257149435155377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8555093831009532580207169 6416320373257149435155377)
                ·
                  refine ⟨4812240279942862076366533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6416320373257149435155377 4812240279942862076366533)
                  ·
                    refine ⟨902295052489286639318725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4812240279942862076366533 902295052489286639318725)
                    ·
                      rfl

theorem cell23_5271640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_5271640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271640 prefixEnd_5271640 := by exact prefixLift 5271640
  have htrace : WordTrace (prefixWord ++ tailWord_5271640) baseStart_5271640 baseEnd_5271640 := by
    simpa [prefixWord, tailWord_5271640, baseEnd_5271640] using wordTrace_append hprefix tailTrace_5271640
  have hstable : (prefixWord ++ tailWord_5271640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271640).length < 2 ^ (prefixWord ++ tailWord_5271640).sum := by decide
  have hdescent : baseEnd_5271640 < baseStart_5271640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271660 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_5271660 : Nat := 118140960795 + 5271660 * 2 ^ 59
def prefixEnd_5271660 : Nat := 4983230072969 + 3 ^ 40 * 5271660 * 2
def baseEnd_5271660 : Nat := 2706895427080949839706083

theorem tailTrace_5271660 : CollatzResearch.WordTrace tailWord_5271660 prefixEnd_5271660 2706895427080949839706083 := by
  unfold tailWord_5271660
  simp only [CollatzResearch.WordTrace]
  refine ⟨96136618040841811347174217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128182157387789081796232289 96136618040841811347174217)
  ·
    refine ⟨72102463530631358510380663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96136618040841811347174217 72102463530631358510380663)
    ·
      refine ⟨108153695295947037765570995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72102463530631358510380663 108153695295947037765570995)
      ·
        refine ⟨162230542943920556648356493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108153695295947037765570995 162230542943920556648356493)
        ·
          refine ⟨60836453603970208743133685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162230542943920556648356493 60836453603970208743133685)
          ·
            refine ⟨5703417525372207069668783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60836453603970208743133685 5703417525372207069668783)
            ·
              refine ⟨8555126288058310604503175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5703417525372207069668783 8555126288058310604503175)
              ·
                refine ⟨12832689432087465906754763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8555126288058310604503175 12832689432087465906754763)
                ·
                  refine ⟨19249034148131198860132145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12832689432087465906754763 19249034148131198860132145)
                  ·
                    refine ⟨14436775611098399145099109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19249034148131198860132145 14436775611098399145099109)
                    ·
                      refine ⟨2706895427080949839706083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14436775611098399145099109 2706895427080949839706083)
                      ·
                        rfl

theorem cell23_5271660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_5271660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271660 prefixEnd_5271660 := by exact prefixLift 5271660
  have htrace : WordTrace (prefixWord ++ tailWord_5271660) baseStart_5271660 baseEnd_5271660 := by
    simpa [prefixWord, tailWord_5271660, baseEnd_5271660] using wordTrace_append hprefix tailTrace_5271660
  have hstable : (prefixWord ++ tailWord_5271660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271660).length < 2 ^ (prefixWord ++ tailWord_5271660).sum := by decide
  have hdescent : baseEnd_5271660 < baseStart_5271660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271670 : List Nat := [5, 1, 1, 2, 1, 2, 4, 7]
def baseStart_5271670 : Nat := 118140960795 + 5271670 * 2 ^ 59
def prefixEnd_5271670 : Nat := 4983230072969 + 3 ^ 40 * 5271670 * 2
def baseEnd_5271670 : Nat := 100255576366203511132631

theorem tailTrace_5271670 : CollatzResearch.WordTrace tailWord_5271670 prefixEnd_5271670 100255576366203511132631 := by
  unfold tailWord_5271670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12017100050727962150138279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128182400541098262934808309 12017100050727962150138279)
  ·
    refine ⟨18025650076091943225207419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12017100050727962150138279 18025650076091943225207419)
    ·
      refine ⟨27038475114137914837811129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18025650076091943225207419 27038475114137914837811129)
      ·
        refine ⟨20278856335603436128358347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27038475114137914837811129 20278856335603436128358347)
        ·
          refine ⟨30418284503405154192537521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20278856335603436128358347 30418284503405154192537521)
          ·
            refine ⟨22813713377553865644403141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30418284503405154192537521 22813713377553865644403141)
            ·
              refine ⟨4277571258291349808325589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22813713377553865644403141 4277571258291349808325589)
              ·
                refine ⟨100255576366203511132631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4277571258291349808325589 100255576366203511132631)
                ·
                  rfl

theorem cell23_5271670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_5271670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271670 prefixEnd_5271670 := by exact prefixLift 5271670
  have htrace : WordTrace (prefixWord ++ tailWord_5271670) baseStart_5271670 baseEnd_5271670 := by
    simpa [prefixWord, tailWord_5271670, baseEnd_5271670] using wordTrace_append hprefix tailTrace_5271670
  have hstable : (prefixWord ++ tailWord_5271670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271670).length < 2 ^ (prefixWord ++ tailWord_5271670).sum := by decide
  have hdescent : baseEnd_5271670 < baseStart_5271670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271714 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_5271714 : Nat := 118140960795 + 5271714 * 2 ^ 59
def prefixEnd_5271714 : Nat := 4983230072969 + 3 ^ 40 * 5271714 * 2
def baseEnd_5271714 : Nat := 2706923155036292628430835

theorem tailTrace_5271714 : CollatzResearch.WordTrace tailWord_5271714 prefixEnd_5271714 2706923155036292628430835 := by
  unfold tailWord_5271714
  simp only [CollatzResearch.WordTrace]
  refine ⟨48068801405871997479203549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128183470415658659944542797 48068801405871997479203549)
  ·
    refine ⟨18025800527201999054701331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48068801405871997479203549 18025800527201999054701331)
    ·
      refine ⟨27038700790802998582051997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18025800527201999054701331 27038700790802998582051997)
      ·
        refine ⟨10139512796551124468269499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27038700790802998582051997 10139512796551124468269499)
        ·
          refine ⟨15209269194826686702404249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10139512796551124468269499 15209269194826686702404249)
          ·
            refine ⟨11406951896120015026803187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15209269194826686702404249 11406951896120015026803187)
            ·
              refine ⟨17110427844180022540204781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11406951896120015026803187 17110427844180022540204781)
              ·
                refine ⟨6416410441567508452576793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17110427844180022540204781 6416410441567508452576793)
                ·
                  refine ⟨4812307831175631339432595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6416410441567508452576793 4812307831175631339432595)
                  ·
                    refine ⟨7218461746763447009148893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4812307831175631339432595 7218461746763447009148893)
                    ·
                      refine ⟨2706923155036292628430835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7218461746763447009148893 2706923155036292628430835)
                      ·
                        rfl

theorem cell23_5271714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_5271714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271714 prefixEnd_5271714 := by exact prefixLift 5271714
  have htrace : WordTrace (prefixWord ++ tailWord_5271714) baseStart_5271714 baseEnd_5271714 := by
    simpa [prefixWord, tailWord_5271714, baseEnd_5271714] using wordTrace_append hprefix tailTrace_5271714
  have hstable : (prefixWord ++ tailWord_5271714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271714).length < 2 ^ (prefixWord ++ tailWord_5271714).sum := by decide
  have hdescent : baseEnd_5271714 < baseStart_5271714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271754 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_5271754 : Nat := 118140960795 + 5271754 * 2 ^ 59
def prefixEnd_5271754 : Nat := 4983230072969 + 3 ^ 40 * 5271754 * 2
def baseEnd_5271754 : Nat := 2706943694262472471930651

theorem tailTrace_5271754 : CollatzResearch.WordTrace tailWord_5271754 prefixEnd_5271754 2706943694262472471930651 := by
  unfold tailWord_5271754
  simp only [CollatzResearch.WordTrace]
  refine ⟨48069166135835769187067579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128184443028895384498846877 48069166135835769187067579)
  ·
    refine ⟨72103749203753653780601369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48069166135835769187067579 72103749203753653780601369)
    ·
      refine ⟨54077811902815240335451027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72103749203753653780601369 54077811902815240335451027)
      ·
        refine ⟨81116717854222860503176541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54077811902815240335451027 81116717854222860503176541)
        ·
          refine ⟨30418769195333572688691203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81116717854222860503176541 30418769195333572688691203)
          ·
            refine ⟨45628153793000359033036805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30418769195333572688691203 45628153793000359033036805)
            ·
              refine ⟨8555278836187567318694401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45628153793000359033036805 8555278836187567318694401)
              ·
                refine ⟨6416459127140675489020801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8555278836187567318694401 6416459127140675489020801)
                ·
                  refine ⟨4812344345355506616765601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6416459127140675489020801 4812344345355506616765601)
                  ·
                    refine ⟨3609258259016629962574201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4812344345355506616765601 3609258259016629962574201)
                    ·
                      refine ⟨2706943694262472471930651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609258259016629962574201 2706943694262472471930651)
                      ·
                        rfl

theorem cell23_5271754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_5271754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271754 prefixEnd_5271754 := by exact prefixLift 5271754
  have htrace : WordTrace (prefixWord ++ tailWord_5271754) baseStart_5271754 baseEnd_5271754 := by
    simpa [prefixWord, tailWord_5271754, baseEnd_5271754] using wordTrace_append hprefix tailTrace_5271754
  have hstable : (prefixWord ++ tailWord_5271754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271754).length < 2 ^ (prefixWord ++ tailWord_5271754).sum := by decide
  have hdescent : baseEnd_5271754 < baseStart_5271754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271780 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_5271780 : Nat := 118140960795 + 5271780 * 2 ^ 59
def prefixEnd_5271780 : Nat := 4983230072969 + 3 ^ 40 * 5271780 * 2
def baseEnd_5271780 : Nat := 2706957044759489370205531

theorem tailTrace_5271780 : CollatzResearch.WordTrace tailWord_5271780 prefixEnd_5271780 2706957044759489370205531 := by
  unfold tailWord_5271780
  simp only [CollatzResearch.WordTrace]
  refine ⟨96138806420624441594358397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128185075227499255459144529 96138806420624441594358397)
  ·
    refine ⟨36052052407734165597884399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96138806420624441594358397 36052052407734165597884399)
    ·
      refine ⟨54078078611601248396826599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36052052407734165597884399 54078078611601248396826599)
      ·
        refine ⟨81117117917401872595239899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54078078611601248396826599 81117117917401872595239899)
        ·
          refine ⟨121675676876102808892859849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81117117917401872595239899 121675676876102808892859849)
          ·
            refine ⟨91256757657077106669644887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121675676876102808892859849 91256757657077106669644887)
            ·
              refine ⟨136885136485615660004467331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91256757657077106669644887 136885136485615660004467331)
              ·
                refine ⟨205327704728423490006700997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136885136485615660004467331 205327704728423490006700997)
                ·
                  refine ⟨38498944636579404376256437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205327704728423490006700997 38498944636579404376256437)
                  ·
                    refine ⟨3609276059679319160274041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38498944636579404376256437 3609276059679319160274041)
                    ·
                      refine ⟨2706957044759489370205531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609276059679319160274041 2706957044759489370205531)
                      ·
                        rfl

theorem cell23_5271780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_5271780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271780 prefixEnd_5271780 := by exact prefixLift 5271780
  have htrace : WordTrace (prefixWord ++ tailWord_5271780) baseStart_5271780 baseEnd_5271780 := by
    simpa [prefixWord, tailWord_5271780, baseEnd_5271780] using wordTrace_append hprefix tailTrace_5271780
  have hstable : (prefixWord ++ tailWord_5271780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271780).length < 2 ^ (prefixWord ++ tailWord_5271780).sum := by decide
  have hdescent : baseEnd_5271780 < baseStart_5271780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271947 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 4]
def baseStart_5271947 : Nat := 118140960795 + 5271947 * 2 ^ 59
def prefixEnd_5271947 : Nat := 4983230072969 + 3 ^ 40 * 5271947 * 2
def baseEnd_5271947 : Nat := 2707042796028790216817263

theorem tailTrace_5271947 : CollatzResearch.WordTrace tailWord_5271947 prefixEnd_5271947 2707042796028790216817263 := by
  unfold tailWord_5271947
  simp only [CollatzResearch.WordTrace]
  refine ⟨192283703831643870710046095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128189135887762580473364063 192283703831643870710046095)
  ·
    refine ⟨288425555747465806065069143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192283703831643870710046095 288425555747465806065069143)
    ·
      refine ⟨432638333621198709097603715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288425555747465806065069143 432638333621198709097603715)
      ·
        refine ⟨648957500431798063646405573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432638333621198709097603715 648957500431798063646405573)
        ·
          refine ⟨121679531330962136933701045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 648957500431798063646405573 121679531330962136933701045)
          ·
            refine ⟨11407456062277700337534473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121679531330962136933701045 11407456062277700337534473)
            ·
              refine ⟨8555592046708275253150855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11407456062277700337534473 8555592046708275253150855)
              ·
                refine ⟨12833388070062412879726283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8555592046708275253150855 12833388070062412879726283)
                ·
                  refine ⟨19250082105093619319589425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12833388070062412879726283 19250082105093619319589425)
                  ·
                    refine ⟨14437561578820214489692069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19250082105093619319589425 14437561578820214489692069)
                    ·
                      refine ⟨2707042796028790216817263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14437561578820214489692069 2707042796028790216817263)
                      ·
                        rfl

theorem cell23_5271947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 4].length) (baseStart_5271947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271947 prefixEnd_5271947 := by exact prefixLift 5271947
  have htrace : WordTrace (prefixWord ++ tailWord_5271947) baseStart_5271947 baseEnd_5271947 := by
    simpa [prefixWord, tailWord_5271947, baseEnd_5271947] using wordTrace_append hprefix tailTrace_5271947
  have hstable : (prefixWord ++ tailWord_5271947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271947).length < 2 ^ (prefixWord ++ tailWord_5271947).sum := by decide
  have hdescent : baseEnd_5271947 < baseStart_5271947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271967 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 3]
def baseStart_5271967 : Nat := 118140960795 + 5271967 * 2 ^ 59
def prefixEnd_5271967 : Nat := 4983230072969 + 3 ^ 40 * 5271967 * 2
def baseEnd_5271967 : Nat := 2707053065641880138567171

theorem tailTrace_5271967 : CollatzResearch.WordTrace tailWord_5271967 prefixEnd_5271967 2707053065641880138567171 := by
  unfold tailWord_5271967
  simp only [CollatzResearch.WordTrace]
  refine ⟨192284433291571414125774155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128189622194380942750516103 192284433291571414125774155)
  ·
    refine ⟨288426649937357121188661233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192284433291571414125774155 288426649937357121188661233)
    ·
      refine ⟨216319987453017840891495925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288426649937357121188661233 216319987453017840891495925)
      ·
        refine ⟨20279998823720422583577743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216319987453017840891495925 20279998823720422583577743)
        ·
          refine ⟨30419998235580633875366615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20279998823720422583577743 30419998235580633875366615)
          ·
            refine ⟨45629997353370950813049923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30419998235580633875366615 45629997353370950813049923)
            ·
              refine ⟨68444996030056426219574885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45629997353370950813049923 68444996030056426219574885)
              ·
                refine ⟨12833436755635579916170291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68444996030056426219574885 12833436755635579916170291)
                ·
                  refine ⟨19250155133453369874255437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12833436755635579916170291 19250155133453369874255437)
                  ·
                    refine ⟨7218808175045013702845789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19250155133453369874255437 7218808175045013702845789)
                    ·
                      refine ⟨2707053065641880138567171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7218808175045013702845789 2707053065641880138567171)
                      ·
                        rfl

theorem cell23_5271967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_5271967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271967 prefixEnd_5271967 := by exact prefixLift 5271967
  have htrace : WordTrace (prefixWord ++ tailWord_5271967) baseStart_5271967 baseEnd_5271967 := by
    simpa [prefixWord, tailWord_5271967, baseEnd_5271967] using wordTrace_append hprefix tailTrace_5271967
  have hstable : (prefixWord ++ tailWord_5271967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271967).length < 2 ^ (prefixWord ++ tailWord_5271967).sum := by decide
  have hdescent : baseEnd_5271967 < baseStart_5271967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271968 : List Nat := [2, 1, 1, 4, 1, 4, 2, 3, 1, 2, 2]
def baseStart_5271968 : Nat := 118140960795 + 5271968 * 2 ^ 59
def prefixEnd_5271968 : Nat := 4983230072969 + 3 ^ 40 * 5271968 * 2
def baseEnd_5271968 : Nat := 2707053579122534634654667

theorem tailTrace_5271968 : CollatzResearch.WordTrace tailWord_5271968 prefixEnd_5271968 2707053579122534634654667 := by
  unfold tailWord_5271968
  simp only [CollatzResearch.WordTrace]
  refine ⟨96142234882283895648280279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128189646509711860864373705 96142234882283895648280279)
  ·
    refine ⟨144213352323425843472420419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96142234882283895648280279 144213352323425843472420419)
    ·
      refine ⟨216320028485138765208630629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144213352323425843472420419 216320028485138765208630629)
      ·
        refine ⟨40560005340963518476618243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216320028485138765208630629 40560005340963518476618243)
        ·
          refine ⟨60840008011445277714927365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40560005340963518476618243 60840008011445277714927365)
          ·
            refine ⟨11407501502145989571548881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60840008011445277714927365 11407501502145989571548881)
            ·
              refine ⟨8555626126609492178661661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11407501502145989571548881 8555626126609492178661661)
              ·
                refine ⟨3208359797478559566998123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8555626126609492178661661 3208359797478559566998123)
                ·
                  refine ⟨4812539696217839350497185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208359797478559566998123 4812539696217839350497185)
                  ·
                    refine ⟨3609404772163379512872889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4812539696217839350497185 3609404772163379512872889)
                    ·
                      refine ⟨2707053579122534634654667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609404772163379512872889 2707053579122534634654667)
                      ·
                        rfl

theorem cell23_5271968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_5271968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271968 prefixEnd_5271968 := by exact prefixLift 5271968
  have htrace : WordTrace (prefixWord ++ tailWord_5271968) baseStart_5271968 baseEnd_5271968 := by
    simpa [prefixWord, tailWord_5271968, baseEnd_5271968] using wordTrace_append hprefix tailTrace_5271968
  have hstable : (prefixWord ++ tailWord_5271968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271968).length < 2 ^ (prefixWord ++ tailWord_5271968).sum := by decide
  have hdescent : baseEnd_5271968 < baseStart_5271968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271971 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 1, 2, 3]
def baseStart_5271971 : Nat := 118140960795 + 5271971 * 2 ^ 59
def prefixEnd_5271971 : Nat := 4983230072969 + 3 ^ 40 * 5271971 * 2
def baseEnd_5271971 : Nat := 2707055119564498122917153

theorem tailTrace_5271971 : CollatzResearch.WordTrace tailWord_5271971 prefixEnd_5271971 2707055119564498122917153 := by
  unfold tailWord_5271971
  simp only [CollatzResearch.WordTrace]
  refine ⟨192284579183556922808919767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128189719455704615205946511 192284579183556922808919767)
  ·
    refine ⟨288426868775335384213379651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192284579183556922808919767 288426868775335384213379651)
    ·
      refine ⟨432640303163003076320069477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288426868775335384213379651 432640303163003076320069477)
      ·
        refine ⟨81120056843063076810013027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 432640303163003076320069477 81120056843063076810013027)
        ·
          refine ⟨121680085264594615215019541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81120056843063076810013027 121680085264594615215019541)
          ·
            refine ⟨5703753996777872588204041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121680085264594615215019541 5703753996777872588204041)
            ·
              refine ⟨4277815497583404441153031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5703753996777872588204041 4277815497583404441153031)
              ·
                refine ⟨6416723246375106661729547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4277815497583404441153031 6416723246375106661729547)
                ·
                  refine ⟨9625084869562659992594321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6416723246375106661729547 9625084869562659992594321)
                  ·
                    refine ⟨7218813652171994994445741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9625084869562659992594321 7218813652171994994445741)
                    ·
                      refine ⟨2707055119564498122917153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7218813652171994994445741 2707055119564498122917153)
                      ·
                        rfl

theorem cell23_5271971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_5271971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271971 prefixEnd_5271971 := by exact prefixLift 5271971
  have htrace : WordTrace (prefixWord ++ tailWord_5271971) baseStart_5271971 baseEnd_5271971 := by
    simpa [prefixWord, tailWord_5271971, baseEnd_5271971] using wordTrace_append hprefix tailTrace_5271971
  have hstable : (prefixWord ++ tailWord_5271971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271971).length < 2 ^ (prefixWord ++ tailWord_5271971).sum := by decide
  have hdescent : baseEnd_5271971 < baseStart_5271971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5271978 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5271978 : Nat := 118140960795 + 5271978 * 2 ^ 59
def prefixEnd_5271978 : Nat := 4983230072969 + 3 ^ 40 * 5271978 * 2
def baseEnd_5271978 : Nat := 902352904643026531843207

theorem tailTrace_5271978 : CollatzResearch.WordTrace tailWord_5271978 prefixEnd_5271978 902352904643026531843207 := by
  unfold tailWord_5271978
  simp only [CollatzResearch.WordTrace]
  refine ⟨48071208623632890751106147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128189889663021042002949725 48071208623632890751106147)
  ·
    refine ⟨72106812935449336126659221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48071208623632890751106147 72106812935449336126659221)
    ·
      refine ⟨3380006856349187630937151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72106812935449336126659221 3380006856349187630937151)
      ·
        refine ⟨5070010284523781446405727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380006856349187630937151 5070010284523781446405727)
        ·
          refine ⟨7605015426785672169608591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5070010284523781446405727 7605015426785672169608591)
          ·
            refine ⟨11407523140178508254412887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7605015426785672169608591 11407523140178508254412887)
            ·
              refine ⟨17111284710267762381619331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11407523140178508254412887 17111284710267762381619331)
              ·
                refine ⟨25666927065401643572428997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17111284710267762381619331 25666927065401643572428997)
                ·
                  refine ⟨4812548824762808169830437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25666927065401643572428997 4812548824762808169830437)
                  ·
                    refine ⟨902352904643026531843207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4812548824762808169830437 902352904643026531843207)
                    ·
                      rfl

theorem cell23_5271978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5271978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5271978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5271978 prefixEnd_5271978 := by exact prefixLift 5271978
  have htrace : WordTrace (prefixWord ++ tailWord_5271978) baseStart_5271978 baseEnd_5271978 := by
    simpa [prefixWord, tailWord_5271978, baseEnd_5271978] using wordTrace_append hprefix tailTrace_5271978
  have hstable : (prefixWord ++ tailWord_5271978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5271978).length < 2 ^ (prefixWord ++ tailWord_5271978).sum := by decide
  have hdescent : baseEnd_5271978 < baseStart_5271978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5271978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272057 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 3]
def baseStart_5272057 : Nat := 118140960795 + 5272057 * 2 ^ 59
def prefixEnd_5272057 : Nat := 4983230072969 + 3 ^ 40 * 5272057 * 2
def baseEnd_5272057 : Nat := 2707099278900784786441757

theorem tailTrace_5272057 : CollatzResearch.WordTrace tailWord_5272057 prefixEnd_5272057 2707099278900784786441757 := by
  unfold tailWord_5272057
  simp only [CollatzResearch.WordTrace]
  refine ⟨192287715861245359496550425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128191810574163572997700283 192287715861245359496550425)
  ·
    refine ⟨144215786895934019622412819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192287715861245359496550425 144215786895934019622412819)
    ·
      refine ⟨216323680343901029433619229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144215786895934019622412819 216323680343901029433619229)
      ·
        refine ⟨81121380128962886037607211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216323680343901029433619229 81121380128962886037607211)
        ·
          refine ⟨121682070193444329056410817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81121380128962886037607211 121682070193444329056410817)
          ·
            refine ⟨91261552645083246792308113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121682070193444329056410817 91261552645083246792308113)
            ·
              refine ⟨68446164483812435094231085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91261552645083246792308113 68446164483812435094231085)
              ·
                refine ⟨25667311681429663160336657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68446164483812435094231085 25667311681429663160336657)
                ·
                  refine ⟨19250483761072247370252493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25667311681429663160336657 19250483761072247370252493)
                  ·
                    refine ⟨7218931410402092763844685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19250483761072247370252493 7218931410402092763844685)
                    ·
                      refine ⟨2707099278900784786441757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7218931410402092763844685 2707099278900784786441757)
                      ·
                        rfl

theorem cell23_5272057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_5272057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272057 prefixEnd_5272057 := by exact prefixLift 5272057
  have htrace : WordTrace (prefixWord ++ tailWord_5272057) baseStart_5272057 baseEnd_5272057 := by
    simpa [prefixWord, tailWord_5272057, baseEnd_5272057] using wordTrace_append hprefix tailTrace_5272057
  have hstable : (prefixWord ++ tailWord_5272057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272057).length < 2 ^ (prefixWord ++ tailWord_5272057).sum := by decide
  have hdescent : baseEnd_5272057 < baseStart_5272057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272104 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5272104 : Nat := 118140960795 + 5272104 * 2 ^ 59
def prefixEnd_5272104 : Nat := 4983230072969 + 3 ^ 40 * 5272104 * 2
def baseEnd_5272104 : Nat := 2707123412491546102554041

theorem tailTrace_5272104 : CollatzResearch.WordTrace tailWord_5272104 prefixEnd_5272104 2707123412491546102554041 := by
  unfold tailWord_5272104
  simp only [CollatzResearch.WordTrace]
  refine ⟨96144715046037543261755683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128192953394716724349007577 96144715046037543261755683)
  ·
    refine ⟨144217072569056314892633525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96144715046037543261755683 144217072569056314892633525)
    ·
      refine ⟨13520350553349029521184393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144217072569056314892633525 13520350553349029521184393)
      ·
        refine ⟨10140262915011772140888295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13520350553349029521184393 10140262915011772140888295)
        ·
          refine ⟨15210394372517658211332443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10140262915011772140888295 15210394372517658211332443)
          ·
            refine ⟨22815591558776487316998665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15210394372517658211332443 22815591558776487316998665)
            ·
              refine ⟨17111693669082365487748999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22815591558776487316998665 17111693669082365487748999)
              ·
                refine ⟨25667540503623548231623499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17111693669082365487748999 25667540503623548231623499)
                ·
                  refine ⟨38501310755435322347435249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25667540503623548231623499 38501310755435322347435249)
                  ·
                    refine ⟨28875983066576491760576437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38501310755435322347435249 28875983066576491760576437)
                    ·
                      refine ⟨2707123412491546102554041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28875983066576491760576437 2707123412491546102554041)
                      ·
                        rfl

theorem cell23_5272104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5272104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272104 prefixEnd_5272104 := by exact prefixLift 5272104
  have htrace : WordTrace (prefixWord ++ tailWord_5272104) baseStart_5272104 baseEnd_5272104 := by
    simpa [prefixWord, tailWord_5272104, baseEnd_5272104] using wordTrace_append hprefix tailTrace_5272104
  have hstable : (prefixWord ++ tailWord_5272104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272104).length < 2 ^ (prefixWord ++ tailWord_5272104).sum := by decide
  have hdescent : baseEnd_5272104 < baseStart_5272104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272107 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 7, 4]
def baseStart_5272107 : Nat := 118140960795 + 5272107 * 2 ^ 59
def prefixEnd_5272107 : Nat := 4983230072969 + 3 ^ 40 * 5272107 * 2
def baseEnd_5272107 : Nat := 902374984311169863605509

theorem tailTrace_5272107 : CollatzResearch.WordTrace tailWord_5272107 prefixEnd_5272107 902374984311169863605509 := by
  unfold tailWord_5272107
  simp only [CollatzResearch.WordTrace]
  refine ⟨192289539511064218035870575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128193026340709478690580383 192289539511064218035870575)
  ·
    refine ⟨288434309266596327053805863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192289539511064218035870575 288434309266596327053805863)
    ·
      refine ⟨432651463899894490580708795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288434309266596327053805863 432651463899894490580708795)
      ·
        refine ⟨648977195849841735871063193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432651463899894490580708795 648977195849841735871063193)
        ·
          refine ⟨486732896887381301903297395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648977195849841735871063193 486732896887381301903297395)
          ·
            refine ⟨730099345331071952854946093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486732896887381301903297395 730099345331071952854946093)
            ·
              refine ⟨273787254499151982320604785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 730099345331071952854946093 273787254499151982320604785)
              ·
                refine ⟨205340440874363986740453589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273787254499151982320604785 205340440874363986740453589)
                ·
                  refine ⟨4812666582992905939229381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 205340440874363986740453589 4812666582992905939229381)
                  ·
                    refine ⟨902374984311169863605509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4812666582992905939229381 902374984311169863605509)
                    ·
                      rfl

theorem cell23_5272107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 4].length) (baseStart_5272107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272107 prefixEnd_5272107 := by exact prefixLift 5272107
  have htrace : WordTrace (prefixWord ++ tailWord_5272107) baseStart_5272107 baseEnd_5272107 := by
    simpa [prefixWord, tailWord_5272107, baseEnd_5272107] using wordTrace_append hprefix tailTrace_5272107
  have hstable : (prefixWord ++ tailWord_5272107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272107).length < 2 ^ (prefixWord ++ tailWord_5272107).sum := by decide
  have hdescent : baseEnd_5272107 < baseStart_5272107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272114 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_5272114 : Nat := 118140960795 + 5272114 * 2 ^ 59
def prefixEnd_5272114 : Nat := 4983230072969 + 3 ^ 40 * 5272114 * 2
def baseEnd_5272114 : Nat := 2707128547298091063428995

theorem tailTrace_5272114 : CollatzResearch.WordTrace tailWord_5272114 prefixEnd_5272114 2707128547298091063428995 := by
  unfold tailWord_5272114
  simp only [CollatzResearch.WordTrace]
  refine ⟨48072448705509714557843849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128193196548025905487583597 48072448705509714557843849)
  ·
    refine ⟨36054336529132285918382887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48072448705509714557843849 36054336529132285918382887)
    ·
      refine ⟨54081504793698428877574331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36054336529132285918382887 54081504793698428877574331)
      ·
        refine ⟨81122257190547643316361497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54081504793698428877574331 81122257190547643316361497)
        ·
          refine ⟨60841692892910732487271123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81122257190547643316361497 60841692892910732487271123)
          ·
            refine ⟨91262539339366098730906685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60841692892910732487271123 91262539339366098730906685)
            ·
              refine ⟨34223452252262287024090007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91262539339366098730906685 34223452252262287024090007)
              ·
                refine ⟨51335178378393430536135011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34223452252262287024090007 51335178378393430536135011)
                ·
                  refine ⟨77002767567590145804202517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51335178378393430536135011 77002767567590145804202517)
                  ·
                    refine ⟨3609504729730788084571993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77002767567590145804202517 3609504729730788084571993)
                    ·
                      refine ⟨2707128547298091063428995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609504729730788084571993 2707128547298091063428995)
                      ·
                        rfl

theorem cell23_5272114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_5272114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272114 prefixEnd_5272114 := by exact prefixLift 5272114
  have htrace : WordTrace (prefixWord ++ tailWord_5272114) baseStart_5272114 baseEnd_5272114 := by
    simpa [prefixWord, tailWord_5272114, baseEnd_5272114] using wordTrace_append hprefix tailTrace_5272114
  have hstable : (prefixWord ++ tailWord_5272114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272114).length < 2 ^ (prefixWord ++ tailWord_5272114).sum := by decide
  have hdescent : baseEnd_5272114 < baseStart_5272114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272124 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_5272124 : Nat := 118140960795 + 5272124 * 2 ^ 59
def prefixEnd_5272124 : Nat := 4983230072969 + 3 ^ 40 * 5272124 * 2
def baseEnd_5272124 : Nat := 902377894034878674767983

theorem tailTrace_5272124 : CollatzResearch.WordTrace tailWord_5272124 prefixEnd_5272124 902377894034878674767983 := by
  unfold tailWord_5272124
  simp only [CollatzResearch.WordTrace]
  refine ⟨96145079776001314969619713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128193439701335086626159617 96145079776001314969619713)
  ·
    refine ⟨72108809832000986227214785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96145079776001314969619713 72108809832000986227214785)
    ·
      refine ⟨54081607374000739670411089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72108809832000986227214785 54081607374000739670411089)
      ·
        refine ⟨40561205530500554752808317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54081607374000739670411089 40561205530500554752808317)
        ·
          refine ⟨15210452073937708032303119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40561205530500554752808317 15210452073937708032303119)
          ·
            refine ⟨22815678110906562048454679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15210452073937708032303119 22815678110906562048454679)
            ·
              refine ⟨34223517166359843072682019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22815678110906562048454679 34223517166359843072682019)
              ·
                refine ⟨51335275749539764609023029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34223517166359843072682019 51335275749539764609023029)
                ·
                  refine ⟨4812682101519352932095909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51335275749539764609023029 4812682101519352932095909)
                  ·
                    refine ⟨902377894034878674767983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4812682101519352932095909 902377894034878674767983)
                    ·
                      rfl

theorem cell23_5272124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_5272124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272124 prefixEnd_5272124 := by exact prefixLift 5272124
  have htrace : WordTrace (prefixWord ++ tailWord_5272124) baseStart_5272124 baseEnd_5272124 := by
    simpa [prefixWord, tailWord_5272124, baseEnd_5272124] using wordTrace_append hprefix tailTrace_5272124
  have hstable : (prefixWord ++ tailWord_5272124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272124).length < 2 ^ (prefixWord ++ tailWord_5272124).sum := by decide
  have hdescent : baseEnd_5272124 < baseStart_5272124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272207 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_5272207 : Nat := 118140960795 + 5272207 * 2 ^ 59
def prefixEnd_5272207 : Nat := 4983230072969 + 3 ^ 40 * 5272207 * 2
def baseEnd_5272207 : Nat := 2707176300998959199566067

theorem tailTrace_5272207 : CollatzResearch.WordTrace tailWord_5272207 prefixEnd_5272207 2707176300998959199566067 := by
  unfold tailWord_5272207
  simp only [CollatzResearch.WordTrace]
  refine ⟨192293186810701935114510875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128195457873801290076340583 192293186810701935114510875)
  ·
    refine ⟨288439780216052902671766313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192293186810701935114510875 288439780216052902671766313)
    ·
      refine ⟨216329835162039677003824735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288439780216052902671766313 216329835162039677003824735)
      ·
        refine ⟨324494752743059515505737103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216329835162039677003824735 324494752743059515505737103)
        ·
          refine ⟨486742129114589273258605655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324494752743059515505737103 486742129114589273258605655)
          ·
            refine ⟨730113193671883909887908483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486742129114589273258605655 730113193671883909887908483)
            ·
              refine ⟨1095169790507825864831862725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730113193671883909887908483 1095169790507825864831862725)
              ·
                refine ⟨205344335720217349655974261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1095169790507825864831862725 205344335720217349655974261)
                ·
                  refine ⟨19251031473770376530247587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205344335720217349655974261 19251031473770376530247587)
                  ·
                    refine ⟨28876547210655564795371381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19251031473770376530247587 28876547210655564795371381)
                    ·
                      refine ⟨2707176300998959199566067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28876547210655564795371381 2707176300998959199566067)
                      ·
                        rfl

theorem cell23_5272207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_5272207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272207 prefixEnd_5272207 := by exact prefixLift 5272207
  have htrace : WordTrace (prefixWord ++ tailWord_5272207) baseStart_5272207 baseEnd_5272207 := by
    simpa [prefixWord, tailWord_5272207, baseEnd_5272207] using wordTrace_append hprefix tailTrace_5272207
  have hstable : (prefixWord ++ tailWord_5272207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272207).length < 2 ^ (prefixWord ++ tailWord_5272207).sum := by decide
  have hdescent : baseEnd_5272207 < baseStart_5272207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272215 : List Nat := [1, 1, 3, 3, 2, 1, 5, 2, 1, 1, 3]
def baseStart_5272215 : Nat := 118140960795 + 5272215 * 2 ^ 59
def prefixEnd_5272215 : Nat := 4983230072969 + 3 ^ 40 * 5272215 * 2
def baseEnd_5272215 : Nat := 2707180408844195168266031

theorem tailTrace_5272215 : CollatzResearch.WordTrace tailWord_5272215 prefixEnd_5272215 2707180408844195168266031 := by
  unfold tailWord_5272215
  simp only [CollatzResearch.WordTrace]
  refine ⟨192293478594672952480802099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128195652396448634987201399 192293478594672952480802099)
  ·
    refine ⟨288440217892009428721203149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192293478594672952480802099 288440217892009428721203149)
    ·
      refine ⟨108165081709503535770451181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288440217892009428721203149 108165081709503535770451181)
      ·
        refine ⟨40561905641063825913919193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108165081709503535770451181 40561905641063825913919193)
        ·
          refine ⟨30421429230797869435439395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40561905641063825913919193 30421429230797869435439395)
          ·
            refine ⟨45632143846196804153159093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30421429230797869435439395 45632143846196804153159093)
            ·
              refine ⟨4278013485580950389358665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45632143846196804153159093 4278013485580950389358665)
              ·
                refine ⟨3208510114185712792018999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4278013485580950389358665 3208510114185712792018999)
                ·
                  refine ⟨4812765171278569188028499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208510114185712792018999 4812765171278569188028499)
                  ·
                    refine ⟨7219147756917853782042749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4812765171278569188028499 7219147756917853782042749)
                    ·
                      refine ⟨2707180408844195168266031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7219147756917853782042749 2707180408844195168266031)
                      ·
                        rfl

theorem cell23_5272215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_5272215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272215 prefixEnd_5272215 := by exact prefixLift 5272215
  have htrace : WordTrace (prefixWord ++ tailWord_5272215) baseStart_5272215 baseEnd_5272215 := by
    simpa [prefixWord, tailWord_5272215, baseEnd_5272215] using wordTrace_append hprefix tailTrace_5272215
  have hstable : (prefixWord ++ tailWord_5272215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272215).length < 2 ^ (prefixWord ++ tailWord_5272215).sum := by decide
  have hdescent : baseEnd_5272215 < baseStart_5272215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272217 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_5272217 : Nat := 118140960795 + 5272217 * 2 ^ 59
def prefixEnd_5272217 : Nat := 4983230072969 + 3 ^ 40 * 5272217 * 2
def baseEnd_5272217 : Nat := 2707181435805504160441021

theorem tailTrace_5272217 : CollatzResearch.WordTrace tailWord_5272217 prefixEnd_5272217 2707181435805504160441021 := by
  unfold tailWord_5272217
  simp only [CollatzResearch.WordTrace]
  refine ⟨192293551540665706822374905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128195701027110471214916603 192293551540665706822374905)
  ·
    refine ⟨144220163655499280116781179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192293551540665706822374905 144220163655499280116781179)
    ·
      refine ⟨216330245483248920175171769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144220163655499280116781179 216330245483248920175171769)
      ·
        refine ⟨162247684112436690131378827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216330245483248920175171769 162247684112436690131378827)
        ·
          refine ⟨243371526168655035197068241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162247684112436690131378827 243371526168655035197068241)
          ·
            refine ⟨182528644626491276397801181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243371526168655035197068241 182528644626491276397801181)
            ·
              refine ⟨68448241734934228649175443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182528644626491276397801181 68448241734934228649175443)
              ·
                refine ⟨102672362602401342973763165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68448241734934228649175443 102672362602401342973763165)
                ·
                  refine ⟨38502135975900503615161187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102672362602401342973763165 38502135975900503615161187)
                  ·
                    refine ⟨57753203963850755422741781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38502135975900503615161187 57753203963850755422741781)
                    ·
                      refine ⟨2707181435805504160441021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57753203963850755422741781 2707181435805504160441021)
                      ·
                        rfl

theorem cell23_5272217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_5272217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272217 prefixEnd_5272217 := by exact prefixLift 5272217
  have htrace : WordTrace (prefixWord ++ tailWord_5272217) baseStart_5272217 baseEnd_5272217 := by
    simpa [prefixWord, tailWord_5272217, baseEnd_5272217] using wordTrace_append hprefix tailTrace_5272217
  have hstable : (prefixWord ++ tailWord_5272217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272217).length < 2 ^ (prefixWord ++ tailWord_5272217).sum := by decide
  have hdescent : baseEnd_5272217 < baseStart_5272217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272238 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5272238 : Nat := 118140960795 + 5272238 * 2 ^ 59
def prefixEnd_5272238 : Nat := 4983230072969 + 3 ^ 40 * 5272238 * 2
def baseEnd_5272238 : Nat := 2707192218899248578278425

theorem tailTrace_5272238 : CollatzResearch.WordTrace tailWord_5272238 prefixEnd_5272238 2707192218899248578278425 := by
  unfold tailWord_5272238
  simp only [CollatzResearch.WordTrace]
  refine ⟨24036789684198703426111171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128196211649059751605926245 24036789684198703426111171)
  ·
    refine ⟨36055184526298055139166757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24036789684198703426111171 36055184526298055139166757)
    ·
      refine ⟨6760347098680885338593767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36055184526298055139166757 6760347098680885338593767)
      ·
        refine ⟨10140520648021328007890651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760347098680885338593767 10140520648021328007890651)
        ·
          refine ⟨15210780972031992011835977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10140520648021328007890651 15210780972031992011835977)
          ·
            refine ⟨11408085729023994008876983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15210780972031992011835977 11408085729023994008876983)
            ·
              refine ⟨17112128593535991013315475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11408085729023994008876983 17112128593535991013315475)
              ·
                refine ⟨25668192890303986519973213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17112128593535991013315475 25668192890303986519973213)
                ·
                  refine ⟨9625572333863994944989955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25668192890303986519973213 9625572333863994944989955)
                  ·
                    refine ⟨14438358500795992417484933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9625572333863994944989955 14438358500795992417484933)
                    ·
                      refine ⟨2707192218899248578278425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14438358500795992417484933 2707192218899248578278425)
                      ·
                        rfl

theorem cell23_5272238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5272238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272238 prefixEnd_5272238 := by exact prefixLift 5272238
  have htrace : WordTrace (prefixWord ++ tailWord_5272238) baseStart_5272238 baseEnd_5272238 := by
    simpa [prefixWord, tailWord_5272238, baseEnd_5272238] using wordTrace_append hprefix tailTrace_5272238
  have hstable : (prefixWord ++ tailWord_5272238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272238).length < 2 ^ (prefixWord ++ tailWord_5272238).sum := by decide
  have hdescent : baseEnd_5272238 < baseStart_5272238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272267 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 7]
def baseStart_5272267 : Nat := 118140960795 + 5272267 * 2 ^ 59
def prefixEnd_5272267 : Nat := 4983230072969 + 3 ^ 40 * 5272267 * 2
def baseEnd_5272267 : Nat := 2707207109838228964815791

theorem tailTrace_5272267 : CollatzResearch.WordTrace tailWord_5272267 prefixEnd_5272267 2707207109838228964815791 := by
  unfold tailWord_5272267
  simp only [CollatzResearch.WordTrace]
  refine ⟨192295375190484565361695055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128196916793656376907796703 192295375190484565361695055)
  ·
    refine ⟨288443062785726848042542583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192295375190484565361695055 288443062785726848042542583)
    ·
      refine ⟨432664594178590272063813875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288443062785726848042542583 432664594178590272063813875)
      ·
        refine ⟨648996891267885408095720813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432664594178590272063813875 648996891267885408095720813)
        ·
          refine ⟨243373834225457028035895305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 648996891267885408095720813 243373834225457028035895305)
          ·
            refine ⟨182530375669092771026921479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243373834225457028035895305 182530375669092771026921479)
            ·
              refine ⟨273795563503639156540382219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182530375669092771026921479 273795563503639156540382219)
              ·
                refine ⟨410693345255458734810573329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273795563503639156540382219 410693345255458734810573329)
                ·
                  refine ⟨308020008941594051107929997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410693345255458734810573329 308020008941594051107929997)
                  ·
                    refine ⟨115507503353097769165473749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 308020008941594051107929997 115507503353097769165473749)
                    ·
                      refine ⟨2707207109838228964815791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115507503353097769165473749 2707207109838228964815791)
                      ·
                        rfl

theorem cell23_5272267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_5272267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272267 prefixEnd_5272267 := by exact prefixLift 5272267
  have htrace : WordTrace (prefixWord ++ tailWord_5272267) baseStart_5272267 baseEnd_5272267 := by
    simpa [prefixWord, tailWord_5272267, baseEnd_5272267] using wordTrace_append hprefix tailTrace_5272267
  have hstable : (prefixWord ++ tailWord_5272267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272267).length < 2 ^ (prefixWord ++ tailWord_5272267).sum := by decide
  have hdescent : baseEnd_5272267 < baseStart_5272267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272281 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 5, 3, 2]
def baseStart_5272281 : Nat := 118140960795 + 5272281 * 2 ^ 59
def prefixEnd_5272281 : Nat := 4983230072969 + 3 ^ 40 * 5272281 * 2
def baseEnd_5272281 : Nat := 2707214298567391910040727

theorem tailTrace_5272281 : CollatzResearch.WordTrace tailWord_5272281 prefixEnd_5272281 2707214298567391910040727 := by
  unfold tailWord_5272281
  simp only [CollatzResearch.WordTrace]
  refine ⟨192295885812433845752704697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128197257208289230501803131 192295885812433845752704697)
  ·
    refine ⟨144221914359325384314528523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192295885812433845752704697 144221914359325384314528523)
    ·
      refine ⟨216332871538988076471792785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144221914359325384314528523 216332871538988076471792785)
      ·
        refine ⟨162249653654241057353844589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216332871538988076471792785 162249653654241057353844589)
        ·
          refine ⟨60843620120340396507691721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162249653654241057353844589 60843620120340396507691721)
          ·
            refine ⟨45632715090255297380768791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60843620120340396507691721 45632715090255297380768791)
            ·
              refine ⟨68449072635382946071153187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45632715090255297380768791 68449072635382946071153187)
              ·
                refine ⟨102673608953074419106729781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68449072635382946071153187 102673608953074419106729781)
                ·
                  refine ⟨9625650839350726791255917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102673608953074419106729781 9625650839350726791255917)
                  ·
                    refine ⟨3609619064756522546720969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9625650839350726791255917 3609619064756522546720969)
                    ·
                      refine ⟨2707214298567391910040727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609619064756522546720969 2707214298567391910040727)
                      ·
                        rfl

theorem cell23_5272281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_5272281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272281 prefixEnd_5272281 := by exact prefixLift 5272281
  have htrace : WordTrace (prefixWord ++ tailWord_5272281) baseStart_5272281 baseEnd_5272281 := by
    simpa [prefixWord, tailWord_5272281, baseEnd_5272281] using wordTrace_append hprefix tailTrace_5272281
  have hstable : (prefixWord ++ tailWord_5272281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272281).length < 2 ^ (prefixWord ++ tailWord_5272281).sum := by decide
  have hdescent : baseEnd_5272281 < baseStart_5272281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272298 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_5272298 : Nat := 118140960795 + 5272298 * 2 ^ 59
def prefixEnd_5272298 : Nat := 4983230072969 + 3 ^ 40 * 5272298 * 2
def baseEnd_5272298 : Nat := 2707223027738518343528149

theorem tailTrace_5272298 : CollatzResearch.WordTrace tailWord_5272298 prefixEnd_5272298 2707223027738518343528149 := by
  unfold tailWord_5272298
  simp only [CollatzResearch.WordTrace]
  refine ⟨48074126463343064414018387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128197670568914838437382365 48074126463343064414018387)
  ·
    refine ⟨72111189695014596621027581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48074126463343064414018387 72111189695014596621027581)
    ·
      refine ⟨27041696135630473732885343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72111189695014596621027581 27041696135630473732885343)
      ·
        refine ⟨40562544203445710599328015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27041696135630473732885343 40562544203445710599328015)
        ·
          refine ⟨60843816305168565898992023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40562544203445710599328015 60843816305168565898992023)
          ·
            refine ⟨91265724457752848848488035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60843816305168565898992023 91265724457752848848488035)
            ·
              refine ⟨136898586686629273272732053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91265724457752848848488035 136898586686629273272732053)
              ·
                refine ⟨6417121250935747184659315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136898586686629273272732053 6417121250935747184659315)
                ·
                  refine ⟨9625681876403620776988973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6417121250935747184659315 9625681876403620776988973)
                  ·
                    refine ⟨3609630703651357791370865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9625681876403620776988973 3609630703651357791370865)
                    ·
                      refine ⟨2707223027738518343528149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609630703651357791370865 2707223027738518343528149)
                      ·
                        rfl

theorem cell23_5272298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_5272298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272298 prefixEnd_5272298 := by exact prefixLift 5272298
  have htrace : WordTrace (prefixWord ++ tailWord_5272298) baseStart_5272298 baseEnd_5272298 := by
    simpa [prefixWord, tailWord_5272298, baseEnd_5272298] using wordTrace_append hprefix tailTrace_5272298
  have hstable : (prefixWord ++ tailWord_5272298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272298).length < 2 ^ (prefixWord ++ tailWord_5272298).sum := by decide
  have hdescent : baseEnd_5272298 < baseStart_5272298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272314 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_5272314 : Nat := 118140960795 + 5272314 * 2 ^ 59
def prefixEnd_5272314 : Nat := 4983230072969 + 3 ^ 40 * 5272314 * 2
def baseEnd_5272314 : Nat := 2707231243428990280928075

theorem tailTrace_5272314 : CollatzResearch.WordTrace tailWord_5272314 prefixEnd_5272314 2707231243428990280928075 := by
  unfold tailWord_5272314
  simp only [CollatzResearch.WordTrace]
  refine ⟨48074272355328573097163999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128198059614209528259103997 48074272355328573097163999)
  ·
    refine ⟨72111408532992859645745999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48074272355328573097163999 72111408532992859645745999)
    ·
      refine ⟨108167112799489289468618999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72111408532992859645745999 108167112799489289468618999)
      ·
        refine ⟨162250669199233934202928499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108167112799489289468618999 162250669199233934202928499)
        ·
          refine ⟨243376003798850901304392749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162250669199233934202928499 243376003798850901304392749)
          ·
            refine ⟨91266001424569087989147281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243376003798850901304392749 91266001424569087989147281)
            ·
              refine ⟨68449501068426815991860461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91266001424569087989147281 68449501068426815991860461)
              ·
                refine ⟨25668562900660055996947673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68449501068426815991860461 25668562900660055996947673)
                ·
                  refine ⟨19251422175495041997710755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25668562900660055996947673 19251422175495041997710755)
                  ·
                    refine ⟨28877133263242562996566133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19251422175495041997710755 28877133263242562996566133)
                    ·
                      refine ⟨2707231243428990280928075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28877133263242562996566133 2707231243428990280928075)
                      ·
                        rfl

theorem cell23_5272314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_5272314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272314 prefixEnd_5272314 := by exact prefixLift 5272314
  have htrace : WordTrace (prefixWord ++ tailWord_5272314) baseStart_5272314 baseEnd_5272314 := by
    simpa [prefixWord, tailWord_5272314, baseEnd_5272314] using wordTrace_append hprefix tailTrace_5272314
  have hstable : (prefixWord ++ tailWord_5272314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272314).length < 2 ^ (prefixWord ++ tailWord_5272314).sum := by decide
  have hdescent : baseEnd_5272314 < baseStart_5272314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272322 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_5272322 : Nat := 118140960795 + 5272322 * 2 ^ 59
def prefixEnd_5272322 : Nat := 4983230072969 + 3 ^ 40 * 5272322 * 2
def baseEnd_5272322 : Nat := 2707235351274226249628039

theorem tailTrace_5272322 : CollatzResearch.WordTrace tailWord_5272322 prefixEnd_5272322 2707235351274226249628039 := by
  unfold tailWord_5272322
  simp only [CollatzResearch.WordTrace]
  refine ⟨48074345301321327438736805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128198254136856873169964813 48074345301321327438736805)
  ·
    refine ⟨9013939743997748894763151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48074345301321327438736805 9013939743997748894763151)
    ·
      refine ⟨13520909615996623342144727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9013939743997748894763151 13520909615996623342144727)
      ·
        refine ⟨20281364423994935013217091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13520909615996623342144727 20281364423994935013217091)
        ·
          refine ⟨30422046635992402519825637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20281364423994935013217091 30422046635992402519825637)
          ·
            refine ⟨5704133744248575472467307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30422046635992402519825637 5704133744248575472467307)
            ·
              refine ⟨8556200616372863208700961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5704133744248575472467307 8556200616372863208700961)
              ·
                refine ⟨6417150462279647406525721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8556200616372863208700961 6417150462279647406525721)
                ·
                  refine ⟨4812862846709735554894291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6417150462279647406525721 4812862846709735554894291)
                  ·
                    refine ⟨7219294270064603332341437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4812862846709735554894291 7219294270064603332341437)
                    ·
                      refine ⟨2707235351274226249628039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7219294270064603332341437 2707235351274226249628039)
                      ·
                        rfl

theorem cell23_5272322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_5272322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272322 prefixEnd_5272322 := by exact prefixLift 5272322
  have htrace : WordTrace (prefixWord ++ tailWord_5272322) baseStart_5272322 baseEnd_5272322 := by
    simpa [prefixWord, tailWord_5272322, baseEnd_5272322] using wordTrace_append hprefix tailTrace_5272322
  have hstable : (prefixWord ++ tailWord_5272322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272322).length < 2 ^ (prefixWord ++ tailWord_5272322).sum := by decide
  have hdescent : baseEnd_5272322 < baseStart_5272322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272364 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_5272364 : Nat := 118140960795 + 5272364 * 2 ^ 59
def prefixEnd_5272364 : Nat := 4983230072969 + 3 ^ 40 * 5272364 * 2
def baseEnd_5272364 : Nat := 902418972487238361767615

theorem tailTrace_5272364 : CollatzResearch.WordTrace tailWord_5272364 prefixEnd_5272364 902418972487238361767615 := by
  unfold tailWord_5272364
  simp only [CollatzResearch.WordTrace]
  refine ⟨96149456535566575463988073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128199275380755433951984097 96149456535566575463988073)
  ·
    refine ⟨72112092401674931597991055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96149456535566575463988073 72112092401674931597991055)
    ·
      refine ⟨108168138602512397396986583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72112092401674931597991055 108168138602512397396986583)
      ·
        refine ⟨162252207903768596095479875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108168138602512397396986583 162252207903768596095479875)
        ·
          refine ⟨243378311855652894143219813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162252207903768596095479875 243378311855652894143219813)
          ·
            refine ⟨45633433472934917651853715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243378311855652894143219813 45633433472934917651853715)
            ·
              refine ⟨68450150209402376477780573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45633433472934917651853715 68450150209402376477780573)
              ·
                refine ⟨25668806328525891179167715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68450150209402376477780573 25668806328525891179167715)
                ·
                  refine ⟨38503209492788836768751573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25668806328525891179167715 38503209492788836768751573)
                  ·
                    refine ⟨902418972487238361767615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38503209492788836768751573 902418972487238361767615)
                    ·
                      rfl

theorem cell23_5272364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_5272364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272364 prefixEnd_5272364 := by exact prefixLift 5272364
  have htrace : WordTrace (prefixWord ++ tailWord_5272364) baseStart_5272364 baseEnd_5272364 := by
    simpa [prefixWord, tailWord_5272364, baseEnd_5272364] using wordTrace_append hprefix tailTrace_5272364
  have hstable : (prefixWord ++ tailWord_5272364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272364).length < 2 ^ (prefixWord ++ tailWord_5272364).sum := by decide
  have hdescent : baseEnd_5272364 < baseStart_5272364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272365 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5272365 : Nat := 118140960795 + 5272365 * 2 ^ 59
def prefixEnd_5272365 : Nat := 4983230072969 + 3 ^ 40 * 5272365 * 2
def baseEnd_5272365 : Nat := 2707257430942369581390341

theorem tailTrace_5272365 : CollatzResearch.WordTrace tailWord_5272365 prefixEnd_5272365 2707257430942369581390341 := by
  unfold tailWord_5272365
  simp only [CollatzResearch.WordTrace]
  refine ⟨192298949544129528098762549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128199299696086352065841699 192298949544129528098762549)
  ·
    refine ⟨18028026519762143259258989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192298949544129528098762549 18028026519762143259258989)
    ·
      refine ⟨6760509944910803722222121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18028026519762143259258989 6760509944910803722222121)
      ·
        refine ⟨5070382458683102791666591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6760509944910803722222121 5070382458683102791666591)
        ·
          refine ⟨7605573688024654187499887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5070382458683102791666591 7605573688024654187499887)
          ·
            refine ⟨11408360532036981281249831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7605573688024654187499887 11408360532036981281249831)
            ·
              refine ⟨17112540798055471921874747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11408360532036981281249831 17112540798055471921874747)
              ·
                refine ⟨25668811197083207882812121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17112540798055471921874747 25668811197083207882812121)
                ·
                  refine ⟨19251608397812405912109091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25668811197083207882812121 19251608397812405912109091)
                  ·
                    refine ⟨28877412596718608868163637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19251608397812405912109091 28877412596718608868163637)
                    ·
                      refine ⟨2707257430942369581390341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28877412596718608868163637 2707257430942369581390341)
                      ·
                        rfl

theorem cell23_5272365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5272365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272365 prefixEnd_5272365 := by exact prefixLift 5272365
  have htrace : WordTrace (prefixWord ++ tailWord_5272365) baseStart_5272365 baseEnd_5272365 := by
    simpa [prefixWord, tailWord_5272365, baseEnd_5272365] using wordTrace_append hprefix tailTrace_5272365
  have hstable : (prefixWord ++ tailWord_5272365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272365).length < 2 ^ (prefixWord ++ tailWord_5272365).sum := by decide
  have hdescent : baseEnd_5272365 < baseStart_5272365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272385 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 7]
def baseStart_5272385 : Nat := 118140960795 + 5272385 * 2 ^ 59
def prefixEnd_5272385 : Nat := 4983230072969 + 3 ^ 40 * 5272385 * 2
def baseEnd_5272385 : Nat := 300807522283939944793361

theorem tailTrace_5272385 : CollatzResearch.WordTrace tailWord_5272385 prefixEnd_5272385 300807522283939944793361 := by
  unfold tailWord_5272385
  simp only [CollatzResearch.WordTrace]
  refine ⟨192299679004057071514490609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128199786002704714342993739 192299679004057071514490609)
  ·
    refine ⟨144224759253042803635867957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192299679004057071514490609 144224759253042803635867957)
    ·
      refine ⟨13521071179972762840862621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144224759253042803635867957 13521071179972762840862621)
      ·
        refine ⟨5070401692489786065323483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13521071179972762840862621 5070401692489786065323483)
        ·
          refine ⟨7605602538734679097985225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5070401692489786065323483 7605602538734679097985225)
          ·
            refine ⟨5704201904051009323488919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7605602538734679097985225 5704201904051009323488919)
            ·
              refine ⟨8556302856076513985233379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5704201904051009323488919 8556302856076513985233379)
              ·
                refine ⟨12834454284114770977850069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8556302856076513985233379 12834454284114770977850069)
                ·
                  refine ⟨300807522283939944793361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12834454284114770977850069 300807522283939944793361)
                  ·
                    rfl

theorem cell23_5272385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 7].length) (baseStart_5272385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272385 prefixEnd_5272385 := by exact prefixLift 5272385
  have htrace : WordTrace (prefixWord ++ tailWord_5272385) baseStart_5272385 baseEnd_5272385 := by
    simpa [prefixWord, tailWord_5272385, baseEnd_5272385] using wordTrace_append hprefix tailTrace_5272385
  have hstable : (prefixWord ++ tailWord_5272385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272385).length < 2 ^ (prefixWord ++ tailWord_5272385).sum := by decide
  have hdescent : baseEnd_5272385 < baseStart_5272385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272394 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_5272394 : Nat := 118140960795 + 5272394 * 2 ^ 59
def prefixEnd_5272394 : Nat := 4983230072969 + 3 ^ 40 * 5272394 * 2
def baseEnd_5272394 : Nat := 902424107293783322642569

theorem tailTrace_5272394 : CollatzResearch.WordTrace tailWord_5272394 prefixEnd_5272394 902424107293783322642569 := by
  unfold tailWord_5272394
  simp only [CollatzResearch.WordTrace]
  refine ⟨48075001815256116512892059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128200004840682977367712157 48075001815256116512892059)
  ·
    refine ⟨72112502722884174769338089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48075001815256116512892059 72112502722884174769338089)
    ·
      refine ⟨54084377042163131077003567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72112502722884174769338089 54084377042163131077003567)
      ·
        refine ⟨81126565563244696615505351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54084377042163131077003567 81126565563244696615505351)
        ·
          refine ⟨121689848344867044923258027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81126565563244696615505351 121689848344867044923258027)
          ·
            refine ⟨182534772517300567384887041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121689848344867044923258027 182534772517300567384887041)
            ·
              refine ⟨136901079387975425538665281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182534772517300567384887041 136901079387975425538665281)
              ·
                refine ⟨102675809540981569153998961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136901079387975425538665281 102675809540981569153998961)
                ·
                  refine ⟨77006857155736176865499221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102675809540981569153998961 77006857155736176865499221)
                  ·
                    refine ⟨902424107293783322642569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77006857155736176865499221 902424107293783322642569)
                    ·
                      rfl

theorem cell23_5272394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_5272394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272394 prefixEnd_5272394 := by exact prefixLift 5272394
  have htrace : WordTrace (prefixWord ++ tailWord_5272394) baseStart_5272394 baseEnd_5272394 := by
    simpa [prefixWord, tailWord_5272394, baseEnd_5272394] using wordTrace_append hprefix tailTrace_5272394
  have hstable : (prefixWord ++ tailWord_5272394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272394).length < 2 ^ (prefixWord ++ tailWord_5272394).sum := by decide
  have hdescent : baseEnd_5272394 < baseStart_5272394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272421 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_5272421 : Nat := 118140960795 + 5272421 * 2 ^ 59
def prefixEnd_5272421 : Nat := 4983230072969 + 3 ^ 40 * 5272421 * 2
def baseEnd_5272421 : Nat := 2707286185859021362290083

theorem tailTrace_5272421 : CollatzResearch.WordTrace tailWord_5272421 prefixEnd_5272421 2707286185859021362290083 := by
  unfold tailWord_5272421
  simp only [CollatzResearch.WordTrace]
  refine ⟨192300992031926649662801117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128200661354617766441867411 192300992031926649662801117)
  ·
    refine ⟨72112872011972493623550419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192300992031926649662801117 72112872011972493623550419)
    ·
      refine ⟨108169308017958740435325629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72112872011972493623550419 108169308017958740435325629)
      ·
        refine ⟨40563490506734527663247111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108169308017958740435325629 40563490506734527663247111)
        ·
          refine ⟨60845235760101791494870667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40563490506734527663247111 60845235760101791494870667)
          ·
            refine ⟨91267853640152687242306001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60845235760101791494870667 91267853640152687242306001)
            ·
              refine ⟨68450890230114515431729501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91267853640152687242306001 68450890230114515431729501)
              ·
                refine ⟨25669083836292943286898563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68450890230114515431729501 25669083836292943286898563)
                ·
                  refine ⟨38503625754439414930347845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25669083836292943286898563 38503625754439414930347845)
                  ·
                    refine ⟨7219429828957390299440221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38503625754439414930347845 7219429828957390299440221)
                    ·
                      refine ⟨2707286185859021362290083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7219429828957390299440221 2707286185859021362290083)
                      ·
                        rfl

theorem cell23_5272421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_5272421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272421 prefixEnd_5272421 := by exact prefixLift 5272421
  have htrace : WordTrace (prefixWord ++ tailWord_5272421) baseStart_5272421 baseEnd_5272421 := by
    simpa [prefixWord, tailWord_5272421, baseEnd_5272421] using wordTrace_append hprefix tailTrace_5272421
  have hstable : (prefixWord ++ tailWord_5272421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272421).length < 2 ^ (prefixWord ++ tailWord_5272421).sum := by decide
  have hdescent : baseEnd_5272421 < baseStart_5272421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272441 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 6]
def baseStart_5272441 : Nat := 118140960795 + 5272441 * 2 ^ 59
def prefixEnd_5272441 : Nat := 4983230072969 + 3 ^ 40 * 5272441 * 2
def baseEnd_5272441 : Nat := 300810717274679031559999

theorem tailTrace_5272441 : CollatzResearch.WordTrace tailWord_5272441 prefixEnd_5272441 300810717274679031559999 := by
  unfold tailWord_5272441
  simp only [CollatzResearch.WordTrace]
  refine ⟨192301721491854193078529177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128201147661236128719019451 192301721491854193078529177)
  ·
    refine ⟨144226291118890644808896883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192301721491854193078529177 144226291118890644808896883)
    ·
      refine ⟨216339436678335967213345325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144226291118890644808896883 216339436678335967213345325)
      ·
        refine ⟨81127288754375987705004497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216339436678335967213345325 81127288754375987705004497)
        ·
          refine ⟨60845466565781990778753373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81127288754375987705004497 60845466565781990778753373)
          ·
            refine ⟨22817049962168246542032515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60845466565781990778753373 22817049962168246542032515)
            ·
              refine ⟨34225574943252369813048773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22817049962168246542032515 34225574943252369813048773)
              ·
                refine ⟨6417295301859819339946645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34225574943252369813048773 6417295301859819339946645)
                ·
                  refine ⟨300810717274679031559999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6417295301859819339946645 300810717274679031559999)
                  ·
                    rfl

theorem cell23_5272441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 6].length) (baseStart_5272441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272441 prefixEnd_5272441 := by exact prefixLift 5272441
  have htrace : WordTrace (prefixWord ++ tailWord_5272441) baseStart_5272441 baseEnd_5272441 := by
    simpa [prefixWord, tailWord_5272441, baseEnd_5272441] using wordTrace_append hprefix tailTrace_5272441
  have hstable : (prefixWord ++ tailWord_5272441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272441).length < 2 ^ (prefixWord ++ tailWord_5272441).sum := by decide
  have hdescent : baseEnd_5272441 < baseStart_5272441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272458 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 6]
def baseStart_5272458 : Nat := 118140960795 + 5272458 * 2 ^ 59
def prefixEnd_5272458 : Nat := 4983230072969 + 3 ^ 40 * 5272458 * 2
def baseEnd_5272458 : Nat := 300811687182581968614157

theorem tailTrace_5272458 : CollatzResearch.WordTrace tailWord_5272458 prefixEnd_5272458 300811687182581968614157 := by
  unfold tailWord_5272458
  simp only [CollatzResearch.WordTrace]
  refine ⟨48075585383198151245474507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128201561021861736654598685 48075585383198151245474507)
  ·
    refine ⟨72113378074797226868211761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48075585383198151245474507 72113378074797226868211761)
    ·
      refine ⟨54085033556097920151158821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72113378074797226868211761 54085033556097920151158821)
      ·
        refine ⟨10140943791768360028342279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54085033556097920151158821 10140943791768360028342279)
        ·
          refine ⟨15211415687652540042513419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10140943791768360028342279 15211415687652540042513419)
          ·
            refine ⟨22817123531478810063770129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15211415687652540042513419 22817123531478810063770129)
            ·
              refine ⟨17112842648609107547827597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22817123531478810063770129 17112842648609107547827597)
              ·
                refine ⟨6417315993228415330435349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17112842648609107547827597 6417315993228415330435349)
                ·
                  refine ⟨300811687182581968614157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6417315993228415330435349 300811687182581968614157)
                  ·
                    rfl

theorem cell23_5272458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_5272458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272458 prefixEnd_5272458 := by exact prefixLift 5272458
  have htrace : WordTrace (prefixWord ++ tailWord_5272458) baseStart_5272458 baseEnd_5272458 := by
    simpa [prefixWord, tailWord_5272458, baseEnd_5272458] using wordTrace_append hprefix tailTrace_5272458
  have hstable : (prefixWord ++ tailWord_5272458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272458).length < 2 ^ (prefixWord ++ tailWord_5272458).sum := by decide
  have hdescent : baseEnd_5272458 < baseStart_5272458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272471 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 3, 5]
def baseStart_5272471 : Nat := 118140960795 + 5272471 * 2 ^ 59
def prefixEnd_5272471 : Nat := 4983230072969 + 3 ^ 40 * 5272471 * 2
def baseEnd_5272471 : Nat := 902437286630582055554951

theorem tailTrace_5272471 : CollatzResearch.WordTrace tailWord_5272471 prefixEnd_5272471 902437286630582055554951 := by
  unfold tailWord_5272471
  simp only [CollatzResearch.WordTrace]
  refine ⟨192302815681745508202121267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128201877121163672134747511 192302815681745508202121267)
  ·
    refine ⟨288454223522618262303181901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192302815681745508202121267 288454223522618262303181901)
    ·
      refine ⟨108170333820981848363693213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288454223522618262303181901 108170333820981848363693213)
      ·
        refine ⟨40563875182868193136384955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108170333820981848363693213 40563875182868193136384955)
        ·
          refine ⟨60845812774302289704577433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40563875182868193136384955 60845812774302289704577433)
          ·
            refine ⟨45634359580726717278433075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60845812774302289704577433 45634359580726717278433075)
            ·
              refine ⟨68451539371090075917649613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45634359580726717278433075 68451539371090075917649613)
              ·
                refine ⟨25669327264158778469118605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68451539371090075917649613 25669327264158778469118605)
                ·
                  refine ⟨9625997724059541925919477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25669327264158778469118605 9625997724059541925919477)
                  ·
                    refine ⟨902437286630582055554951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9625997724059541925919477 902437286630582055554951)
                    ·
                      rfl

theorem cell23_5272471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_5272471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272471 prefixEnd_5272471 := by exact prefixLift 5272471
  have htrace : WordTrace (prefixWord ++ tailWord_5272471) baseStart_5272471 baseEnd_5272471 := by
    simpa [prefixWord, tailWord_5272471, baseEnd_5272471] using wordTrace_append hprefix tailTrace_5272471
  have hstable : (prefixWord ++ tailWord_5272471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272471).length < 2 ^ (prefixWord ++ tailWord_5272471).sum := by decide
  have hdescent : baseEnd_5272471 < baseStart_5272471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272511 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 3]
def baseStart_5272511 : Nat := 118140960795 + 5272511 * 2 ^ 59
def prefixEnd_5272511 : Nat := 4983230072969 + 3 ^ 40 * 5272511 * 2
def baseEnd_5272511 : Nat := 2707332399117926010164669

theorem tailTrace_5272511 : CollatzResearch.WordTrace tailWord_5272511 prefixEnd_5272511 2707332399117926010164669 := by
  unfold tailWord_5272511
  simp only [CollatzResearch.WordTrace]
  refine ⟨192304274601600595033577387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128202849734400396689051591 192304274601600595033577387)
  ·
    refine ⟨288456411902400892550366081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192304274601600595033577387 288456411902400892550366081)
    ·
      refine ⟨216342308926800669412774561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288456411902400892550366081 216342308926800669412774561)
      ·
        refine ⟨162256731695100502059580921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216342308926800669412774561 162256731695100502059580921)
        ·
          refine ⟨121692548771325376544685691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162256731695100502059580921 121692548771325376544685691)
          ·
            refine ⟨182538823156988064817028537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121692548771325376544685691 182538823156988064817028537)
            ·
              refine ⟨136904117367741048612771403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182538823156988064817028537 136904117367741048612771403)
              ·
                refine ⟨205356176051611572919157105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136904117367741048612771403 205356176051611572919157105)
                ·
                  refine ⟨154017132038708679689367829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205356176051611572919157105 154017132038708679689367829)
                  ·
                    refine ⟨7219553064314469360439117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 154017132038708679689367829 7219553064314469360439117)
                    ·
                      refine ⟨2707332399117926010164669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7219553064314469360439117 2707332399117926010164669)
                      ·
                        rfl

theorem cell23_5272511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_5272511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272511 prefixEnd_5272511 := by exact prefixLift 5272511
  have htrace : WordTrace (prefixWord ++ tailWord_5272511) baseStart_5272511 baseEnd_5272511 := by
    simpa [prefixWord, tailWord_5272511, baseEnd_5272511] using wordTrace_append hprefix tailTrace_5272511
  have hstable : (prefixWord ++ tailWord_5272511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272511).length < 2 ^ (prefixWord ++ tailWord_5272511).sum := by decide
  have hdescent : baseEnd_5272511 < baseStart_5272511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272568 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 2, 7, 2]
def baseStart_5272568 : Nat := 118140960795 + 5272568 * 2 ^ 59
def prefixEnd_5272568 : Nat := 4983230072969 + 3 ^ 40 * 5272568 * 2
def baseEnd_5272568 : Nat := 2707361667515232287151907

theorem tailTrace_5272568 : CollatzResearch.WordTrace tailWord_5272568 prefixEnd_5272568 2707361667515232287151907 := by
  unfold tailWord_5272568
  simp only [CollatzResearch.WordTrace]
  refine ⟨96153176781197046884201179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128204235708262729178934905 96153176781197046884201179)
  ·
    refine ⟨144229765171795570326301769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96153176781197046884201179 144229765171795570326301769)
    ·
      refine ⟨108172323878846677744726327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144229765171795570326301769 108172323878846677744726327)
      ·
        refine ⟨162258485818270016617089491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108172323878846677744726327 162258485818270016617089491)
        ·
          refine ⟨243387728727405024925634237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162258485818270016617089491 243387728727405024925634237)
          ·
            refine ⟨91270398272776884347112839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243387728727405024925634237 91270398272776884347112839)
            ·
              refine ⟨136905597409165326520669259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91270398272776884347112839 136905597409165326520669259)
              ·
                refine ⟨205358396113747989781003889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136905597409165326520669259 205358396113747989781003889)
                ·
                  refine ⟨154018797085310992335752917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205358396113747989781003889 154018797085310992335752917)
                  ·
                    refine ⟨3609815556686976382869209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 154018797085310992335752917 3609815556686976382869209)
                    ·
                      refine ⟨2707361667515232287151907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609815556686976382869209 2707361667515232287151907)
                      ·
                        rfl

theorem cell23_5272568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_5272568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272568 prefixEnd_5272568 := by exact prefixLift 5272568
  have htrace : WordTrace (prefixWord ++ tailWord_5272568) baseStart_5272568 baseEnd_5272568 := by
    simpa [prefixWord, tailWord_5272568, baseEnd_5272568] using wordTrace_append hprefix tailTrace_5272568
  have hstable : (prefixWord ++ tailWord_5272568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272568).length < 2 ^ (prefixWord ++ tailWord_5272568).sum := by decide
  have hdescent : baseEnd_5272568 < baseStart_5272568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272615 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_5272615 : Nat := 118140960795 + 5272615 * 2 ^ 59
def prefixEnd_5272615 : Nat := 4983230072969 + 3 ^ 40 * 5272615 * 2
def baseEnd_5272615 : Nat := 2707385801105993603264191

theorem tailTrace_5272615 : CollatzResearch.WordTrace tailWord_5272615 prefixEnd_5272615 2707385801105993603264191 := by
  unfold tailWord_5272615
  simp only [CollatzResearch.WordTrace]
  refine ⟨192308067793223820795363299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128205378528815880530242199 192308067793223820795363299)
  ·
    refine ⟨288462101689835731193044949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192308067793223820795363299 288462101689835731193044949)
    ·
      refine ⟨6760830508355524949836991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 288462101689835731193044949 6760830508355524949836991)
      ·
        refine ⟨10141245762533287424755487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760830508355524949836991 10141245762533287424755487)
        ·
          refine ⟨15211868643799931137133231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10141245762533287424755487 15211868643799931137133231)
          ·
            refine ⟨22817802965699896705699847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15211868643799931137133231 22817802965699896705699847)
            ·
              refine ⟨34226704448549845058549771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22817802965699896705699847 34226704448549845058549771)
              ·
                refine ⟨51340056672824767587824657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34226704448549845058549771 51340056672824767587824657)
                ·
                  refine ⟨38505042504618575690868493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51340056672824767587824657 38505042504618575690868493)
                  ·
                    refine ⟨14439390939231965884075685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38505042504618575690868493 14439390939231965884075685)
                    ·
                      refine ⟨2707385801105993603264191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14439390939231965884075685 2707385801105993603264191)
                      ·
                        rfl

theorem cell23_5272615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_5272615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272615 prefixEnd_5272615 := by exact prefixLift 5272615
  have htrace : WordTrace (prefixWord ++ tailWord_5272615) baseStart_5272615 baseEnd_5272615 := by
    simpa [prefixWord, tailWord_5272615, baseEnd_5272615] using wordTrace_append hprefix tailTrace_5272615
  have hstable : (prefixWord ++ tailWord_5272615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272615).length < 2 ^ (prefixWord ++ tailWord_5272615).sum := by decide
  have hdescent : baseEnd_5272615 < baseStart_5272615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272632 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 1, 4, 2]
def baseStart_5272632 : Nat := 118140960795 + 5272632 * 2 ^ 59
def prefixEnd_5272632 : Nat := 4983230072969 + 3 ^ 40 * 5272632 * 2
def baseEnd_5272632 : Nat := 2707394530277120036751613

theorem tailTrace_5272632 : CollatzResearch.WordTrace tailWord_5272632 prefixEnd_5272632 2707394530277120036751613 := by
  unfold tailWord_5272632
  simp only [CollatzResearch.WordTrace]
  refine ⟨96154343917081116349366075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128205791889441488465821433 96154343917081116349366075)
  ·
    refine ⟨144231515875621674524049113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96154343917081116349366075 144231515875621674524049113)
    ·
      refine ⟨108173636906716255893036835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144231515875621674524049113 108173636906716255893036835)
      ·
        refine ⟨162260455360074383839555253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108173636906716255893036835 162260455360074383839555253)
        ·
          refine ⟨15211917690006973484958305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162260455360074383839555253 15211917690006973484958305)
          ·
            refine ⟨11408938267505230113718729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15211917690006973484958305 11408938267505230113718729)
            ·
              refine ⟨8556703700628922585289047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11408938267505230113718729 8556703700628922585289047)
              ·
                refine ⟨12835055550943383877933571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8556703700628922585289047 12835055550943383877933571)
                ·
                  refine ⟨19252583326415075816900357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12835055550943383877933571 19252583326415075816900357)
                  ·
                    refine ⟨3609859373702826715668817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19252583326415075816900357 3609859373702826715668817)
                    ·
                      refine ⟨2707394530277120036751613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3609859373702826715668817 2707394530277120036751613)
                      ·
                        rfl

theorem cell23_5272632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_5272632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272632 prefixEnd_5272632 := by exact prefixLift 5272632
  have htrace : WordTrace (prefixWord ++ tailWord_5272632) baseStart_5272632 baseEnd_5272632 := by
    simpa [prefixWord, tailWord_5272632, baseEnd_5272632] using wordTrace_append hprefix tailTrace_5272632
  have hstable : (prefixWord ++ tailWord_5272632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272632).length < 2 ^ (prefixWord ++ tailWord_5272632).sum := by decide
  have hdescent : baseEnd_5272632 < baseStart_5272632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272648 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_5272648 : Nat := 118140960795 + 5272648 * 2 ^ 59
def prefixEnd_5272648 : Nat := 4983230072969 + 3 ^ 40 * 5272648 * 2
def baseEnd_5272648 : Nat := 2707402745967591974151539

theorem tailTrace_5272648 : CollatzResearch.WordTrace tailWord_5272648 prefixEnd_5272648 2707402745967591974151539 := by
  unfold tailWord_5272648
  simp only [CollatzResearch.WordTrace]
  refine ⟨96154635701052133715657299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128206180934736178287543065 96154635701052133715657299)
  ·
    refine ⟨144231953551578200573485949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96154635701052133715657299 144231953551578200573485949)
    ·
      refine ⟨54086982581841825215057231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144231953551578200573485949 54086982581841825215057231)
      ·
        refine ⟨81130473872762737822585847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54086982581841825215057231 81130473872762737822585847)
        ·
          refine ⟨121695710809144106733878771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81130473872762737822585847 121695710809144106733878771)
          ·
            refine ⟨182543566213716160100818157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121695710809144106733878771 182543566213716160100818157)
            ·
              refine ⟨68453837330143560037806809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182543566213716160100818157 68453837330143560037806809)
              ·
                refine ⟨51340377997607670028355107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68453837330143560037806809 51340377997607670028355107)
                ·
                  refine ⟨77010566996411505042532661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51340377997607670028355107 77010566996411505042532661)
                  ·
                    refine ⟨7219740655913578597737437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77010566996411505042532661 7219740655913578597737437)
                    ·
                      refine ⟨2707402745967591974151539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7219740655913578597737437 2707402745967591974151539)
                      ·
                        rfl

theorem cell23_5272648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_5272648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272648 prefixEnd_5272648 := by exact prefixLift 5272648
  have htrace : WordTrace (prefixWord ++ tailWord_5272648) baseStart_5272648 baseEnd_5272648 := by
    simpa [prefixWord, tailWord_5272648, baseEnd_5272648] using wordTrace_append hprefix tailTrace_5272648
  have hstable : (prefixWord ++ tailWord_5272648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272648).length < 2 ^ (prefixWord ++ tailWord_5272648).sum := by decide
  have hdescent : baseEnd_5272648 < baseStart_5272648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272688 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_5272688 : Nat := 118140960795 + 5272688 * 2 ^ 59
def prefixEnd_5272688 : Nat := 4983230072969 + 3 ^ 40 * 5272688 * 2
def baseEnd_5272688 : Nat := 2707423285193771817651355

theorem tailTrace_5272688 : CollatzResearch.WordTrace tailWord_5272688 prefixEnd_5272688 2707423285193771817651355 := by
  unfold tailWord_5272688
  simp only [CollatzResearch.WordTrace]
  refine ⟨96155365160979677131385359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128207153547972902841847145 96155365160979677131385359)
  ·
    refine ⟨144233047741469515697078039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96155365160979677131385359 144233047741469515697078039)
    ·
      refine ⟨216349571612204273545617059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144233047741469515697078039 216349571612204273545617059)
      ·
        refine ⟨324524357418306410318425589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216349571612204273545617059 324524357418306410318425589)
        ·
          refine ⟨30424158507966225967352399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 324524357418306410318425589 30424158507966225967352399)
          ·
            refine ⟨45636237761949338951028599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30424158507966225967352399 45636237761949338951028599)
            ·
              refine ⟨68454356642924008426542899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45636237761949338951028599 68454356642924008426542899)
              ·
                refine ⟨102681534964386012639814349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68454356642924008426542899 102681534964386012639814349)
                ·
                  refine ⟨38505575611644754739930381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102681534964386012639814349 38505575611644754739930381)
                  ·
                    refine ⟨14439590854366783027473893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38505575611644754739930381 14439590854366783027473893)
                    ·
                      refine ⟨2707423285193771817651355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14439590854366783027473893 2707423285193771817651355)
                      ·
                        rfl

theorem cell23_5272688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_5272688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272688 prefixEnd_5272688 := by exact prefixLift 5272688
  have htrace : WordTrace (prefixWord ++ tailWord_5272688) baseStart_5272688 baseEnd_5272688 := by
    simpa [prefixWord, tailWord_5272688, baseEnd_5272688] using wordTrace_append hprefix tailTrace_5272688
  have hstable : (prefixWord ++ tailWord_5272688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272688).length < 2 ^ (prefixWord ++ tailWord_5272688).sum := by decide
  have hdescent : baseEnd_5272688 < baseStart_5272688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272705 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_5272705 : Nat := 118140960795 + 5272705 * 2 ^ 59
def prefixEnd_5272705 : Nat := 4983230072969 + 3 ^ 40 * 5272705 * 2
def baseEnd_5272705 : Nat := 2707432014364898251138777

theorem tailTrace_5272705 : CollatzResearch.WordTrace tailWord_5272705 prefixEnd_5272705 2707432014364898251138777 := by
  unfold tailWord_5272705
  simp only [CollatzResearch.WordTrace]
  refine ⟨192311350362897766166139569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128207566908598510777426379 192311350362897766166139569)
  ·
    refine ⟨144233512772173324624604677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192311350362897766166139569 144233512772173324624604677)
    ·
      refine ⟨27043783644782498367113377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144233512772173324624604677 27043783644782498367113377)
      ·
        refine ⟨20282837733586873775335033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27043783644782498367113377 20282837733586873775335033)
        ·
          refine ⟨15212128300190155331501275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20282837733586873775335033 15212128300190155331501275)
          ·
            refine ⟨22818192450285232997251913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15212128300190155331501275 22818192450285232997251913)
            ·
              refine ⟨17113644337713924747938935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22818192450285232997251913 17113644337713924747938935)
              ·
                refine ⟨25670466506570887121908403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17113644337713924747938935 25670466506570887121908403)
                ·
                  refine ⟨38505699759856330682862605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25670466506570887121908403 38505699759856330682862605)
                  ·
                    refine ⟨14439637409946124006073477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38505699759856330682862605 14439637409946124006073477)
                    ·
                      refine ⟨2707432014364898251138777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14439637409946124006073477 2707432014364898251138777)
                      ·
                        rfl

theorem cell23_5272705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_5272705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272705 prefixEnd_5272705 := by exact prefixLift 5272705
  have htrace : WordTrace (prefixWord ++ tailWord_5272705) baseStart_5272705 baseEnd_5272705 := by
    simpa [prefixWord, tailWord_5272705, baseEnd_5272705] using wordTrace_append hprefix tailTrace_5272705
  have hstable : (prefixWord ++ tailWord_5272705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272705).length < 2 ^ (prefixWord ++ tailWord_5272705).sum := by decide
  have hdescent : baseEnd_5272705 < baseStart_5272705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272722 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_5272722 : Nat := 118140960795 + 5272722 * 2 ^ 59
def prefixEnd_5272722 : Nat := 4983230072969 + 3 ^ 40 * 5272722 * 2
def baseEnd_5272722 : Nat := 2707440743536024684626199

theorem tailTrace_5272722 : CollatzResearch.WordTrace tailWord_5272722 prefixEnd_5272722 2707440743536024684626199 := by
  unfold tailWord_5272722
  simp only [CollatzResearch.WordTrace]
  refine ⟨48077992600959044517377105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128207980269224118713005613 48077992600959044517377105)
  ·
    refine ⟨36058494450719283388032829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48077992600959044517377105 36058494450719283388032829)
    ·
      refine ⟨13521935419019731270512311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36058494450719283388032829 13521935419019731270512311)
      ·
        refine ⟨20282903128529596905768467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13521935419019731270512311 20282903128529596905768467)
        ·
          refine ⟨30424354692794395358652701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20282903128529596905768467 30424354692794395358652701)
          ·
            refine ⟨11409133009797898259494763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30424354692794395358652701 11409133009797898259494763)
            ·
              refine ⟨17113699514696847389242145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11409133009797898259494763 17113699514696847389242145)
              ·
                refine ⟨12835274636022635541931609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17113699514696847389242145 12835274636022635541931609)
                ·
                  refine ⟨9626455977016976656448707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12835274636022635541931609 9626455977016976656448707)
                  ·
                    refine ⟨14439683965525464984673061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9626455977016976656448707 14439683965525464984673061)
                    ·
                      refine ⟨2707440743536024684626199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14439683965525464984673061 2707440743536024684626199)
                      ·
                        rfl

theorem cell23_5272722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_5272722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272722 prefixEnd_5272722 := by exact prefixLift 5272722
  have htrace : WordTrace (prefixWord ++ tailWord_5272722) baseStart_5272722 baseEnd_5272722 := by
    simpa [prefixWord, tailWord_5272722, baseEnd_5272722] using wordTrace_append hprefix tailTrace_5272722
  have hstable : (prefixWord ++ tailWord_5272722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272722).length < 2 ^ (prefixWord ++ tailWord_5272722).sum := by decide
  have hdescent : baseEnd_5272722 < baseStart_5272722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272732 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_5272732 : Nat := 118140960795 + 5272732 * 2 ^ 59
def prefixEnd_5272732 : Nat := 4983230072969 + 3 ^ 40 * 5272732 * 2
def baseEnd_5272732 : Nat := 902481959447523215167051

theorem tailTrace_5272732 : CollatzResearch.WordTrace tailWord_5272732 prefixEnd_5272732 902481959447523215167051 := by
  unfold tailWord_5272732
  simp only [CollatzResearch.WordTrace]
  refine ⟨96156167566899974888686225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128208223422533299851581633 96156167566899974888686225)
  ·
    refine ⟨72117125675174981166514669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96156167566899974888686225 72117125675174981166514669)
    ·
      refine ⟨27043922128190617937443001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72117125675174981166514669 27043922128190617937443001)
      ·
        refine ⟨20282941596142963453082251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27043922128190617937443001 20282941596142963453082251)
        ·
          refine ⟨30424412394214445179623377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20282941596142963453082251 30424412394214445179623377)
          ·
            refine ⟨22818309295660833884717533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30424412394214445179623377 22818309295660833884717533)
            ·
              refine ⟨8556865985872812706769075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22818309295660833884717533 8556865985872812706769075)
              ·
                refine ⟨12835298978809219060153613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8556865985872812706769075 12835298978809219060153613)
                ·
                  refine ⟨4813237117053457147557605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12835298978809219060153613 4813237117053457147557605)
                  ·
                    refine ⟨902481959447523215167051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4813237117053457147557605 902481959447523215167051)
                    ·
                      rfl

theorem cell23_5272732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_5272732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272732 prefixEnd_5272732 := by exact prefixLift 5272732
  have htrace : WordTrace (prefixWord ++ tailWord_5272732) baseStart_5272732 baseEnd_5272732 := by
    simpa [prefixWord, tailWord_5272732, baseEnd_5272732] using wordTrace_append hprefix tailTrace_5272732
  have hstable : (prefixWord ++ tailWord_5272732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272732).length < 2 ^ (prefixWord ++ tailWord_5272732).sum := by decide
  have hdescent : baseEnd_5272732 < baseStart_5272732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272775 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 1, 5]
def baseStart_5272775 : Nat := 118140960795 + 5272775 * 2 ^ 59
def prefixEnd_5272775 : Nat := 4983230072969 + 3 ^ 40 * 5272775 * 2
def baseEnd_5272775 : Nat := 902489319336904325754485

theorem tailTrace_5272775 : CollatzResearch.WordTrace tailWord_5272775 prefixEnd_5272775 902489319336904325754485 := by
  unfold tailWord_5272775
  simp only [CollatzResearch.WordTrace]
  refine ⟨192313903472644168121187779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128209268981762778747458519 192313903472644168121187779)
  ·
    refine ⟨288470855208966252181781669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192313903472644168121187779 288470855208966252181781669)
    ·
      refine ⟨54088285351681172284084063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288470855208966252181781669 54088285351681172284084063)
      ·
        refine ⟨81132428027521758426126095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54088285351681172284084063 81132428027521758426126095)
        ·
          refine ⟨121698642041282637639189143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81132428027521758426126095 121698642041282637639189143)
          ·
            refine ⟨182547963061923956458783715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121698642041282637639189143 182547963061923956458783715)
            ·
              refine ⟨273821944592885934688175573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182547963061923956458783715 273821944592885934688175573)
              ·
                refine ⟨6417701826395764094254115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 273821944592885934688175573 6417701826395764094254115)
                ·
                  refine ⟨9626552739593646141381173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6417701826395764094254115 9626552739593646141381173)
                  ·
                    refine ⟨902489319336904325754485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9626552739593646141381173 902489319336904325754485)
                    ·
                      rfl

theorem cell23_5272775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_5272775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272775 prefixEnd_5272775 := by exact prefixLift 5272775
  have htrace : WordTrace (prefixWord ++ tailWord_5272775) baseStart_5272775 baseEnd_5272775 := by
    simpa [prefixWord, tailWord_5272775, baseEnd_5272775] using wordTrace_append hprefix tailTrace_5272775
  have hstable : (prefixWord ++ tailWord_5272775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272775).length < 2 ^ (prefixWord ++ tailWord_5272775).sum := by decide
  have hdescent : baseEnd_5272775 < baseStart_5272775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272822 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_5272822 : Nat := 118140960795 + 5272822 * 2 ^ 59
def prefixEnd_5272822 : Nat := 4983230072969 + 3 ^ 40 * 5272822 * 2
def baseEnd_5272822 : Nat := 902497363867158097791913

theorem tailTrace_5272822 : CollatzResearch.WordTrace tailWord_5272822 prefixEnd_5272822 902497363867158097791913 := by
  unfold tailWord_5272822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019726106467118446759295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128210411802315930098765813 12019726106467118446759295)
  ·
    refine ⟨18029589159700677670138943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12019726106467118446759295 18029589159700677670138943)
    ·
      refine ⟨27044383739551016505208415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18029589159700677670138943 27044383739551016505208415)
      ·
        refine ⟨40566575609326524757812623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27044383739551016505208415 40566575609326524757812623)
        ·
          refine ⟨60849863413989787136718935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40566575609326524757812623 60849863413989787136718935)
          ·
            refine ⟨91274795120984680705078403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60849863413989787136718935 91274795120984680705078403)
            ·
              refine ⟨136912192681477021057617605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91274795120984680705078403 136912192681477021057617605)
              ·
                refine ⟨25671036127776941448303301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136912192681477021057617605 25671036127776941448303301)
                ·
                  refine ⟨4813319273958176521556869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25671036127776941448303301 4813319273958176521556869)
                  ·
                    refine ⟨902497363867158097791913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4813319273958176521556869 902497363867158097791913)
                    ·
                      rfl

theorem cell23_5272822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_5272822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272822 prefixEnd_5272822 := by exact prefixLift 5272822
  have htrace : WordTrace (prefixWord ++ tailWord_5272822) baseStart_5272822 baseEnd_5272822 := by
    simpa [prefixWord, tailWord_5272822, baseEnd_5272822] using wordTrace_append hprefix tailTrace_5272822
  have hstable : (prefixWord ++ tailWord_5272822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272822).length < 2 ^ (prefixWord ++ tailWord_5272822).sum := by decide
  have hdescent : baseEnd_5272822 < baseStart_5272822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272825 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_5272825 : Nat := 118140960795 + 5272825 * 2 ^ 59
def prefixEnd_5272825 : Nat := 4983230072969 + 3 ^ 40 * 5272825 * 2
def baseEnd_5272825 : Nat := 2707493632043437781638225

theorem tailTrace_5272825 : CollatzResearch.WordTrace tailWord_5272825 prefixEnd_5272825 2707493632043437781638225 := by
  unfold tailWord_5272825
  simp only [CollatzResearch.WordTrace]
  refine ⟨192315727122463026660507929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128210484748308684440338619 192315727122463026660507929)
  ·
    refine ⟨144236795341847269995380947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192315727122463026660507929 144236795341847269995380947)
    ·
      refine ⟨216355193012770904993071421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144236795341847269995380947 216355193012770904993071421)
      ·
        refine ⟨81133197379789089372401783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216355193012770904993071421 81133197379789089372401783)
        ·
          refine ⟨121699796069683634058602675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81133197379789089372401783 121699796069683634058602675)
          ·
            refine ⟨182549694104525451087904013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121699796069683634058602675 182549694104525451087904013)
            ·
              refine ⟨68456135289197044157964005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182549694104525451087904013 68456135289197044157964005)
              ·
                refine ⟨12835525366724445779618251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68456135289197044157964005 12835525366724445779618251)
                ·
                  refine ⟨19253288050086668669427377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12835525366724445779618251 19253288050086668669427377)
                  ·
                    refine ⟨14439966037565001502070533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19253288050086668669427377 14439966037565001502070533)
                    ·
                      refine ⟨2707493632043437781638225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14439966037565001502070533 2707493632043437781638225)
                      ·
                        rfl

theorem cell23_5272825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_5272825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272825 prefixEnd_5272825 := by exact prefixLift 5272825
  have htrace : WordTrace (prefixWord ++ tailWord_5272825) baseStart_5272825 baseEnd_5272825 := by
    simpa [prefixWord, tailWord_5272825, baseEnd_5272825] using wordTrace_append hprefix tailTrace_5272825
  have hstable : (prefixWord ++ tailWord_5272825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272825).length < 2 ^ (prefixWord ++ tailWord_5272825).sum := by decide
  have hdescent : baseEnd_5272825 < baseStart_5272825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272846 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_5272846 : Nat := 118140960795 + 5272846 * 2 ^ 59
def prefixEnd_5272846 : Nat := 4983230072969 + 3 ^ 40 * 5272846 * 2
def baseEnd_5272846 : Nat := 2707504415137182199475629

theorem tailTrace_5272846 : CollatzResearch.WordTrace tailWord_5272846 prefixEnd_5272846 2707504415137182199475629 := by
  unfold tailWord_5272846
  simp only [CollatzResearch.WordTrace]
  refine ⟨24039561631923368405877799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128210995370257964831348261 24039561631923368405877799)
  ·
    refine ⟨36059342447885052608816699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24039561631923368405877799 36059342447885052608816699)
    ·
      refine ⟨54089013671827578913225049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36059342447885052608816699 54089013671827578913225049)
      ·
        refine ⟨40566760253870684184918787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54089013671827578913225049 40566760253870684184918787)
        ·
          refine ⟨60850140380806026277378181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40566760253870684184918787 60850140380806026277378181)
          ·
            refine ⟨11409401321401129927008409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60850140380806026277378181 11409401321401129927008409)
            ·
              refine ⟨8557050991050847445256307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11409401321401129927008409 8557050991050847445256307)
              ·
                refine ⟨12835576486576271167884461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8557050991050847445256307 12835576486576271167884461)
                ·
                  refine ⟨4813341182466101687956673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12835576486576271167884461 4813341182466101687956673)
                  ·
                    refine ⟨3610005886849576265967505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4813341182466101687956673 3610005886849576265967505)
                    ·
                      refine ⟨2707504415137182199475629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610005886849576265967505 2707504415137182199475629)
                      ·
                        rfl

theorem cell23_5272846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_5272846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272846 prefixEnd_5272846 := by exact prefixLift 5272846
  have htrace : WordTrace (prefixWord ++ tailWord_5272846) baseStart_5272846 baseEnd_5272846 := by
    simpa [prefixWord, tailWord_5272846, baseEnd_5272846] using wordTrace_append hprefix tailTrace_5272846
  have hstable : (prefixWord ++ tailWord_5272846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272846).length < 2 ^ (prefixWord ++ tailWord_5272846).sum := by decide
  have hdescent : baseEnd_5272846 < baseStart_5272846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272866 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_5272866 : Nat := 118140960795 + 5272866 * 2 ^ 59
def prefixEnd_5272866 : Nat := 4983230072969 + 3 ^ 40 * 5272866 * 2
def baseEnd_5272866 : Nat := 2707514684750272121225537

theorem tailTrace_5272866 : CollatzResearch.WordTrace tailWord_5272866 prefixEnd_5272866 2707514684750272121225537 := by
  unfold tailWord_5272866
  simp only [CollatzResearch.WordTrace]
  refine ⟨48079305628828622665687613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128211481676876327108500301 48079305628828622665687613)
  ·
    refine ⟨18029739610810733499632855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48079305628828622665687613 18029739610810733499632855)
    ·
      refine ⟨27044609416216100249449283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18029739610810733499632855 27044609416216100249449283)
      ·
        refine ⟨40566914124324150374173925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27044609416216100249449283 40566914124324150374173925)
        ·
          refine ⟨7606296398310778195157611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40566914124324150374173925 7606296398310778195157611)
          ·
            refine ⟨11409444597466167292736417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7606296398310778195157611 11409444597466167292736417)
            ·
              refine ⟨8557083448099625469552313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11409444597466167292736417 8557083448099625469552313)
              ·
                refine ⟨6417812586074719102164235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8557083448099625469552313 6417812586074719102164235)
                ·
                  refine ⟨9626718879112078653246353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6417812586074719102164235 9626718879112078653246353)
                  ·
                    refine ⟨7220039159334058989934765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9626718879112078653246353 7220039159334058989934765)
                    ·
                      refine ⟨2707514684750272121225537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220039159334058989934765 2707514684750272121225537)
                      ·
                        rfl

theorem cell23_5272866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_5272866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272866 prefixEnd_5272866 := by exact prefixLift 5272866
  have htrace : WordTrace (prefixWord ++ tailWord_5272866) baseStart_5272866 baseEnd_5272866 := by
    simpa [prefixWord, tailWord_5272866, baseEnd_5272866] using wordTrace_append hprefix tailTrace_5272866
  have hstable : (prefixWord ++ tailWord_5272866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272866).length < 2 ^ (prefixWord ++ tailWord_5272866).sum := by decide
  have hdescent : baseEnd_5272866 < baseStart_5272866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272886 : List Nat := [5, 1, 2, 3, 2, 1, 9]
def baseStart_5272886 : Nat := 118140960795 + 5272886 * 2 ^ 59
def prefixEnd_5272886 : Nat := 4983230072969 + 3 ^ 40 * 5272886 * 2
def baseEnd_5272886 : Nat := 33426234004485951147845

theorem tailTrace_5272886 : CollatzResearch.WordTrace tailWord_5272886 prefixEnd_5272886 33426234004485951147845 := by
  unfold tailWord_5272886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019871998452627129904907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128211967983494689385652341 12019871998452627129904907)
  ·
    refine ⟨18029807997678940694857361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12019871998452627129904907 18029807997678940694857361)
    ·
      refine ⟨13522355998259205521143021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18029807997678940694857361 13522355998259205521143021)
      ·
        refine ⟨5070883499347202070428633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13522355998259205521143021 5070883499347202070428633)
        ·
          refine ⟨3803162624510401552821475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5070883499347202070428633 3803162624510401552821475)
          ·
            refine ⟨5704743936765602329232213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3803162624510401552821475 5704743936765602329232213)
            ·
              refine ⟨33426234004485951147845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5704743936765602329232213 33426234004485951147845)
              ·
                rfl

theorem cell23_5272886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 9].length) (baseStart_5272886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272886 prefixEnd_5272886 := by exact prefixLift 5272886
  have htrace : WordTrace (prefixWord ++ tailWord_5272886) baseStart_5272886 baseEnd_5272886 := by
    simpa [prefixWord, tailWord_5272886, baseEnd_5272886] using wordTrace_append hprefix tailTrace_5272886
  have hstable : (prefixWord ++ tailWord_5272886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272886).length < 2 ^ (prefixWord ++ tailWord_5272886).sum := by decide
  have hdescent : baseEnd_5272886 < baseStart_5272886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272915 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 4]
def baseStart_5272915 : Nat := 118140960795 + 5272915 * 2 ^ 59
def prefixEnd_5272915 : Nat := 4983230072969 + 3 ^ 40 * 5272915 * 2
def baseEnd_5272915 : Nat := 2707539845302342429512811

theorem tailTrace_5272915 : CollatzResearch.WordTrace tailWord_5272915 prefixEnd_5272915 2707539845302342429512811 := by
  unfold tailWord_5272915
  simp only [CollatzResearch.WordTrace]
  refine ⟨192319009692136972031284199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128212673128091314687522799 192319009692136972031284199)
  ·
    refine ⟨288478514538205458046926299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192319009692136972031284199 288478514538205458046926299)
    ·
      refine ⟨432717771807308187070389449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288478514538205458046926299 432717771807308187070389449)
      ·
        refine ⟨324538328855481140302792087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432717771807308187070389449 324538328855481140302792087)
        ·
          refine ⟨486807493283221710454188131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324538328855481140302792087 486807493283221710454188131)
          ·
            refine ⟨730211239924832565681282197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486807493283221710454188131 730211239924832565681282197)
            ·
              refine ⟨34228651871476526516310103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 730211239924832565681282197 34228651871476526516310103)
              ·
                refine ⟨51342977807214789774465155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34228651871476526516310103 51342977807214789774465155)
                ·
                  refine ⟨77014466710822184661697733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51342977807214789774465155 77014466710822184661697733)
                  ·
                    refine ⟨14440212508279159624068325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77014466710822184661697733 14440212508279159624068325)
                    ·
                      refine ⟨2707539845302342429512811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14440212508279159624068325 2707539845302342429512811)
                      ·
                        rfl

theorem cell23_5272915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_5272915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272915 prefixEnd_5272915 := by exact prefixLift 5272915
  have htrace : WordTrace (prefixWord ++ tailWord_5272915) baseStart_5272915 baseEnd_5272915 := by
    simpa [prefixWord, tailWord_5272915, baseEnd_5272915] using wordTrace_append hprefix tailTrace_5272915
  have hstable : (prefixWord ++ tailWord_5272915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272915).length < 2 ^ (prefixWord ++ tailWord_5272915).sum := by decide
  have hdescent : baseEnd_5272915 < baseStart_5272915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272936 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_5272936 : Nat := 118140960795 + 5272936 * 2 ^ 59
def prefixEnd_5272936 : Nat := 4983230072969 + 3 ^ 40 * 5272936 * 2
def baseEnd_5272936 : Nat := 2707550628396086847350215

theorem tailTrace_5272936 : CollatzResearch.WordTrace tailWord_5272936 prefixEnd_5272936 2707550628396086847350215 := by
  unfold tailWord_5272936
  simp only [CollatzResearch.WordTrace]
  refine ⟨96159887812530446308899331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128213183750040595078532441 96159887812530446308899331)
  ·
    refine ⟨144239831718795669463348997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96159887812530446308899331 144239831718795669463348997)
    ·
      refine ⟨27044968447274188024377937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144239831718795669463348997 27044968447274188024377937)
      ·
        refine ⟨20283726335455641018283453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27044968447274188024377937 20283726335455641018283453)
        ·
          refine ⟨7606397375795865381856295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20283726335455641018283453 7606397375795865381856295)
          ·
            refine ⟨11409596063693798072784443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7606397375795865381856295 11409596063693798072784443)
            ·
              refine ⟨17114394095540697109176665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11409596063693798072784443 17114394095540697109176665)
              ·
                refine ⟨12835795571655522831882499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17114394095540697109176665 12835795571655522831882499)
                ·
                  refine ⟨19253693357483284247823749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12835795571655522831882499 19253693357483284247823749)
                  ·
                    refine ⟨3610067504528115796466953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19253693357483284247823749 3610067504528115796466953)
                    ·
                      refine ⟨2707550628396086847350215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610067504528115796466953 2707550628396086847350215)
                      ·
                        rfl

theorem cell23_5272936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_5272936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272936 prefixEnd_5272936 := by exact prefixLift 5272936
  have htrace : WordTrace (prefixWord ++ tailWord_5272936) baseStart_5272936 baseEnd_5272936 := by
    simpa [prefixWord, tailWord_5272936, baseEnd_5272936] using wordTrace_append hprefix tailTrace_5272936
  have hstable : (prefixWord ++ tailWord_5272936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272936).length < 2 ^ (prefixWord ++ tailWord_5272936).sum := by decide
  have hdescent : baseEnd_5272936 < baseStart_5272936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272969 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 3]
def baseStart_5272969 : Nat := 118140960795 + 5272969 * 2 ^ 59
def prefixEnd_5272969 : Nat := 4983230072969 + 3 ^ 40 * 5272969 * 2
def baseEnd_5272969 : Nat := 2707567573257685218237563

theorem tailTrace_5272969 : CollatzResearch.WordTrace tailWord_5272969 prefixEnd_5272969 2707567573257685218237563 := by
  unfold tailWord_5272969
  simp only [CollatzResearch.WordTrace]
  refine ⟨192320979233941339253749961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128213986155960892835833307 192320979233941339253749961)
  ·
    refine ⟨144240734425456004440312471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192320979233941339253749961 144240734425456004440312471)
    ·
      refine ⟨216361101638184006660468707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144240734425456004440312471 216361101638184006660468707)
      ·
        refine ⟨324541652457276009990703061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216361101638184006660468707 324541652457276009990703061)
        ·
          refine ⟨7606444979467406484157103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 324541652457276009990703061 7606444979467406484157103)
          ·
            refine ⟨11409667469201109726235655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7606444979467406484157103 11409667469201109726235655)
            ·
              refine ⟨17114501203801664589353483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11409667469201109726235655 17114501203801664589353483)
              ·
                refine ⟨25671751805702496884030225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17114501203801664589353483 25671751805702496884030225)
                ·
                  refine ⟨19253813854276872663022669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25671751805702496884030225 19253813854276872663022669)
                  ·
                    refine ⟨7220180195353827248633501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19253813854276872663022669 7220180195353827248633501)
                    ·
                      refine ⟨2707567573257685218237563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220180195353827248633501 2707567573257685218237563)
                      ·
                        rfl

theorem cell23_5272969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_5272969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272969 prefixEnd_5272969 := by exact prefixLift 5272969
  have htrace : WordTrace (prefixWord ++ tailWord_5272969) baseStart_5272969 baseEnd_5272969 := by
    simpa [prefixWord, tailWord_5272969, baseEnd_5272969] using wordTrace_append hprefix tailTrace_5272969
  have hstable : (prefixWord ++ tailWord_5272969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272969).length < 2 ^ (prefixWord ++ tailWord_5272969).sum := by decide
  have hdescent : baseEnd_5272969 < baseStart_5272969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272989 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_5272989 : Nat := 118140960795 + 5272989 * 2 ^ 59
def prefixEnd_5272989 : Nat := 4983230072969 + 3 ^ 40 * 5272989 * 2
def baseEnd_5272989 : Nat := 902525947623591713329157

theorem tailTrace_5272989 : CollatzResearch.WordTrace tailWord_5272989 prefixEnd_5272989 902525947623591713329157 := by
  unfold tailWord_5272989
  simp only [CollatzResearch.WordTrace]
  refine ⟨192321708693868882669478021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128214472462579255112985347 192321708693868882669478021)
  ·
    refine ⟨36060320380100415500527129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192321708693868882669478021 36060320380100415500527129)
    ·
      refine ⟨27045240285075311625395347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36060320380100415500527129 27045240285075311625395347)
      ·
        refine ⟨40567860427612967438093021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27045240285075311625395347 40567860427612967438093021)
        ·
          refine ⟨15212947660354862789284883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40567860427612967438093021 15212947660354862789284883)
          ·
            refine ⟨22819421490532294183927325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15212947660354862789284883 22819421490532294183927325)
            ·
              refine ⟨8557283058949610318972747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22819421490532294183927325 8557283058949610318972747)
              ·
                refine ⟨12835924588424415478459121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8557283058949610318972747 12835924588424415478459121)
                ·
                  refine ⟨9626943441318311608844341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12835924588424415478459121 9626943441318311608844341)
                  ·
                    refine ⟨902525947623591713329157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9626943441318311608844341 902525947623591713329157)
                    ·
                      rfl

theorem cell23_5272989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_5272989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272989 prefixEnd_5272989 := by exact prefixLift 5272989
  have htrace : WordTrace (prefixWord ++ tailWord_5272989) baseStart_5272989 baseEnd_5272989 := by
    simpa [prefixWord, tailWord_5272989, baseEnd_5272989] using wordTrace_append hprefix tailTrace_5272989
  have hstable : (prefixWord ++ tailWord_5272989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272989).length < 2 ^ (prefixWord ++ tailWord_5272989).sum := by decide
  have hdescent : baseEnd_5272989 < baseStart_5272989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5272992 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_5272992 : Nat := 118140960795 + 5272992 * 2 ^ 59
def prefixEnd_5272992 : Nat := 4983230072969 + 3 ^ 40 * 5272992 * 2
def baseEnd_5272992 : Nat := 2707579383312738628249957

theorem tailTrace_5272992 : CollatzResearch.WordTrace tailWord_5272992 prefixEnd_5272992 2707579383312738628249957 := by
  unfold tailWord_5272992
  simp only [CollatzResearch.WordTrace]
  refine ⟨96160909056429007090918615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128214545408572009454558153 96160909056429007090918615)
  ·
    refine ⟨144241363584643510636377923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96160909056429007090918615 144241363584643510636377923)
    ·
      refine ⟨216362045376965265954566885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144241363584643510636377923 216362045376965265954566885)
      ·
        refine ⟨40567883508180987366481291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216362045376965265954566885 40567883508180987366481291)
        ·
          refine ⟨60851825262271481049721937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40567883508180987366481291 60851825262271481049721937)
          ·
            refine ⟨45638868946703610787291453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60851825262271481049721937 45638868946703610787291453)
            ·
              refine ⟨17114575855013854045234295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45638868946703610787291453 17114575855013854045234295)
              ·
                refine ⟨25671863782520781067851443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17114575855013854045234295 25671863782520781067851443)
                ·
                  refine ⟨38507795673781171601777165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25671863782520781067851443 38507795673781171601777165)
                  ·
                    refine ⟨14440423377667939350666437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38507795673781171601777165 14440423377667939350666437)
                    ·
                      refine ⟨2707579383312738628249957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14440423377667939350666437 2707579383312738628249957)
                      ·
                        rfl

theorem cell23_5272992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_5272992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5272992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5272992 prefixEnd_5272992 := by exact prefixLift 5272992
  have htrace : WordTrace (prefixWord ++ tailWord_5272992) baseStart_5272992 baseEnd_5272992 := by
    simpa [prefixWord, tailWord_5272992, baseEnd_5272992] using wordTrace_append hprefix tailTrace_5272992
  have hstable : (prefixWord ++ tailWord_5272992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5272992).length < 2 ^ (prefixWord ++ tailWord_5272992).sum := by decide
  have hdescent : baseEnd_5272992 < baseStart_5272992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5272992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273009 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 4, 4, 2]
def baseStart_5273009 : Nat := 118140960795 + 5273009 * 2 ^ 59
def prefixEnd_5273009 : Nat := 4983230072969 + 3 ^ 40 * 5273009 * 2
def baseEnd_5273009 : Nat := 2707588112483865061737379

theorem tailTrace_5273009 : CollatzResearch.WordTrace tailWord_5273009 prefixEnd_5273009 2707588112483865061737379 := by
  unfold tailWord_5273009
  simp only [CollatzResearch.WordTrace]
  refine ⟨192322438153796426085206081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128214958769197617390137387 192322438153796426085206081)
  ·
    refine ⟨144241828615347319563904561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192322438153796426085206081 144241828615347319563904561)
    ·
      refine ⟨108181371461510489672928421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144241828615347319563904561 108181371461510489672928421)
      ·
        refine ⟨20284007149033216813674079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108181371461510489672928421 20284007149033216813674079)
        ·
          refine ⟨30426010723549825220511119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20284007149033216813674079 30426010723549825220511119)
          ·
            refine ⟨45639016085324737830766679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30426010723549825220511119 45639016085324737830766679)
            ·
              refine ⟨68458524127987106746150019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45639016085324737830766679 68458524127987106746150019)
              ·
                refine ⟨102687786191980660119225029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68458524127987106746150019 102687786191980660119225029)
                ·
                  refine ⟨19253959910996373772354693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102687786191980660119225029 19253959910996373772354693)
                  ·
                    refine ⟨3610117483311820082316505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19253959910996373772354693 3610117483311820082316505)
                    ·
                      refine ⟨2707588112483865061737379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610117483311820082316505 2707588112483865061737379)
                      ·
                        rfl

theorem cell23_5273009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_5273009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273009 prefixEnd_5273009 := by exact prefixLift 5273009
  have htrace : WordTrace (prefixWord ++ tailWord_5273009) baseStart_5273009 baseEnd_5273009 := by
    simpa [prefixWord, tailWord_5273009, baseEnd_5273009] using wordTrace_append hprefix tailTrace_5273009
  have hstable : (prefixWord ++ tailWord_5273009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273009).length < 2 ^ (prefixWord ++ tailWord_5273009).sum := by decide
  have hdescent : baseEnd_5273009 < baseStart_5273009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273022 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_5273022 : Nat := 118140960795 + 5273022 * 2 ^ 59
def prefixEnd_5273022 : Nat := 4983230072969 + 3 ^ 40 * 5273022 * 2
def baseEnd_5273022 : Nat := 2707594787732373510874819

theorem tailTrace_5273022 : CollatzResearch.WordTrace tailWord_5273022 prefixEnd_5273022 2707594787732373510874819 := by
  unfold tailWord_5273022
  simp only [CollatzResearch.WordTrace]
  refine ⟨24040364037843666163178665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128215274868499552870286213 24040364037843666163178665)
  ·
    refine ⟨18030273028382749622383999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24040364037843666163178665 18030273028382749622383999)
    ·
      refine ⟨27045409542574124433575999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18030273028382749622383999 27045409542574124433575999)
      ·
        refine ⟨40568114313861186650363999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27045409542574124433575999 40568114313861186650363999)
        ·
          refine ⟨60852171470791779975545999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40568114313861186650363999 60852171470791779975545999)
          ·
            refine ⟨91278257206187669963318999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60852171470791779975545999 91278257206187669963318999)
            ·
              refine ⟨136917385809281504944978499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91278257206187669963318999 136917385809281504944978499)
              ·
                refine ⟨205376078713922257417467749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136917385809281504944978499 205376078713922257417467749)
                ·
                  refine ⟨38508014758860423265775203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205376078713922257417467749 38508014758860423265775203)
                  ·
                    refine ⟨57762022138290634898662805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38508014758860423265775203 57762022138290634898662805)
                    ·
                      refine ⟨2707594787732373510874819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57762022138290634898662805 2707594787732373510874819)
                      ·
                        rfl

theorem cell23_5273022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_5273022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273022 prefixEnd_5273022 := by exact prefixLift 5273022
  have htrace : WordTrace (prefixWord ++ tailWord_5273022) baseStart_5273022 baseEnd_5273022 := by
    simpa [prefixWord, tailWord_5273022, baseEnd_5273022] using wordTrace_append hprefix tailTrace_5273022
  have hstable : (prefixWord ++ tailWord_5273022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273022).length < 2 ^ (prefixWord ++ tailWord_5273022).sum := by decide
  have hdescent : baseEnd_5273022 < baseStart_5273022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273046 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_5273046 : Nat := 118140960795 + 5273046 * 2 ^ 59
def prefixEnd_5273046 : Nat := 4983230072969 + 3 ^ 40 * 5273046 * 2
def baseEnd_5273046 : Nat := 2707607111268081416974709

theorem tailTrace_5273046 : CollatzResearch.WordTrace tailWord_5273046 prefixEnd_5273046 2707607111268081416974709 := by
  unfold tailWord_5273046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12020236728416398837768937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128215858436441587602868661 12020236728416398837768937)
  ·
    refine ⟨9015177546312299128326703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12020236728416398837768937 9015177546312299128326703)
    ·
      refine ⟨13522766319468448692490055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9015177546312299128326703 13522766319468448692490055)
      ·
        refine ⟨20284149479202673038735083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13522766319468448692490055 20284149479202673038735083)
        ·
          refine ⟨30426224218804009558102625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20284149479202673038735083 30426224218804009558102625)
          ·
            refine ⟨22819668164103007168576969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30426224218804009558102625 22819668164103007168576969)
            ·
              refine ⟨17114751123077255376432727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22819668164103007168576969 17114751123077255376432727)
              ·
                refine ⟨25672126684615883064649091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17114751123077255376432727 25672126684615883064649091)
                ·
                  refine ⟨38508190026923824596973637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25672126684615883064649091 38508190026923824596973637)
                  ·
                    refine ⟨7220285630048217111932557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38508190026923824596973637 7220285630048217111932557)
                    ·
                      refine ⟨2707607111268081416974709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220285630048217111932557 2707607111268081416974709)
                      ·
                        rfl

theorem cell23_5273046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_5273046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273046 prefixEnd_5273046 := by exact prefixLift 5273046
  have htrace : WordTrace (prefixWord ++ tailWord_5273046) baseStart_5273046 baseEnd_5273046 := by
    simpa [prefixWord, tailWord_5273046, baseEnd_5273046] using wordTrace_append hprefix tailTrace_5273046
  have hstable : (prefixWord ++ tailWord_5273046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273046).length < 2 ^ (prefixWord ++ tailWord_5273046).sum := by decide
  have hdescent : baseEnd_5273046 < baseStart_5273046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273053 : List Nat := [1, 4, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_5273053 : Nat := 118140960795 + 5273053 * 2 ^ 59
def prefixEnd_5273053 : Nat := 4983230072969 + 3 ^ 40 * 5273053 * 2
def baseEnd_5273053 : Nat := 902536901877554296529059

theorem tailTrace_5273053 : CollatzResearch.WordTrace tailWord_5273053 prefixEnd_5273053 902536901877554296529059 := by
  unfold tailWord_5273053
  simp only [CollatzResearch.WordTrace]
  refine ⟨192324042965637021599807813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128216028643758014399871875 192324042965637021599807813)
  ·
    refine ⟨36060758056056941549963965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192324042965637021599807813 36060758056056941549963965)
    ·
      refine ⟨13522784271021353081236487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36060758056056941549963965 13522784271021353081236487)
      ·
        refine ⟨20284176406532029621854731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13522784271021353081236487 20284176406532029621854731)
        ·
          refine ⟨30426264609798044432782097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20284176406532029621854731 30426264609798044432782097)
          ·
            refine ⟨22819698457348533324586573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30426264609798044432782097 22819698457348533324586573)
            ·
              refine ⟨8557386921505699996719965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22819698457348533324586573 8557386921505699996719965)
              ·
                refine ⟨3209020095564637498769987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8557386921505699996719965 3209020095564637498769987)
                ·
                  refine ⟨4813530143346956248154981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209020095564637498769987 4813530143346956248154981)
                  ·
                    refine ⟨902536901877554296529059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4813530143346956248154981 902536901877554296529059)
                    ·
                      rfl

theorem cell23_5273053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_5273053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273053 prefixEnd_5273053 := by exact prefixLift 5273053
  have htrace : WordTrace (prefixWord ++ tailWord_5273053) baseStart_5273053 baseEnd_5273053 := by
    simpa [prefixWord, tailWord_5273053, baseEnd_5273053] using wordTrace_append hprefix tailTrace_5273053
  have hstable : (prefixWord ++ tailWord_5273053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273053).length < 2 ^ (prefixWord ++ tailWord_5273053).sum := by decide
  have hdescent : baseEnd_5273053 < baseStart_5273053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273109 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_5273109 : Nat := 118140960795 + 5273109 * 2 ^ 59
def prefixEnd_5273109 : Nat := 4983230072969 + 3 ^ 40 * 5273109 * 2
def baseEnd_5273109 : Nat := 902546486849771556828973

theorem tailTrace_5273109 : CollatzResearch.WordTrace tailWord_5273109 prefixEnd_5273109 902546486849771556828973 := by
  unfold tailWord_5273109
  simp only [CollatzResearch.WordTrace]
  refine ⟨192326085453434143163846381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128217390302289428775897587 192326085453434143163846381)
  ·
    refine ⟨72122282045037803686442393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192326085453434143163846381 72122282045037803686442393)
    ·
      refine ⟨54091711533778352764831795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72122282045037803686442393 54091711533778352764831795)
      ·
        refine ⟨81137567300667529147247693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54091711533778352764831795 81137567300667529147247693)
        ·
          refine ⟨30426587737750323430217885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81137567300667529147247693 30426587737750323430217885)
          ·
            refine ⟨11409970401656371286331707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30426587737750323430217885 11409970401656371286331707)
            ·
              refine ⟨17114955602484556929497561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11409970401656371286331707 17114955602484556929497561)
              ·
                refine ⟨12836216701863417697123171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17114955602484556929497561 12836216701863417697123171)
                ·
                  refine ⟨19254325052795126545684757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12836216701863417697123171 19254325052795126545684757)
                  ·
                    refine ⟨902546486849771556828973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19254325052795126545684757 902546486849771556828973)
                    ·
                      rfl

theorem cell23_5273109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_5273109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273109 prefixEnd_5273109 := by exact prefixLift 5273109
  have htrace : WordTrace (prefixWord ++ tailWord_5273109) baseStart_5273109 baseEnd_5273109 := by
    simpa [prefixWord, tailWord_5273109, baseEnd_5273109] using wordTrace_append hprefix tailTrace_5273109
  have hstable : (prefixWord ++ tailWord_5273109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273109).length < 2 ^ (prefixWord ++ tailWord_5273109).sum := by decide
  have hdescent : baseEnd_5273109 < baseStart_5273109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273119 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 5]
def baseStart_5273119 : Nat := 118140960795 + 5273119 * 2 ^ 59
def prefixEnd_5273119 : Nat := 4983230072969 + 3 ^ 40 * 5273119 * 2
def baseEnd_5273119 : Nat := 2707644595355859631361873

theorem tailTrace_5273119 : CollatzResearch.WordTrace tailWord_5273119 prefixEnd_5273119 2707644595355859631361873 := by
  unfold tailWord_5273119
  simp only [CollatzResearch.WordTrace]
  refine ⟨192326450183397914871710411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128217633455598609914473607 192326450183397914871710411)
  ·
    refine ⟨288489675275096872307565617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192326450183397914871710411 288489675275096872307565617)
    ·
      refine ⟨216367256456322654230674213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288489675275096872307565617 216367256456322654230674213)
      ·
        refine ⟨40568860585560497668251415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216367256456322654230674213 40568860585560497668251415)
        ·
          refine ⟨60853290878340746502377123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40568860585560497668251415 60853290878340746502377123)
          ·
            refine ⟨91279936317511119753565685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60853290878340746502377123 91279936317511119753565685)
            ·
              refine ⟨8557494029766667476896783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91279936317511119753565685 8557494029766667476896783)
              ·
                refine ⟨12836241044650001215345175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8557494029766667476896783 12836241044650001215345175)
                ·
                  refine ⟨19254361566975001823017763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12836241044650001215345175 19254361566975001823017763)
                  ·
                    refine ⟨28881542350462502734526645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19254361566975001823017763 28881542350462502734526645)
                    ·
                      refine ⟨2707644595355859631361873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28881542350462502734526645 2707644595355859631361873)
                      ·
                        rfl

theorem cell23_5273119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_5273119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273119 prefixEnd_5273119 := by exact prefixLift 5273119
  have htrace : WordTrace (prefixWord ++ tailWord_5273119) baseStart_5273119 baseEnd_5273119 := by
    simpa [prefixWord, tailWord_5273119, baseEnd_5273119] using wordTrace_append hprefix tailTrace_5273119
  have hstable : (prefixWord ++ tailWord_5273119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273119).length < 2 ^ (prefixWord ++ tailWord_5273119).sum := by decide
  have hdescent : baseEnd_5273119 < baseStart_5273119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273139 : List Nat := [1, 1, 1, 2, 4, 5, 1, 8]
def baseStart_5273139 : Nat := 118140960795 + 5273139 * 2 ^ 59
def prefixEnd_5273139 : Nat := 4983230072969 + 3 ^ 40 * 5273139 * 2
def baseEnd_5273139 : Nat := 100283513517368501967103

theorem tailTrace_5273139 : CollatzResearch.WordTrace tailWord_5273139 prefixEnd_5273139 100283513517368501967103 := by
  unfold tailWord_5273139
  simp only [CollatzResearch.WordTrace]
  refine ⟨192327179643325458287438471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128218119762216972191625647 192327179643325458287438471)
  ·
    refine ⟨288490769464988187431157707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192327179643325458287438471 288490769464988187431157707)
    ·
      refine ⟨432736154197482281146736561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288490769464988187431157707 432736154197482281146736561)
      ·
        refine ⟨324552115648111710860052421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432736154197482281146736561 324552115648111710860052421)
        ·
          refine ⟨60853521684020945786259829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 324552115648111710860052421 60853521684020945786259829)
          ·
            refine ⟨5705017657876963667461859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60853521684020945786259829 5705017657876963667461859)
            ·
              refine ⟨8557526486815445501192789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5705017657876963667461859 8557526486815445501192789)
              ·
                refine ⟨100283513517368501967103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8557526486815445501192789 100283513517368501967103)
                ·
                  rfl

theorem cell23_5273139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 8].length) (baseStart_5273139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273139 prefixEnd_5273139 := by exact prefixLift 5273139
  have htrace : WordTrace (prefixWord ++ tailWord_5273139) baseStart_5273139 baseEnd_5273139 := by
    simpa [prefixWord, tailWord_5273139, baseEnd_5273139] using wordTrace_append hprefix tailTrace_5273139
  have hstable : (prefixWord ++ tailWord_5273139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273139).length < 2 ^ (prefixWord ++ tailWord_5273139).sum := by decide
  have hdescent : baseEnd_5273139 < baseStart_5273139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273152 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 4, 7]
def baseStart_5273152 : Nat := 118140960795 + 5273152 * 2 ^ 59
def prefixEnd_5273152 : Nat := 4983230072969 + 3 ^ 40 * 5273152 * 2
def baseEnd_5273152 : Nat := 902553846739152667416407

theorem tailTrace_5273152 : CollatzResearch.WordTrace tailWord_5273152 prefixEnd_5273152 902553846739152667416407 := by
  unfold tailWord_5273152
  simp only [CollatzResearch.WordTrace]
  refine ⟨96163826896139180753830855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128218435861518907671774473 96163826896139180753830855)
  ·
    refine ⟨144245740344208771130746283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96163826896139180753830855 144245740344208771130746283)
    ·
      refine ⟨216368610516313156696119425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144245740344208771130746283 216368610516313156696119425)
      ·
        refine ⟨162276457887234867522089569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216368610516313156696119425 162276457887234867522089569)
        ·
          refine ⟨121707343415426150641567177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162276457887234867522089569 121707343415426150641567177)
          ·
            refine ⟨91280507561569612981175383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121707343415426150641567177 91280507561569612981175383)
            ·
              refine ⟨136920761342354419471763075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91280507561569612981175383 136920761342354419471763075)
              ·
                refine ⟨205381142013531629207644613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136920761342354419471763075 205381142013531629207644613)
                ·
                  refine ⟨38508964127537180476433365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205381142013531629207644613 38508964127537180476433365)
                  ·
                    refine ⟨902553846739152667416407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38508964127537180476433365 902553846739152667416407)
                    ·
                      rfl

theorem cell23_5273152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_5273152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273152 prefixEnd_5273152 := by exact prefixLift 5273152
  have htrace : WordTrace (prefixWord ++ tailWord_5273152) baseStart_5273152 baseEnd_5273152 := by
    simpa [prefixWord, tailWord_5273152, baseEnd_5273152] using wordTrace_append hprefix tailTrace_5273152
  have hstable : (prefixWord ++ tailWord_5273152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273152).length < 2 ^ (prefixWord ++ tailWord_5273152).sum := by decide
  have hdescent : baseEnd_5273152 < baseStart_5273152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273166 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_5273166 : Nat := 118140960795 + 5273166 * 2 ^ 59
def prefixEnd_5273166 : Nat := 4983230072969 + 3 ^ 40 * 5273166 * 2
def baseEnd_5273166 : Nat := 2707668728946620947474157

theorem tailTrace_5273166 : CollatzResearch.WordTrace tailWord_5273166 prefixEnd_5273166 2707668728946620947474157 := by
  unfold tailWord_5273166
  simp only [CollatzResearch.WordTrace]
  refine ⟨24041020551778455237333919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128218776276151761265780901 24041020551778455237333919)
  ·
    refine ⟨36061530827667682856000879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24041020551778455237333919 36061530827667682856000879)
    ·
      refine ⟨54092296241501524284001319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36061530827667682856000879 54092296241501524284001319)
      ·
        refine ⟨81138444362252286426001979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54092296241501524284001319 81138444362252286426001979)
        ·
          refine ⟨121707666543378429639002969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81138444362252286426001979 121707666543378429639002969)
          ·
            refine ⟨91280749907533822229252227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121707666543378429639002969 91280749907533822229252227)
            ·
              refine ⟨136921124861300733343878341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91280749907533822229252227 136921124861300733343878341)
              ·
                refine ⟨25672710911493887501977189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136921124861300733343878341 25672710911493887501977189)
                ·
                  refine ⟨4813633295905103906620723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25672710911493887501977189 4813633295905103906620723)
                  ·
                    refine ⟨7220449943857655859931085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4813633295905103906620723 7220449943857655859931085)
                    ·
                      refine ⟨2707668728946620947474157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220449943857655859931085 2707668728946620947474157)
                      ·
                        rfl

theorem cell23_5273166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_5273166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273166 prefixEnd_5273166 := by exact prefixLift 5273166
  have htrace : WordTrace (prefixWord ++ tailWord_5273166) baseStart_5273166 baseEnd_5273166 := by
    simpa [prefixWord, tailWord_5273166, baseEnd_5273166] using wordTrace_append hprefix tailTrace_5273166
  have hstable : (prefixWord ++ tailWord_5273166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273166).length < 2 ^ (prefixWord ++ tailWord_5273166).sum := by decide
  have hdescent : baseEnd_5273166 < baseStart_5273166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273170 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_5273170 : Nat := 118140960795 + 5273170 * 2 ^ 59
def prefixEnd_5273170 : Nat := 4983230072969 + 3 ^ 40 * 5273170 * 2
def baseEnd_5273170 : Nat := 2707670782869238931824139

theorem tailTrace_5273170 : CollatzResearch.WordTrace tailWord_5273170 prefixEnd_5273170 2707670782869238931824139 := by
  unfold tailWord_5273170
  simp only [CollatzResearch.WordTrace]
  refine ⟨48082077576553287645454241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128218873537475433721211309 48082077576553287645454241)
  ·
    refine ⟨36061558182414965734090681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48082077576553287645454241 36061558182414965734090681)
    ·
      refine ⟨27046168636811224300568011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36061558182414965734090681 27046168636811224300568011)
      ·
        refine ⟨40569252955216836450852017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27046168636811224300568011 40569252955216836450852017)
        ·
          refine ⟨30426939716412627338139013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40569252955216836450852017 30426939716412627338139013)
          ·
            refine ⟨5705051196827367625901065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30426939716412627338139013 5705051196827367625901065)
            ·
              refine ⟨4278788397620525719425799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5705051196827367625901065 4278788397620525719425799)
              ·
                refine ⟨6418182596430788579138699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4278788397620525719425799 6418182596430788579138699)
                ·
                  refine ⟨9627273894646182868708049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418182596430788579138699 9627273894646182868708049)
                  ·
                    refine ⟨7220455420984637151531037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9627273894646182868708049 7220455420984637151531037)
                    ·
                      refine ⟨2707670782869238931824139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220455420984637151531037 2707670782869238931824139)
                      ·
                        rfl

theorem cell23_5273170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_5273170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273170 prefixEnd_5273170 := by exact prefixLift 5273170
  have htrace : WordTrace (prefixWord ++ tailWord_5273170) baseStart_5273170 baseEnd_5273170 := by
    simpa [prefixWord, tailWord_5273170, baseEnd_5273170] using wordTrace_append hprefix tailTrace_5273170
  have hstable : (prefixWord ++ tailWord_5273170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273170).length < 2 ^ (prefixWord ++ tailWord_5273170).sum := by decide
  have hdescent : baseEnd_5273170 < baseStart_5273170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273200 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 2, 1, 3]
def baseStart_5273200 : Nat := 118140960795 + 5273200 * 2 ^ 59
def prefixEnd_5273200 : Nat := 4983230072969 + 3 ^ 40 * 5273200 * 2
def baseEnd_5273200 : Nat := 2707686187288873814449001

theorem tailTrace_5273200 : CollatzResearch.WordTrace tailWord_5273200 prefixEnd_5273200 2707686187288873814449001 := by
  unfold tailWord_5273200
  simp only [CollatzResearch.WordTrace]
  refine ⟨96164702248052232852704527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128219602997402977136939369 96164702248052232852704527)
  ·
    refine ⟨144247053372078349279056791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96164702248052232852704527 144247053372078349279056791)
    ·
      refine ⟨216370580058117523918585187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144247053372078349279056791 216370580058117523918585187)
      ·
        refine ⟨324555870087176285877877781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216370580058117523918585187 324555870087176285877877781)
        ·
          refine ⟨15213556410336388400525521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 324555870087176285877877781 15213556410336388400525521)
          ·
            refine ⟨11410167307752291300394141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15213556410336388400525521 11410167307752291300394141)
            ·
              refine ⟨4278812740407109237647803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11410167307752291300394141 4278812740407109237647803)
              ·
                refine ⟨6418219110610663856471705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4278812740407109237647803 6418219110610663856471705)
                ·
                  refine ⟨4813664332957997892353779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6418219110610663856471705 4813664332957997892353779)
                  ·
                    refine ⟨7220496499436996838530669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4813664332957997892353779 7220496499436996838530669)
                    ·
                      refine ⟨2707686187288873814449001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220496499436996838530669 2707686187288873814449001)
                      ·
                        rfl

theorem cell23_5273200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 1, 3].length) (baseStart_5273200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273200 prefixEnd_5273200 := by exact prefixLift 5273200
  have htrace : WordTrace (prefixWord ++ tailWord_5273200) baseStart_5273200 baseEnd_5273200 := by
    simpa [prefixWord, tailWord_5273200, baseEnd_5273200] using wordTrace_append hprefix tailTrace_5273200
  have hstable : (prefixWord ++ tailWord_5273200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273200).length < 2 ^ (prefixWord ++ tailWord_5273200).sum := by decide
  have hdescent : baseEnd_5273200 < baseStart_5273200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273209 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_5273209 : Nat := 118140960795 + 5273209 * 2 ^ 59
def prefixEnd_5273209 : Nat := 4983230072969 + 3 ^ 40 * 5273209 * 2
def baseEnd_5273209 : Nat := 2707690808614764279236459

theorem tailTrace_5273209 : CollatzResearch.WordTrace tailWord_5273209 prefixEnd_5273209 2707690808614764279236459 := by
  unfold tailWord_5273209
  simp only [CollatzResearch.WordTrace]
  refine ⟨192329732753071860242486681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128219821835381240161657787 192329732753071860242486681)
  ·
    refine ⟨144247299564803895181865011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192329732753071860242486681 144247299564803895181865011)
    ·
      refine ⟨216370949347205842772797517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144247299564803895181865011 216370949347205842772797517)
      ·
        refine ⟨81139106005202191039799069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216370949347205842772797517 81139106005202191039799069)
        ·
          refine ⟨30427164751950821639924651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81139106005202191039799069 30427164751950821639924651)
          ·
            refine ⟨45640747127926232459886977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30427164751950821639924651 45640747127926232459886977)
            ·
              refine ⟨34230560345944674344915233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45640747127926232459886977 34230560345944674344915233)
              ·
                refine ⟨25672920259458505758686425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34230560345944674344915233 25672920259458505758686425)
                ·
                  refine ⟨19254690194593879319014819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25672920259458505758686425 19254690194593879319014819)
                  ·
                    refine ⟨28882035291890818978522229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19254690194593879319014819 28882035291890818978522229)
                    ·
                      refine ⟨2707690808614764279236459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28882035291890818978522229 2707690808614764279236459)
                      ·
                        rfl

theorem cell23_5273209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_5273209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273209 prefixEnd_5273209 := by exact prefixLift 5273209
  have htrace : WordTrace (prefixWord ++ tailWord_5273209) baseStart_5273209 baseEnd_5273209 := by
    simpa [prefixWord, tailWord_5273209, baseEnd_5273209] using wordTrace_append hprefix tailTrace_5273209
  have hstable : (prefixWord ++ tailWord_5273209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273209).length < 2 ^ (prefixWord ++ tailWord_5273209).sum := by decide
  have hdescent : baseEnd_5273209 < baseStart_5273209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273223 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_5273223 : Nat := 118140960795 + 5273223 * 2 ^ 59
def prefixEnd_5273223 : Nat := 4983230072969 + 3 ^ 40 * 5273223 * 2
def baseEnd_5273223 : Nat := 2707697997343927224461395

theorem tailTrace_5273223 : CollatzResearch.WordTrace tailWord_5273223 prefixEnd_5273223 2707697997343927224461395 := by
  unfold tailWord_5273223
  simp only [CollatzResearch.WordTrace]
  refine ⟨192330243375021140633496323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128220162250014093755664215 192330243375021140633496323)
  ·
    refine ⟨288495365062531710950244485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192330243375021140633496323 288495365062531710950244485)
    ·
      refine ⟨54092880949224695803170841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288495365062531710950244485 54092880949224695803170841)
      ·
        refine ⟨40569660711918521852378131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54092880949224695803170841 40569660711918521852378131)
        ·
          refine ⟨60854491067877782778567197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40569660711918521852378131 60854491067877782778567197)
          ·
            refine ⟨22820434150454168541962699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60854491067877782778567197 22820434150454168541962699)
            ·
              refine ⟨34230651225681252812944049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22820434150454168541962699 34230651225681252812944049)
              ·
                refine ⟨25672988419260939609708037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34230651225681252812944049 25672988419260939609708037)
                ·
                  refine ⟨4813685328611426176820257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25672988419260939609708037 4813685328611426176820257)
                  ·
                    refine ⟨3610263996458569632615193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4813685328611426176820257 3610263996458569632615193)
                    ·
                      refine ⟨2707697997343927224461395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3610263996458569632615193 2707697997343927224461395)
                      ·
                        rfl

theorem cell23_5273223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_5273223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273223 prefixEnd_5273223 := by exact prefixLift 5273223
  have htrace : WordTrace (prefixWord ++ tailWord_5273223) baseStart_5273223 baseEnd_5273223 := by
    simpa [prefixWord, tailWord_5273223, baseEnd_5273223] using wordTrace_append hprefix tailTrace_5273223
  have hstable : (prefixWord ++ tailWord_5273223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273223).length < 2 ^ (prefixWord ++ tailWord_5273223).sum := by decide
  have hdescent : baseEnd_5273223 < baseStart_5273223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273226 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5273226 : Nat := 118140960795 + 5273226 * 2 ^ 59
def prefixEnd_5273226 : Nat := 4983230072969 + 3 ^ 40 * 5273226 * 2
def baseEnd_5273226 : Nat := 2707699537785890712723881

theorem tailTrace_5273226 : CollatzResearch.WordTrace tailWord_5273226 prefixEnd_5273226 2707699537785890712723881 := by
  unfold tailWord_5273226
  simp only [CollatzResearch.WordTrace]
  refine ⟨48082588198502568036463883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128220235196006848097237021 48082588198502568036463883)
  ·
    refine ⟨72123882297753852054695825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48082588198502568036463883 72123882297753852054695825)
    ·
      refine ⟨54092911723315389041021869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72123882297753852054695825 54092911723315389041021869)
      ·
        refine ⟨20284841896243270890383201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54092911723315389041021869 20284841896243270890383201)
        ·
          refine ⟨15213631422182453167787401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20284841896243270890383201 15213631422182453167787401)
          ·
            refine ⟨11410223566636839875840551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15213631422182453167787401 11410223566636839875840551)
            ·
              refine ⟨17115335349955259813760827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11410223566636839875840551 17115335349955259813760827)
              ·
                refine ⟨25673003024932889720641241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17115335349955259813760827 25673003024932889720641241)
                ·
                  refine ⟨19254752268699667290480931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25673003024932889720641241 19254752268699667290480931)
                  ·
                    refine ⟨28882128403049500935721397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19254752268699667290480931 28882128403049500935721397)
                    ·
                      refine ⟨2707699537785890712723881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28882128403049500935721397 2707699537785890712723881)
                      ·
                        rfl

theorem cell23_5273226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5273226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273226 prefixEnd_5273226 := by exact prefixLift 5273226
  have htrace : WordTrace (prefixWord ++ tailWord_5273226) baseStart_5273226 baseEnd_5273226 := by
    simpa [prefixWord, tailWord_5273226, baseEnd_5273226] using wordTrace_append hprefix tailTrace_5273226
  have hstable : (prefixWord ++ tailWord_5273226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273226).length < 2 ^ (prefixWord ++ tailWord_5273226).sum := by decide
  have hdescent : baseEnd_5273226 < baseStart_5273226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273276 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_5273276 : Nat := 118140960795 + 5273276 * 2 ^ 59
def prefixEnd_5273276 : Nat := 4983230072969 + 3 ^ 40 * 5273276 * 2
def baseEnd_5273276 : Nat := 902575070606205172366217

theorem tailTrace_5273276 : CollatzResearch.WordTrace tailWord_5273276 prefixEnd_5273276 902575070606205172366217 := by
  unfold tailWord_5273276
  simp only [CollatzResearch.WordTrace]
  refine ⟨96166088221914565342587841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128221450962552753790117121 96166088221914565342587841)
  ·
    refine ⟨72124566166435924006940881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96166088221914565342587841 72124566166435924006940881)
    ·
      refine ⟨54093424624826943005205661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72124566166435924006940881 54093424624826943005205661)
      ·
        refine ⟨20285034234310103626952123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54093424624826943005205661 20285034234310103626952123)
        ·
          refine ⟨30427551351465155440428185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20285034234310103626952123 30427551351465155440428185)
          ·
            refine ⟨22820663513598866580321139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30427551351465155440428185 22820663513598866580321139)
            ·
              refine ⟨34230995270398299870481709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22820663513598866580321139 34230995270398299870481709)
              ·
                refine ⟨12836623226399362451430641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34230995270398299870481709 12836623226399362451430641)
                ·
                  refine ⟨9627467419799521838572981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12836623226399362451430641 9627467419799521838572981)
                  ·
                    refine ⟨902575070606205172366217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9627467419799521838572981 902575070606205172366217)
                    ·
                      rfl

theorem cell23_5273276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_5273276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273276 prefixEnd_5273276 := by exact prefixLift 5273276
  have htrace : WordTrace (prefixWord ++ tailWord_5273276) baseStart_5273276 baseEnd_5273276 := by
    simpa [prefixWord, tailWord_5273276, baseEnd_5273276] using wordTrace_append hprefix tailTrace_5273276
  have hstable : (prefixWord ++ tailWord_5273276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273276).length < 2 ^ (prefixWord ++ tailWord_5273276).sum := by decide
  have hdescent : baseEnd_5273276 < baseStart_5273276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273316 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_5273316 : Nat := 118140960795 + 5273316 * 2 ^ 59
def prefixEnd_5273316 : Nat := 4983230072969 + 3 ^ 40 * 5273316 * 2
def baseEnd_5273316 : Nat := 2707745751044795360598467

theorem tailTrace_5273316 : CollatzResearch.WordTrace tailWord_5273316 prefixEnd_5273316 2707745751044795360598467 := by
  unfold tailWord_5273316
  simp only [CollatzResearch.WordTrace]
  refine ⟨96166817681842108758315901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128222423575789478344421201 96166817681842108758315901)
  ·
    refine ⟨36062556630690790784368463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96166817681842108758315901 36062556630690790784368463)
    ·
      refine ⟨54093834946036186176552695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36062556630690790784368463 54093834946036186176552695)
      ·
        refine ⟨81140752419054279264829043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54093834946036186176552695 81140752419054279264829043)
        ·
          refine ⟨121711128628581418897243565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81140752419054279264829043 121711128628581418897243565)
          ·
            refine ⟨45641673235718032086466337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121711128628581418897243565 45641673235718032086466337)
            ·
              refine ⟨34231254926788524064849753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45641673235718032086466337 34231254926788524064849753)
              ·
                refine ⟨25673441195091393048637315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34231254926788524064849753 25673441195091393048637315)
                ·
                  refine ⟨38510161792637089572955973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25673441195091393048637315 38510161792637089572955973)
                  ·
                    refine ⟨7220655336119454294929245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38510161792637089572955973 7220655336119454294929245)
                    ·
                      refine ⟨2707745751044795360598467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220655336119454294929245 2707745751044795360598467)
                      ·
                        rfl

theorem cell23_5273316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_5273316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273316 prefixEnd_5273316 := by exact prefixLift 5273316
  have htrace : WordTrace (prefixWord ++ tailWord_5273316) baseStart_5273316 baseEnd_5273316 := by
    simpa [prefixWord, tailWord_5273316, baseEnd_5273316] using wordTrace_append hprefix tailTrace_5273316
  have hstable : (prefixWord ++ tailWord_5273316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273316).length < 2 ^ (prefixWord ++ tailWord_5273316).sum := by decide
  have hdescent : baseEnd_5273316 < baseStart_5273316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273340 : List Nat := [2, 2, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_5273340 : Nat := 118140960795 + 5273340 * 2 ^ 59
def prefixEnd_5273340 : Nat := 4983230072969 + 3 ^ 40 * 5273340 * 2
def baseEnd_5273340 : Nat := 902586024860167755566119

theorem tailTrace_5273340 : CollatzResearch.WordTrace tailWord_5273340 prefixEnd_5273340 902586024860167755566119 := by
  unfold tailWord_5273340
  simp only [CollatzResearch.WordTrace]
  refine ⟨96167255357798634807752737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128223007143731513077003649 96167255357798634807752737)
  ·
    refine ⟨72125441518348976105814553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96167255357798634807752737 72125441518348976105814553)
    ·
      refine ⟨54094081138761732079360915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72125441518348976105814553 54094081138761732079360915)
      ·
        refine ⟨81141121708142598119041373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54094081138761732079360915 81141121708142598119041373)
        ·
          refine ⟨30427920640553474294640515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81141121708142598119041373 30427920640553474294640515)
          ·
            refine ⟨45641880960830211441960773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30427920640553474294640515 45641880960830211441960773)
            ·
              refine ⟨8557852680155664645367645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45641880960830211441960773 8557852680155664645367645)
              ·
                refine ⟨3209194755058374242012867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8557852680155664645367645 3209194755058374242012867)
                ·
                  refine ⟨4813792132587561363019301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209194755058374242012867 4813792132587561363019301)
                  ·
                    refine ⟨902586024860167755566119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4813792132587561363019301 902586024860167755566119)
                    ·
                      rfl

theorem cell23_5273340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_5273340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273340 prefixEnd_5273340 := by exact prefixLift 5273340
  have htrace : WordTrace (prefixWord ++ tailWord_5273340) baseStart_5273340 baseEnd_5273340 := by
    simpa [prefixWord, tailWord_5273340, baseEnd_5273340] using wordTrace_append hprefix tailTrace_5273340
  have hstable : (prefixWord ++ tailWord_5273340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273340).length < 2 ^ (prefixWord ++ tailWord_5273340).sum := by decide
  have hdescent : baseEnd_5273340 < baseStart_5273340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273359 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_5273359 : Nat := 118140960795 + 5273359 * 2 ^ 59
def prefixEnd_5273359 : Nat := 4983230072969 + 3 ^ 40 * 5273359 * 2
def baseEnd_5273359 : Nat := 2707767830712938692360769

theorem tailTrace_5273359 : CollatzResearch.WordTrace tailWord_5273359 prefixEnd_5273359 2707767830712938692360769 := by
  unfold tailWord_5273359
  simp only [CollatzResearch.WordTrace]
  refine ⟨192335203702528435860447131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128223469135018957240298087 192335203702528435860447131)
  ·
    refine ⟨288502805553792653790670697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192335203702528435860447131 288502805553792653790670697)
    ·
      refine ⟨216377104165344490343003023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288502805553792653790670697 216377104165344490343003023)
      ·
        refine ⟨324565656248016735514504535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216377104165344490343003023 324565656248016735514504535)
        ·
          refine ⟨486848484372025103271756803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324565656248016735514504535 486848484372025103271756803)
          ·
            refine ⟨730272726558037654907635205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486848484372025103271756803 730272726558037654907635205)
            ·
              refine ⟨136926136229632060295181601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 730272726558037654907635205 136926136229632060295181601)
              ·
                refine ⟨102694602172224045221386201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136926136229632060295181601 102694602172224045221386201)
                ·
                  refine ⟨77020951629168033916039651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102694602172224045221386201 77020951629168033916039651)
                  ·
                    refine ⟨115531427443752050874059477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77020951629168033916039651 115531427443752050874059477)
                    ·
                      refine ⟨2707767830712938692360769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115531427443752050874059477 2707767830712938692360769)
                      ·
                        rfl

theorem cell23_5273359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_5273359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273359 prefixEnd_5273359 := by exact prefixLift 5273359
  have htrace : WordTrace (prefixWord ++ tailWord_5273359) baseStart_5273359 baseEnd_5273359 := by
    simpa [prefixWord, tailWord_5273359, baseEnd_5273359] using wordTrace_append hprefix tailTrace_5273359
  have hstable : (prefixWord ++ tailWord_5273359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273359).length < 2 ^ (prefixWord ++ tailWord_5273359).sum := by decide
  have hdescent : baseEnd_5273359 < baseStart_5273359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273380 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_5273380 : Nat := 118140960795 + 5273380 * 2 ^ 59
def prefixEnd_5273380 : Nat := 4983230072969 + 3 ^ 40 * 5273380 * 2
def baseEnd_5273380 : Nat := 2707778613806683110198173

theorem tailTrace_5273380 : CollatzResearch.WordTrace tailWord_5273380 prefixEnd_5273380 2707778613806683110198173 := by
  unfold tailWord_5273380
  simp only [CollatzResearch.WordTrace]
  refine ⟨96167984817726178223480797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128223979756968237631307729 96167984817726178223480797)
  ·
    refine ⟨36062994306647316833805299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96167984817726178223480797 36062994306647316833805299)
    ·
      refine ⟨54094491459970975250707949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36062994306647316833805299 54094491459970975250707949)
      ·
        refine ⟨20285434297489115719015481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54094491459970975250707949 20285434297489115719015481)
        ·
          refine ⟨15214075723116836789261611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20285434297489115719015481 15214075723116836789261611)
          ·
            refine ⟨22821113584675255183892417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15214075723116836789261611 22821113584675255183892417)
            ·
              refine ⟨17115835188506441387919313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22821113584675255183892417 17115835188506441387919313)
              ·
                refine ⟨12836876391379831040939485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17115835188506441387919313 12836876391379831040939485)
                ·
                  refine ⟨4813828646767436640352307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12836876391379831040939485 4813828646767436640352307)
                  ·
                    refine ⟨7220742970151154960528461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4813828646767436640352307 7220742970151154960528461)
                    ·
                      refine ⟨2707778613806683110198173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220742970151154960528461 2707778613806683110198173)
                      ·
                        rfl

theorem cell23_5273380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_5273380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273380 prefixEnd_5273380 := by exact prefixLift 5273380
  have htrace : WordTrace (prefixWord ++ tailWord_5273380) baseStart_5273380 baseEnd_5273380 := by
    simpa [prefixWord, tailWord_5273380, baseEnd_5273380] using wordTrace_append hprefix tailTrace_5273380
  have hstable : (prefixWord ++ tailWord_5273380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273380).length < 2 ^ (prefixWord ++ tailWord_5273380).sum := by decide
  have hdescent : baseEnd_5273380 < baseStart_5273380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273413 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_5273413 : Nat := 118140960795 + 5273413 * 2 ^ 59
def prefixEnd_5273413 : Nat := 4983230072969 + 3 ^ 40 * 5273413 * 2
def baseEnd_5273413 : Nat := 902598519556093827028507

theorem tailTrace_5273413 : CollatzResearch.WordTrace tailWord_5273413 prefixEnd_5273413 902598519556093827028507 := by
  unfold tailWord_5273413
  simp only [CollatzResearch.WordTrace]
  refine ⟨192337173244332803082912893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128224782162888535388608595 192337173244332803082912893)
  ·
    refine ⟨72126439966624801156092335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192337173244332803082912893 72126439966624801156092335)
    ·
      refine ⟨108189659949937201734138503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72126439966624801156092335 108189659949937201734138503)
      ·
        refine ⟨162284489924905802601207755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108189659949937201734138503 162284489924905802601207755)
        ·
          refine ⟨243426734887358703901811633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162284489924905802601207755 243426734887358703901811633)
          ·
            refine ⟨182570051165519027926358725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243426734887358703901811633 182570051165519027926358725)
            ·
              refine ⟨34231884593534817736192261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182570051165519027926358725 34231884593534817736192261)
              ·
                refine ⟨6418478361287778325536049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34231884593534817736192261 6418478361287778325536049)
                ·
                  refine ⟨4813858770965833744152037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6418478361287778325536049 4813858770965833744152037)
                  ·
                    refine ⟨902598519556093827028507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4813858770965833744152037 902598519556093827028507)
                    ·
                      rfl

theorem cell23_5273413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_5273413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273413 prefixEnd_5273413 := by exact prefixLift 5273413
  have htrace : WordTrace (prefixWord ++ tailWord_5273413) baseStart_5273413 baseEnd_5273413 := by
    simpa [prefixWord, tailWord_5273413, baseEnd_5273413] using wordTrace_append hprefix tailTrace_5273413
  have hstable : (prefixWord ++ tailWord_5273413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273413).length < 2 ^ (prefixWord ++ tailWord_5273413).sum := by decide
  have hdescent : baseEnd_5273413 < baseStart_5273413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273414 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5273414 : Nat := 118140960795 + 5273414 * 2 ^ 59
def prefixEnd_5273414 : Nat := 4983230072969 + 3 ^ 40 * 5273414 * 2
def baseEnd_5273414 : Nat := 2707796072148935977173017

theorem tailTrace_5273414 : CollatzResearch.WordTrace tailWord_5273414 prefixEnd_5273414 2707796072148935977173017 := by
  unfold tailWord_5273414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010537803666536882928103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128224806478219453502466197 6010537803666536882928103)
  ·
    refine ⟨9015806705499805324392155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6010537803666536882928103 9015806705499805324392155)
    ·
      refine ⟨13523710058249707986588233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9015806705499805324392155 13523710058249707986588233)
      ·
        refine ⟨10142782543687280989941175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13523710058249707986588233 10142782543687280989941175)
        ·
          refine ⟨15214173815530921484911763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10142782543687280989941175 15214173815530921484911763)
          ·
            refine ⟨22821260723296382227367645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15214173815530921484911763 22821260723296382227367645)
            ·
              refine ⟨8557972771236143335262867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22821260723296382227367645 8557972771236143335262867)
              ·
                refine ⟨12836959156854215002894301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8557972771236143335262867 12836959156854215002894301)
                ·
                  refine ⟨4813859683820330626085363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12836959156854215002894301 4813859683820330626085363)
                  ·
                    refine ⟨7220789525730495939128045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4813859683820330626085363 7220789525730495939128045)
                    ·
                      refine ⟨2707796072148935977173017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220789525730495939128045 2707796072148935977173017)
                      ·
                        rfl

theorem cell23_5273414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5273414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273414 prefixEnd_5273414 := by exact prefixLift 5273414
  have htrace : WordTrace (prefixWord ++ tailWord_5273414) baseStart_5273414 baseEnd_5273414 := by
    simpa [prefixWord, tailWord_5273414, baseEnd_5273414] using wordTrace_append hprefix tailTrace_5273414
  have hstable : (prefixWord ++ tailWord_5273414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273414).length < 2 ^ (prefixWord ++ tailWord_5273414).sum := by decide
  have hdescent : baseEnd_5273414 < baseStart_5273414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273416 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_5273416 : Nat := 118140960795 + 5273416 * 2 ^ 59
def prefixEnd_5273416 : Nat := 4983230072969 + 3 ^ 40 * 5273416 * 2
def baseEnd_5273416 : Nat := 2707797099110244969348007

theorem tailTrace_5273416 : CollatzResearch.WordTrace tailWord_5273416 prefixEnd_5273416 2707797099110244969348007 := by
  unfold tailWord_5273416
  simp only [CollatzResearch.WordTrace]
  refine ⟨96168641331660967297636051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128224855108881289730181401 96168641331660967297636051)
  ·
    refine ⟨144252961997491450946454077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96168641331660967297636051 144252961997491450946454077)
    ·
      refine ⟨54094860749059294104920279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144252961997491450946454077 54094860749059294104920279)
      ·
        refine ⟨81142291123588941157380419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54094860749059294104920279 81142291123588941157380419)
        ·
          refine ⟨121713436685383411736070629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81142291123588941157380419 121713436685383411736070629)
          ·
            refine ⟨22821269378509389700513243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121713436685383411736070629 22821269378509389700513243)
            ·
              refine ⟨34231904067764084550769865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22821269378509389700513243 34231904067764084550769865)
              ·
                refine ⟨25673928050823063413077399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34231904067764084550769865 25673928050823063413077399)
                ·
                  refine ⟨38510892076234595119616099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25673928050823063413077399 38510892076234595119616099)
                  ·
                    refine ⟨57766338114351892679424149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38510892076234595119616099 57766338114351892679424149)
                    ·
                      refine ⟨2707797099110244969348007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57766338114351892679424149 2707797099110244969348007)
                      ·
                        rfl

theorem cell23_5273416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_5273416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273416 prefixEnd_5273416 := by exact prefixLift 5273416
  have htrace : WordTrace (prefixWord ++ tailWord_5273416) baseStart_5273416 baseEnd_5273416 := by
    simpa [prefixWord, tailWord_5273416, baseEnd_5273416] using wordTrace_append hprefix tailTrace_5273416
  have hstable : (prefixWord ++ tailWord_5273416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273416).length < 2 ^ (prefixWord ++ tailWord_5273416).sum := by decide
  have hdescent : baseEnd_5273416 < baseStart_5273416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273426 : List Nat := [3, 2, 2, 1, 1, 3, 1, 10]
def baseStart_5273426 : Nat := 118140960795 + 5273426 * 2 ^ 59
def prefixEnd_5273426 : Nat := 4983230072969 + 3 ^ 40 * 5273426 * 2
def baseEnd_5273426 : Nat := 100288971626547775193443

theorem tailTrace_5273426 : CollatzResearch.WordTrace tailWord_5273426 prefixEnd_5273426 100288971626547775193443 := by
  unfold tailWord_5273426
  simp only [CollatzResearch.WordTrace]
  refine ⟨48084411848321426575784033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128225098262190470868757421 48084411848321426575784033)
  ·
    refine ⟨36063308886241069931838025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48084411848321426575784033 36063308886241069931838025)
    ·
      refine ⟨27047481664680802448878519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36063308886241069931838025 27047481664680802448878519)
      ·
        refine ⟨40571222497021203673317779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27047481664680802448878519 40571222497021203673317779)
        ·
          refine ⟨60856833745531805509976669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40571222497021203673317779 60856833745531805509976669)
          ·
            refine ⟨22821312654574427066241251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60856833745531805509976669 22821312654574427066241251)
            ·
              refine ⟨34231968981861640599361877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22821312654574427066241251 34231968981861640599361877)
              ·
                refine ⟨100288971626547775193443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34231968981861640599361877 100288971626547775193443)
                ·
                  rfl

theorem cell23_5273426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 10].length) (baseStart_5273426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273426 prefixEnd_5273426 := by exact prefixLift 5273426
  have htrace : WordTrace (prefixWord ++ tailWord_5273426) baseStart_5273426 baseEnd_5273426 := by
    simpa [prefixWord, tailWord_5273426, baseEnd_5273426] using wordTrace_append hprefix tailTrace_5273426
  have hstable : (prefixWord ++ tailWord_5273426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273426).length < 2 ^ (prefixWord ++ tailWord_5273426).sum := by decide
  have hdescent : baseEnd_5273426 < baseStart_5273426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273440 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 3]
def baseStart_5273440 : Nat := 118140960795 + 5273440 * 2 ^ 59
def prefixEnd_5273440 : Nat := 4983230072969 + 3 ^ 40 * 5273440 * 2
def baseEnd_5273440 : Nat := 2707809422645952875447897

theorem tailTrace_5273440 : CollatzResearch.WordTrace tailWord_5273440 prefixEnd_5273440 2707809422645952875447897 := by
  unfold tailWord_5273440
  simp only [CollatzResearch.WordTrace]
  refine ⟨96169079007617493347072887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128225438676823324462763849 96169079007617493347072887)
  ·
    refine ⟨144253618511426240020609331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96169079007617493347072887 144253618511426240020609331)
    ·
      refine ⟨216380427767139360030913997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144253618511426240020609331 216380427767139360030913997)
      ·
        refine ⟨81142660412677260011592749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216380427767139360030913997 81142660412677260011592749)
        ·
          refine ⟨30428497654753972504347281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81142660412677260011592749 30428497654753972504347281)
          ·
            refine ⟨22821373241065479378260461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30428497654753972504347281 22821373241065479378260461)
            ·
              refine ⟨8558014965399554766847673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22821373241065479378260461 8558014965399554766847673)
              ·
                refine ⟨6418511224049666075135755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8558014965399554766847673 6418511224049666075135755)
                ·
                  refine ⟨9627766836074499112703633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418511224049666075135755 9627766836074499112703633)
                  ·
                    refine ⟨7220825127055874334527725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9627766836074499112703633 7220825127055874334527725)
                    ·
                      refine ⟨2707809422645952875447897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220825127055874334527725 2707809422645952875447897)
                      ·
                        rfl

theorem cell23_5273440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_5273440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273440 prefixEnd_5273440 := by exact prefixLift 5273440
  have htrace : WordTrace (prefixWord ++ tailWord_5273440) baseStart_5273440 baseEnd_5273440 := by
    simpa [prefixWord, tailWord_5273440, baseEnd_5273440] using wordTrace_append hprefix tailTrace_5273440
  have hstable : (prefixWord ++ tailWord_5273440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273440).length < 2 ^ (prefixWord ++ tailWord_5273440).sum := by decide
  have hdescent : baseEnd_5273440 < baseStart_5273440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273453 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_5273453 : Nat := 118140960795 + 5273453 * 2 ^ 59
def prefixEnd_5273453 : Nat := 4983230072969 + 3 ^ 40 * 5273453 * 2
def baseEnd_5273453 : Nat := 2707816097894461324585337

theorem tailTrace_5273453 : CollatzResearch.WordTrace tailWord_5273453 prefixEnd_5273453 2707816097894461324585337 := by
  unfold tailWord_5273453
  simp only [CollatzResearch.WordTrace]
  refine ⟨192338632164187889914369013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128225754776125259942912675 192338632164187889914369013)
  ·
    refine ⟨18031746765392614679472095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192338632164187889914369013 18031746765392614679472095)
    ·
      refine ⟨27047620148088922019208143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18031746765392614679472095 27047620148088922019208143)
      ·
        refine ⟨40571430222133383028812215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27047620148088922019208143 40571430222133383028812215)
        ·
          refine ⟨60857145333200074543218323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40571430222133383028812215 60857145333200074543218323)
          ·
            refine ⟨91285717999800111814827485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60857145333200074543218323 91285717999800111814827485)
            ·
              refine ⟨34232144249925041930560307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91285717999800111814827485 34232144249925041930560307)
              ·
                refine ⟨51348216374887562895840461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34232144249925041930560307 51348216374887562895840461)
                ·
                  refine ⟨19255581140582836085940173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51348216374887562895840461 19255581140582836085940173)
                  ·
                    refine ⟨7220842927718563532227565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19255581140582836085940173 7220842927718563532227565)
                    ·
                      refine ⟨2707816097894461324585337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7220842927718563532227565 2707816097894461324585337)
                      ·
                        rfl

theorem cell23_5273453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_5273453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273453 prefixEnd_5273453 := by exact prefixLift 5273453
  have htrace : WordTrace (prefixWord ++ tailWord_5273453) baseStart_5273453 baseEnd_5273453 := by
    simpa [prefixWord, tailWord_5273453, baseEnd_5273453] using wordTrace_append hprefix tailTrace_5273453
  have hstable : (prefixWord ++ tailWord_5273453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273453).length < 2 ^ (prefixWord ++ tailWord_5273453).sum := by decide
  have hdescent : baseEnd_5273453 < baseStart_5273453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273466 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_5273466 : Nat := 118140960795 + 5273466 * 2 ^ 59
def prefixEnd_5273466 : Nat := 4983230072969 + 3 ^ 40 * 5273466 * 2
def baseEnd_5273466 : Nat := 2707822773142969773722777

theorem tailTrace_5273466 : CollatzResearch.WordTrace tailWord_5273466 prefixEnd_5273466 2707822773142969773722777 := by
  unfold tailWord_5273466
  simp only [CollatzResearch.WordTrace]
  refine ⟨48084776578285198283648063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128226070875427195423061501 48084776578285198283648063)
  ·
    refine ⟨72127164867427797425472095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48084776578285198283648063 72127164867427797425472095)
    ·
      refine ⟨108190747301141696138208143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72127164867427797425472095 108190747301141696138208143)
      ·
        refine ⟨162286120951712544207312215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108190747301141696138208143 162286120951712544207312215)
        ·
          refine ⟨243429181427568816310968323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162286120951712544207312215 243429181427568816310968323)
          ·
            refine ⟨365143772141353224466452485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243429181427568816310968323 365143772141353224466452485)
            ·
              refine ⟨68464457276503729587459841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 365143772141353224466452485 68464457276503729587459841)
              ·
                refine ⟨51348342957377797190594881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68464457276503729587459841 51348342957377797190594881)
                ·
                  refine ⟨38511257218033347892946161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51348342957377797190594881 38511257218033347892946161)
                  ·
                    refine ⟨28883442913525010919709621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38511257218033347892946161 28883442913525010919709621)
                    ·
                      refine ⟨2707822773142969773722777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28883442913525010919709621 2707822773142969773722777)
                      ·
                        rfl

theorem cell23_5273466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_5273466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273466 prefixEnd_5273466 := by exact prefixLift 5273466
  have htrace : WordTrace (prefixWord ++ tailWord_5273466) baseStart_5273466 baseEnd_5273466 := by
    simpa [prefixWord, tailWord_5273466, baseEnd_5273466] using wordTrace_append hprefix tailTrace_5273466
  have hstable : (prefixWord ++ tailWord_5273466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273466).length < 2 ^ (prefixWord ++ tailWord_5273466).sum := by decide
  have hdescent : baseEnd_5273466 < baseStart_5273466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273494 : List Nat := [5, 3, 1, 1, 2, 1, 3, 7]
def baseStart_5273494 : Nat := 118140960795 + 5273494 * 2 ^ 59
def prefixEnd_5273494 : Nat := 4983230072969 + 3 ^ 40 * 5273494 * 2
def baseEnd_5273494 : Nat := 100290264837085024598987

theorem tailTrace_5273494 : CollatzResearch.WordTrace tailWord_5273494 prefixEnd_5273494 100290264837085024598987 := by
  unfold tailWord_5273494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021257972314959619788221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128226751704692902611074357 12021257972314959619788221)
  ·
    refine ⟨4507971739618109857420583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12021257972314959619788221 4507971739618109857420583)
    ·
      refine ⟨6761957609427164786130875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4507971739618109857420583 6761957609427164786130875)
      ·
        refine ⟨10142936414140747179196313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6761957609427164786130875 10142936414140747179196313)
        ·
          refine ⟨7607202310605560384397235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10142936414140747179196313 7607202310605560384397235)
          ·
            refine ⟨11410803465908340576595853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7607202310605560384397235 11410803465908340576595853)
            ·
              refine ⟨4279051299715627716223445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11410803465908340576595853 4279051299715627716223445)
              ·
                refine ⟨100290264837085024598987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4279051299715627716223445 100290264837085024598987)
                ·
                  rfl

theorem cell23_5273494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_5273494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273494 prefixEnd_5273494 := by exact prefixLift 5273494
  have htrace : WordTrace (prefixWord ++ tailWord_5273494) baseStart_5273494 baseEnd_5273494 := by
    simpa [prefixWord, tailWord_5273494, baseEnd_5273494] using wordTrace_append hprefix tailTrace_5273494
  have hstable : (prefixWord ++ tailWord_5273494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273494).length < 2 ^ (prefixWord ++ tailWord_5273494).sum := by decide
  have hdescent : baseEnd_5273494 < baseStart_5273494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273533 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 7]
def baseStart_5273533 : Nat := 118140960795 + 5273533 * 2 ^ 59
def prefixEnd_5273533 : Nat := 4983230072969 + 3 ^ 40 * 5273533 * 2
def baseEnd_5273533 : Nat := 300873019594091223509441

theorem tailTrace_5273533 : CollatzResearch.WordTrace tailWord_5273533 prefixEnd_5273533 300873019594091223509441 := by
  unfold tailWord_5273533
  simp only [CollatzResearch.WordTrace]
  refine ⟨192341550003898063577281253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128227700002598709051520835 192341550003898063577281253)
  ·
    refine ⟨36064040625730886920740235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192341550003898063577281253 36064040625730886920740235)
    ·
      refine ⟨54096060938596330381110353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36064040625730886920740235 54096060938596330381110353)
      ·
        refine ⟨40572045703947247785832765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54096060938596330381110353 40572045703947247785832765)
        ·
          refine ⟨15214517138980217919687287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40572045703947247785832765 15214517138980217919687287)
          ·
            refine ⟨22821775708470326879530931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15214517138980217919687287 22821775708470326879530931)
            ·
              refine ⟨34232663562705490319296397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22821775708470326879530931 34232663562705490319296397)
              ·
                refine ⟨12837248836014558869736149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34232663562705490319296397 12837248836014558869736149)
                ·
                  refine ⟨300873019594091223509441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12837248836014558869736149 300873019594091223509441)
                  ·
                    rfl

theorem cell23_5273533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_5273533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273533 prefixEnd_5273533 := by exact prefixLift 5273533
  have htrace : WordTrace (prefixWord ++ tailWord_5273533) baseStart_5273533 baseEnd_5273533 := by
    simpa [prefixWord, tailWord_5273533, baseEnd_5273533] using wordTrace_append hprefix tailTrace_5273533
  have hstable : (prefixWord ++ tailWord_5273533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273533).length < 2 ^ (prefixWord ++ tailWord_5273533).sum := by decide
  have hdescent : baseEnd_5273533 < baseStart_5273533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273564 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5273564 : Nat := 118140960795 + 5273564 * 2 ^ 59
def prefixEnd_5273564 : Nat := 4983230072969 + 3 ^ 40 * 5273564 * 2
def baseEnd_5273564 : Nat := 2707873094247110390297327

theorem tailTrace_5273564 : CollatzResearch.WordTrace tailWord_5273564 prefixEnd_5273564 2707873094247110390297327 := by
  unfold tailWord_5273564
  simp only [CollatzResearch.WordTrace]
  refine ⟨96171340333392877935829873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128228453777857170581106497 96171340333392877935829873)
  ·
    refine ⟨72128505250044658451872405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96171340333392877935829873 72128505250044658451872405)
    ·
      refine ⟨3381023683595843364931519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72128505250044658451872405 3381023683595843364931519)
      ·
        refine ⟨5071535525393765047397279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3381023683595843364931519 5071535525393765047397279)
        ·
          refine ⟨7607303288090647571095919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5071535525393765047397279 7607303288090647571095919)
          ·
            refine ⟨11410954932135971356643879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7607303288090647571095919 11410954932135971356643879)
            ·
              refine ⟨17116432398203957034965819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11410954932135971356643879 17116432398203957034965819)
              ·
                refine ⟨25674648597305935552448729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17116432398203957034965819 25674648597305935552448729)
                ·
                  refine ⟨19255986447979451664336547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25674648597305935552448729 19255986447979451664336547)
                  ·
                    refine ⟨28883979671969177496504821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19255986447979451664336547 28883979671969177496504821)
                    ·
                      refine ⟨2707873094247110390297327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28883979671969177496504821 2707873094247110390297327)
                      ·
                        rfl

theorem cell23_5273564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5273564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273564 prefixEnd_5273564 := by exact prefixLift 5273564
  have htrace : WordTrace (prefixWord ++ tailWord_5273564) baseStart_5273564 baseEnd_5273564 := by
    simpa [prefixWord, tailWord_5273564, baseEnd_5273564] using wordTrace_append hprefix tailTrace_5273564
  have hstable : (prefixWord ++ tailWord_5273564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273564).length < 2 ^ (prefixWord ++ tailWord_5273564).sum := by decide
  have hdescent : baseEnd_5273564 < baseStart_5273564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273567 : List Nat := [1, 1, 2, 3, 4, 3, 1, 3, 5]
def baseStart_5273567 : Nat := 118140960795 + 5273567 * 2 ^ 59
def prefixEnd_5273567 : Nat := 4983230072969 + 3 ^ 40 * 5273567 * 2
def baseEnd_5273567 : Nat := 300874959409897097617757

theorem tailTrace_5273567 : CollatzResearch.WordTrace tailWord_5273567 prefixEnd_5273567 300874959409897097617757 := by
  unfold tailWord_5273567
  simp only [CollatzResearch.WordTrace]
  refine ⟨192342790085774887384018955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128228526723849924922679303 192342790085774887384018955)
  ·
    refine ⟨288514185128662331076028433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192342790085774887384018955 288514185128662331076028433)
    ·
      refine ⟨216385638846496748307021325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288514185128662331076028433 216385638846496748307021325)
      ·
        refine ⟨81144614567436280615132997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216385638846496748307021325 81144614567436280615132997)
        ·
          refine ⟨15214615231394302615337437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81144614567436280615132997 15214615231394302615337437)
          ·
            refine ⟨5705480711772863480751539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15214615231394302615337437 5705480711772863480751539)
            ·
              refine ⟨8558221067659295221127309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5705480711772863480751539 8558221067659295221127309)
              ·
                refine ⟨3209332900372235707922741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8558221067659295221127309 3209332900372235707922741)
                ·
                  refine ⟨300874959409897097617757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3209332900372235707922741 300874959409897097617757)
                  ·
                    rfl

theorem cell23_5273567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 5].length) (baseStart_5273567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273567 prefixEnd_5273567 := by exact prefixLift 5273567
  have htrace : WordTrace (prefixWord ++ tailWord_5273567) baseStart_5273567 baseEnd_5273567 := by
    simpa [prefixWord, tailWord_5273567, baseEnd_5273567] using wordTrace_append hprefix tailTrace_5273567
  have hstable : (prefixWord ++ tailWord_5273567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273567).length < 2 ^ (prefixWord ++ tailWord_5273567).sum := by decide
  have hdescent : baseEnd_5273567 < baseStart_5273567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5273603 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 3]
def baseStart_5273603 : Nat := 118140960795 + 5273603 * 2 ^ 59
def prefixEnd_5273603 : Nat := 4983230072969 + 3 ^ 40 * 5273603 * 2
def baseEnd_5273603 : Nat := 2707893119992635737709647

theorem tailTrace_5273603 : CollatzResearch.WordTrace tailWord_5273603 prefixEnd_5273603 2707893119992635737709647 := by
  unfold tailWord_5273603
  simp only [CollatzResearch.WordTrace]
  refine ⟨192344103113644465532329463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128229402075762977021552975 192344103113644465532329463)
  ·
    refine ⟨288516154670466698298494195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192344103113644465532329463 288516154670466698298494195)
    ·
      refine ⟨432774232005700047447741293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288516154670466698298494195 432774232005700047447741293)
      ·
        refine ⟨162290337002137517792902985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432774232005700047447741293 162290337002137517792902985)
        ·
          refine ⟨121717752751603138344677239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162290337002137517792902985 121717752751603138344677239)
          ·
            refine ⟨182576629127404707517015859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121717752751603138344677239 182576629127404707517015859)
            ·
              refine ⟨273864943691107061275523789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182576629127404707517015859 273864943691107061275523789)
              ·
                refine ⟨102699353884165147978321421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273864943691107061275523789 102699353884165147978321421)
                ·
                  refine ⟨38512257706561930491870533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102699353884165147978321421 38512257706561930491870533)
                  ·
                    refine ⟨7221048319980361967225725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38512257706561930491870533 7221048319980361967225725)
                    ·
                      refine ⟨2707893119992635737709647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7221048319980361967225725 2707893119992635737709647)
                      ·
                        rfl

theorem cell23_5273603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_5273603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5273603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5273603 prefixEnd_5273603 := by exact prefixLift 5273603
  have htrace : WordTrace (prefixWord ++ tailWord_5273603) baseStart_5273603 baseEnd_5273603 := by
    simpa [prefixWord, tailWord_5273603, baseEnd_5273603] using wordTrace_append hprefix tailTrace_5273603
  have hstable : (prefixWord ++ tailWord_5273603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5273603).length < 2 ^ (prefixWord ++ tailWord_5273603).sum := by decide
  have hdescent : baseEnd_5273603 < baseStart_5273603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5273603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
