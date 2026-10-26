import V185TrunkScan23Chunk0395

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2341881 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2341881 : Nat := 118140960795 + 2341881 * 2 ^ 59
def prefixEnd_2341881 : Nat := 4983230072969 + 3 ^ 40 * 2341881 * 2
def baseEnd_2341881 : Nat := 1202510588632057113517391

theorem tailTrace_2341881 : CollatzResearch.WordTrace tailWord_2341881 prefixEnd_2341881 1202510588632057113517391 := by
  unfold tailWord_2341881
  simp only [CollatzResearch.WordTrace]
  refine ⟨85415417228772573277353497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56943611485848382184902331 85415417228772573277353497)
  ·
    refine ⟨64061562921579429958015123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85415417228772573277353497 64061562921579429958015123)
    ·
      refine ⟨96092344382369144937022685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64061562921579429958015123 96092344382369144937022685)
      ·
        refine ⟨36034629143388429351383507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96092344382369144937022685 36034629143388429351383507)
        ·
          refine ⟨54051943715082644027075261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36034629143388429351383507 54051943715082644027075261)
          ·
            refine ⟨20269478893155991510153223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54051943715082644027075261 20269478893155991510153223)
            ·
              refine ⟨30404218339733987265229835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20269478893155991510153223 30404218339733987265229835)
              ·
                refine ⟨45606327509600980897844753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30404218339733987265229835 45606327509600980897844753)
                ·
                  refine ⟨34204745632200735673383565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45606327509600980897844753 34204745632200735673383565)
                  ·
                    refine ⟨12826779612075275877518837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34204745632200735673383565 12826779612075275877518837)
                    ·
                      refine ⟨1202510588632057113517391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12826779612075275877518837 1202510588632057113517391)
                      ·
                        rfl

theorem cell23_2341881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2341881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341881 prefixEnd_2341881 := by exact prefixLift 2341881
  have htrace : WordTrace (prefixWord ++ tailWord_2341881) baseStart_2341881 baseEnd_2341881 := by
    simpa [prefixWord, tailWord_2341881, baseEnd_2341881] using wordTrace_append hprefix tailTrace_2341881
  have hstable : (prefixWord ++ tailWord_2341881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341881).length < 2 ^ (prefixWord ++ tailWord_2341881).sum := by decide
  have hdescent : baseEnd_2341881 < baseStart_2341881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341891 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 4]
def baseStart_2341891 : Nat := 118140960795 + 2341891 * 2 ^ 59
def prefixEnd_2341891 : Nat := 4983230072969 + 3 ^ 40 * 2341891 * 2
def baseEnd_2341891 : Nat := 1202515723438602074392345

theorem tailTrace_2341891 : CollatzResearch.WordTrace tailWord_2341891 prefixEnd_2341891 1202515723438602074392345 := by
  unfold tailWord_2341891
  simp only [CollatzResearch.WordTrace]
  refine ⟨85415781958736344985217527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56943854639157563323478351 85415781958736344985217527)
  ·
    refine ⟨128123672938104517477826291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85415781958736344985217527 128123672938104517477826291)
    ·
      refine ⟨192185509407156776216739437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128123672938104517477826291 192185509407156776216739437)
      ·
        refine ⟨72069566027683791081277289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192185509407156776216739437 72069566027683791081277289)
        ·
          refine ⟨54052174520762843310957967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72069566027683791081277289 54052174520762843310957967)
          ·
            refine ⟨81078261781144264966436951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54052174520762843310957967 81078261781144264966436951)
            ·
              refine ⟨121617392671716397449655427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81078261781144264966436951 121617392671716397449655427)
              ·
                refine ⟨182426089007574596174483141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121617392671716397449655427 182426089007574596174483141)
                ·
                  refine ⟨34204891688920236782715589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182426089007574596174483141 34204891688920236782715589)
                  ·
                    refine ⟨6413417191672544396759173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34204891688920236782715589 6413417191672544396759173)
                    ·
                      refine ⟨1202515723438602074392345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6413417191672544396759173 1202515723438602074392345)
                      ·
                        rfl

theorem cell23_2341891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_2341891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341891 prefixEnd_2341891 := by exact prefixLift 2341891
  have htrace : WordTrace (prefixWord ++ tailWord_2341891) baseStart_2341891 baseEnd_2341891 := by
    simpa [prefixWord, tailWord_2341891, baseEnd_2341891] using wordTrace_append hprefix tailTrace_2341891
  have hstable : (prefixWord ++ tailWord_2341891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341891).length < 2 ^ (prefixWord ++ tailWord_2341891).sum := by decide
  have hdescent : baseEnd_2341891 < baseStart_2341891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341895 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_2341895 : Nat := 118140960795 + 2341895 * 2 ^ 59
def prefixEnd_2341895 : Nat := 4983230072969 + 3 ^ 40 * 2341895 * 2
def baseEnd_2341895 : Nat := 1202517777361220058742327

theorem tailTrace_2341895 : CollatzResearch.WordTrace tailWord_2341895 prefixEnd_2341895 1202517777361220058742327 := by
  unfold tailWord_2341895
  simp only [CollatzResearch.WordTrace]
  refine ⟨85415927850721853668363139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56943951900481235778908759 85415927850721853668363139)
  ·
    refine ⟨128123891776082780502544709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85415927850721853668363139 128123891776082780502544709)
    ·
      refine ⟨24023229708015521344227133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128123891776082780502544709 24023229708015521344227133)
      ·
        refine ⟨9008711140505820504085175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24023229708015521344227133 9008711140505820504085175)
        ·
          refine ⟨13513066710758730756127763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9008711140505820504085175 13513066710758730756127763)
          ·
            refine ⟨20269600066138096134191645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13513066710758730756127763 20269600066138096134191645)
            ·
              refine ⟨7601100024801786050321867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20269600066138096134191645 7601100024801786050321867)
              ·
                refine ⟨11401650037202679075482801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7601100024801786050321867 11401650037202679075482801)
                ·
                  refine ⟨8551237527902009306612101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11401650037202679075482801 8551237527902009306612101)
                  ·
                    refine ⟨1603357036481626744989769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8551237527902009306612101 1603357036481626744989769)
                    ·
                      refine ⟨1202517777361220058742327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603357036481626744989769 1202517777361220058742327)
                      ·
                        rfl

theorem cell23_2341895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_2341895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341895 prefixEnd_2341895 := by exact prefixLift 2341895
  have htrace : WordTrace (prefixWord ++ tailWord_2341895) baseStart_2341895 baseEnd_2341895 := by
    simpa [prefixWord, tailWord_2341895, baseEnd_2341895] using wordTrace_append hprefix tailTrace_2341895
  have hstable : (prefixWord ++ tailWord_2341895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341895).length < 2 ^ (prefixWord ++ tailWord_2341895).sum := by decide
  have hdescent : baseEnd_2341895 < baseStart_2341895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341922 : List Nat := [3, 3, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_2341922 : Nat := 118140960795 + 2341922 * 2 ^ 59
def prefixEnd_2341922 : Nat := 4983230072969 + 3 ^ 40 * 2341922 * 2
def baseEnd_2341922 : Nat := 400843880446297151034901

theorem tailTrace_2341922 : CollatzResearch.WordTrace tailWord_2341922 prefixEnd_2341922 400843880446297151034901 := by
  unfold tailWord_2341922
  simp only [CollatzResearch.WordTrace]
  refine ⟨21354228155406009319899005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56944608414416024853064013 21354228155406009319899005)
  ·
    refine ⟨8007835558277253494962127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21354228155406009319899005 8007835558277253494962127)
    ·
      refine ⟨12011753337415880242443191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8007835558277253494962127 12011753337415880242443191)
      ·
        refine ⟨18017630006123820363664787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12011753337415880242443191 18017630006123820363664787)
        ·
          refine ⟨27026445009185730545497181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18017630006123820363664787 27026445009185730545497181)
          ·
            refine ⟨10134916878444648954561443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27026445009185730545497181 10134916878444648954561443)
            ·
              refine ⟨15202375317666973431842165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10134916878444648954561443 15202375317666973431842165)
              ·
                refine ⟨1425222686031278759235203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15202375317666973431842165 1425222686031278759235203)
                ·
                  refine ⟨2137834029046918138852805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425222686031278759235203 2137834029046918138852805)
                  ·
                    refine ⟨400843880446297151034901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2137834029046918138852805 400843880446297151034901)
                    ·
                      rfl

theorem cell23_2341922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_2341922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341922 prefixEnd_2341922 := by exact prefixLift 2341922
  have htrace : WordTrace (prefixWord ++ tailWord_2341922) baseStart_2341922 baseEnd_2341922 := by
    simpa [prefixWord, tailWord_2341922, baseEnd_2341922] using wordTrace_append hprefix tailTrace_2341922
  have hstable : (prefixWord ++ tailWord_2341922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341922).length < 2 ^ (prefixWord ++ tailWord_2341922).sum := by decide
  have hdescent : baseEnd_2341922 < baseStart_2341922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341968 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_2341968 : Nat := 118140960795 + 2341968 * 2 ^ 59
def prefixEnd_2341968 : Nat := 4983230072969 + 3 ^ 40 * 2341968 * 2
def baseEnd_2341968 : Nat := 1202555261448998273129491

theorem tailTrace_2341968 : CollatzResearch.WordTrace tailWord_2341968 prefixEnd_2341968 1202555261448998273129491 := by
  unfold tailWord_2341968
  simp only [CollatzResearch.WordTrace]
  refine ⟨42709295189728693567885279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56945726919638258090513705 42709295189728693567885279)
  ·
    refine ⟨64063942784593040351827919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42709295189728693567885279 64063942784593040351827919)
    ·
      refine ⟨96095914176889560527741879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64063942784593040351827919 96095914176889560527741879)
      ·
        refine ⟨144143871265334340791612819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96095914176889560527741879 144143871265334340791612819)
        ·
          refine ⟨216215806898001511187419229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144143871265334340791612819 216215806898001511187419229)
          ·
            refine ⟨81080927586750566695282211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216215806898001511187419229 81080927586750566695282211)
            ·
              refine ⟨121621391380125850042923317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81080927586750566695282211 121621391380125850042923317)
              ·
                refine ⟨11402005441886798441524061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121621391380125850042923317 11402005441886798441524061)
                ·
                  refine ⟨4275752040707549415571523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11402005441886798441524061 4275752040707549415571523)
                  ·
                    refine ⟨6413628061061324123357285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4275752040707549415571523 6413628061061324123357285)
                    ·
                      refine ⟨1202555261448998273129491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6413628061061324123357285 1202555261448998273129491)
                      ·
                        rfl

theorem cell23_2341968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_2341968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341968 prefixEnd_2341968 := by exact prefixLift 2341968
  have htrace : WordTrace (prefixWord ++ tailWord_2341968) baseStart_2341968 baseEnd_2341968 := by
    simpa [prefixWord, tailWord_2341968, baseEnd_2341968] using wordTrace_append hprefix tailTrace_2341968
  have hstable : (prefixWord ++ tailWord_2341968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341968).length < 2 ^ (prefixWord ++ tailWord_2341968).sum := by decide
  have hdescent : baseEnd_2341968 < baseStart_2341968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341985 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_2341985 : Nat := 118140960795 + 2341985 * 2 ^ 59
def prefixEnd_2341985 : Nat := 4983230072969 + 3 ^ 40 * 2341985 * 2
def baseEnd_2341985 : Nat := 1202563990620124706616913

theorem tailTrace_2341985 : CollatzResearch.WordTrace tailWord_2341985 prefixEnd_2341985 1202563990620124706616913 := by
  unfold tailWord_2341985
  simp only [CollatzResearch.WordTrace]
  refine ⟨85419210420395799039139409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56946140280263866026092939 85419210420395799039139409)
  ·
    refine ⟨64064407815296849279354557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85419210420395799039139409 64064407815296849279354557)
    ·
      refine ⟨24024152930736318479757959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64064407815296849279354557 24024152930736318479757959)
      ·
        refine ⟨36036229396104477719636939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24024152930736318479757959 36036229396104477719636939)
        ·
          refine ⟨54054344094156716579455409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36036229396104477719636939 54054344094156716579455409)
          ·
            refine ⟨40540758070617537434591557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54054344094156716579455409 40540758070617537434591557)
            ·
              refine ⟨7601392138240788268985917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40540758070617537434591557 7601392138240788268985917)
              ·
                refine ⟨2850522051840295600869719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7601392138240788268985917 2850522051840295600869719)
                ·
                  refine ⟨4275783077760443401304579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850522051840295600869719 4275783077760443401304579)
                  ·
                    refine ⟨6413674616640665101956869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4275783077760443401304579 6413674616640665101956869)
                    ·
                      refine ⟨1202563990620124706616913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6413674616640665101956869 1202563990620124706616913)
                      ·
                        rfl

theorem cell23_2341985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_2341985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341985 prefixEnd_2341985 := by exact prefixLift 2341985
  have htrace : WordTrace (prefixWord ++ tailWord_2341985) baseStart_2341985 baseEnd_2341985 := by
    simpa [prefixWord, tailWord_2341985, baseEnd_2341985] using wordTrace_append hprefix tailTrace_2341985
  have hstable : (prefixWord ++ tailWord_2341985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341985).length < 2 ^ (prefixWord ++ tailWord_2341985).sum := by decide
  have hdescent : baseEnd_2341985 < baseStart_2341985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342035 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 3]
def baseStart_2342035 : Nat := 118140960795 + 2342035 * 2 ^ 59
def prefixEnd_2342035 : Nat := 4983230072969 + 3 ^ 40 * 2342035 * 2
def baseEnd_2342035 : Nat := 1202589664652849510991683

theorem tailTrace_2342035 : CollatzResearch.WordTrace tailWord_2342035 prefixEnd_2342035 1202589664652849510991683 := by
  unfold tailWord_2342035
  simp only [CollatzResearch.WordTrace]
  refine ⟨85421034070214657578459559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56947356046809771718973039 85421034070214657578459559)
  ·
    refine ⟨128131551105321986367689339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85421034070214657578459559 128131551105321986367689339)
    ·
      refine ⟨192197326657982979551534009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128131551105321986367689339 192197326657982979551534009)
      ·
        refine ⟨144147994993487234663650507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192197326657982979551534009 144147994993487234663650507)
        ·
          refine ⟨216221992490230851995475761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144147994993487234663650507 216221992490230851995475761)
          ·
            refine ⟨162166494367673138996606821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216221992490230851995475761 162166494367673138996606821)
            ·
              refine ⟨30406217693938713561863779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162166494367673138996606821 30406217693938713561863779)
              ·
                refine ⟨45609326540908070342795669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30406217693938713561863779 45609326540908070342795669)
                ·
                  refine ⟨2137937181605065797318547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45609326540908070342795669 2137937181605065797318547)
                  ·
                    refine ⟨3206905772407598695977821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2137937181605065797318547 3206905772407598695977821)
                    ·
                      refine ⟨1202589664652849510991683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3206905772407598695977821 1202589664652849510991683)
                      ·
                        rfl

theorem cell23_2342035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 3].length) (baseStart_2342035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342035 prefixEnd_2342035 := by exact prefixLift 2342035
  have htrace : WordTrace (prefixWord ++ tailWord_2342035) baseStart_2342035 baseEnd_2342035 := by
    simpa [prefixWord, tailWord_2342035, baseEnd_2342035] using wordTrace_append hprefix tailTrace_2342035
  have hstable : (prefixWord ++ tailWord_2342035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342035).length < 2 ^ (prefixWord ++ tailWord_2342035).sum := by decide
  have hdescent : baseEnd_2342035 < baseStart_2342035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342039 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 1, 2, 3]
def baseStart_2342039 : Nat := 118140960795 + 2342039 * 2 ^ 59
def prefixEnd_2342039 : Nat := 4983230072969 + 3 ^ 40 * 2342039 * 2
def baseEnd_2342039 : Nat := 1202591718575467495341665

theorem tailTrace_2342039 : CollatzResearch.WordTrace tailWord_2342039 prefixEnd_2342039 1202591718575467495341665 := by
  unfold tailWord_2342039
  simp only [CollatzResearch.WordTrace]
  refine ⟨85421179962200166261605171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56947453308133444174403447 85421179962200166261605171)
  ·
    refine ⟨128131769943300249392407757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85421179962200166261605171 128131769943300249392407757)
    ·
      refine ⟨48049413728737593522152909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128131769943300249392407757 48049413728737593522152909)
      ·
        refine ⟨18018530148276597570807341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48049413728737593522152909 18018530148276597570807341)
        ·
          refine ⟨6756948805603724089052753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18018530148276597570807341 6756948805603724089052753)
          ·
            refine ⟨5067711604202793066789565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6756948805603724089052753 5067711604202793066789565)
            ·
              refine ⟨1900391851576047400046087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5067711604202793066789565 1900391851576047400046087)
              ·
                refine ⟨2850587777364071100069131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900391851576047400046087 2850587777364071100069131)
                ·
                  refine ⟨4275881666046106650103697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850587777364071100069131 4275881666046106650103697)
                  ·
                    refine ⟨3206911249534579987577773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4275881666046106650103697 3206911249534579987577773)
                    ·
                      refine ⟨1202591718575467495341665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3206911249534579987577773 1202591718575467495341665)
                      ·
                        rfl

theorem cell23_2342039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_2342039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342039 prefixEnd_2342039 := by exact prefixLift 2342039
  have htrace : WordTrace (prefixWord ++ tailWord_2342039) baseStart_2342039 baseEnd_2342039 := by
    simpa [prefixWord, tailWord_2342039, baseEnd_2342039] using wordTrace_append hprefix tailTrace_2342039
  have hstable : (prefixWord ++ tailWord_2342039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342039).length < 2 ^ (prefixWord ++ tailWord_2342039).sum := by decide
  have hdescent : baseEnd_2342039 < baseStart_2342039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342053 : List Nat := [1, 3, 1, 2, 1, 6, 2, 2, 1, 2, 2]
def baseStart_2342053 : Nat := 118140960795 + 2342053 * 2 ^ 59
def prefixEnd_2342053 : Nat := 4983230072969 + 3 ^ 40 * 2342053 * 2
def baseEnd_2342053 : Nat := 1202598907304630440566601

theorem tailTrace_2342053 : CollatzResearch.WordTrace tailWord_2342053 prefixEnd_2342053 1202598907304630440566601 := by
  unfold tailWord_2342053
  simp only [CollatzResearch.WordTrace]
  refine ⟨85421690584149446652614813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56947793722766297768409875 85421690584149446652614813)
  ·
    refine ⟨32033133969056042494730555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85421690584149446652614813 32033133969056042494730555)
    ·
      refine ⟨48049700953584063742095833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32033133969056042494730555 48049700953584063742095833)
      ·
        refine ⟨36037275715188047806571875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48049700953584063742095833 36037275715188047806571875)
        ·
          refine ⟨54055913572782071709857813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36037275715188047806571875 54055913572782071709857813)
          ·
            refine ⟨2533870948724159611399585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54055913572782071709857813 2533870948724159611399585)
            ·
              refine ⟨1900403211543119708549689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2533870948724159611399585 1900403211543119708549689)
              ·
                refine ⟨1425302408657339781412267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1900403211543119708549689 1425302408657339781412267)
                ·
                  refine ⟨2137953612986009672118401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425302408657339781412267 2137953612986009672118401)
                  ·
                    refine ⟨1603465209739507254088801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2137953612986009672118401 1603465209739507254088801)
                    ·
                      refine ⟨1202598907304630440566601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603465209739507254088801 1202598907304630440566601)
                      ·
                        rfl

theorem cell23_2342053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_2342053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342053 prefixEnd_2342053 := by exact prefixLift 2342053
  have htrace : WordTrace (prefixWord ++ tailWord_2342053) baseStart_2342053 baseEnd_2342053 := by
    simpa [prefixWord, tailWord_2342053, baseEnd_2342053] using wordTrace_append hprefix tailTrace_2342053
  have hstable : (prefixWord ++ tailWord_2342053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342053).length < 2 ^ (prefixWord ++ tailWord_2342053).sum := by decide
  have hdescent : baseEnd_2342053 < baseStart_2342053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342055 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2342055 : Nat := 118140960795 + 2342055 * 2 ^ 59
def prefixEnd_2342055 : Nat := 4983230072969 + 3 ^ 40 * 2342055 * 2
def baseEnd_2342055 : Nat := 400866644755313144247197

theorem tailTrace_2342055 : CollatzResearch.WordTrace tailWord_2342055 prefixEnd_2342055 400866644755313144247197 := by
  unfold tailWord_2342055
  simp only [CollatzResearch.WordTrace]
  refine ⟨85421763530142200994187619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56947842353428133996125079 85421763530142200994187619)
  ·
    refine ⟨128132645295213301491281429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85421763530142200994187619 128132645295213301491281429)
    ·
      refine ⟨6006217748213123507403817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128132645295213301491281429 6006217748213123507403817)
      ·
        refine ⟨4504663311159842630552863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6006217748213123507403817 4504663311159842630552863)
        ·
          refine ⟨6756994966739763945829295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4504663311159842630552863 6756994966739763945829295)
          ·
            refine ⟨10135492450109645918743943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6756994966739763945829295 10135492450109645918743943)
            ·
              refine ⟨15203238675164468878115915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10135492450109645918743943 15203238675164468878115915)
              ·
                refine ⟨22804858012746703317173873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15203238675164468878115915 22804858012746703317173873)
                ·
                  refine ⟨17103643509560027487880405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22804858012746703317173873 17103643509560027487880405)
                  ·
                    refine ⟨400866644755313144247197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17103643509560027487880405 400866644755313144247197)
                    ·
                      rfl

theorem cell23_2342055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2342055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342055 prefixEnd_2342055 := by exact prefixLift 2342055
  have htrace : WordTrace (prefixWord ++ tailWord_2342055) baseStart_2342055 baseEnd_2342055 := by
    simpa [prefixWord, tailWord_2342055, baseEnd_2342055] using wordTrace_append hprefix tailTrace_2342055
  have hstable : (prefixWord ++ tailWord_2342055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342055).length < 2 ^ (prefixWord ++ tailWord_2342055).sum := by decide
  have hdescent : baseEnd_2342055 < baseStart_2342055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342145 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2342145 : Nat := 118140960795 + 2342145 * 2 ^ 59
def prefixEnd_2342145 : Nat := 4983230072969 + 3 ^ 40 * 2342145 * 2
def baseEnd_2342145 : Nat := 400882049174948026872059

theorem tailTrace_2342145 : CollatzResearch.WordTrace tailWord_2342145 prefixEnd_2342145 400882049174948026872059 := by
  unfold tailWord_2342145
  simp only [CollatzResearch.WordTrace]
  refine ⟨85425046099816146364963889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56950030733210764243309259 85425046099816146364963889)
  ·
    refine ⟨64068784574862109773722917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85425046099816146364963889 64068784574862109773722917)
    ·
      refine ⟨12012897107786645582573047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64068784574862109773722917 12012897107786645582573047)
      ·
        refine ⟨18019345661679968373859571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12012897107786645582573047 18019345661679968373859571)
        ·
          refine ⟨27029018492519952560789357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18019345661679968373859571 27029018492519952560789357)
          ·
            refine ⟨10135881934694982210296009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27029018492519952560789357 10135881934694982210296009)
            ·
              refine ⟨7601911451021236657722007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10135881934694982210296009 7601911451021236657722007)
              ·
                refine ⟨11402867176531854986583011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7601911451021236657722007 11402867176531854986583011)
                ·
                  refine ⟨17104300764797782479874517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11402867176531854986583011 17104300764797782479874517)
                  ·
                    refine ⟨400882049174948026872059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17104300764797782479874517 400882049174948026872059)
                    ·
                      rfl

theorem cell23_2342145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2342145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342145 prefixEnd_2342145 := by exact prefixLift 2342145
  have htrace : WordTrace (prefixWord ++ tailWord_2342145) baseStart_2342145 baseEnd_2342145 := by
    simpa [prefixWord, tailWord_2342145, baseEnd_2342145] using wordTrace_append hprefix tailTrace_2342145
  have hstable : (prefixWord ++ tailWord_2342145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342145).length < 2 ^ (prefixWord ++ tailWord_2342145).sum := by decide
  have hdescent : baseEnd_2342145 < baseStart_2342145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342222 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_2342222 : Nat := 118140960795 + 2342222 * 2 ^ 59
def prefixEnd_2342222 : Nat := 4983230072969 + 3 ^ 40 * 2342222 * 2
def baseEnd_2342222 : Nat := 133631742837248919928147

theorem tailTrace_2342222 : CollatzResearch.WordTrace tailWord_2342222 prefixEnd_2342222 133631742837248919928147 := by
  unfold tailWord_2342222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678481815067148564439615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56951903013691459010344613 10678481815067148564439615)
  ·
    refine ⟨16017722722600722846659423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10678481815067148564439615 16017722722600722846659423)
    ·
      refine ⟨24026584083901084269989135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16017722722600722846659423 24026584083901084269989135)
      ·
        refine ⟨36039876125851626404983703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24026584083901084269989135 36039876125851626404983703)
        ·
          refine ⟨54059814188777439607475555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36039876125851626404983703 54059814188777439607475555)
          ·
            refine ⟨81089721283166159411213333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54059814188777439607475555 81089721283166159411213333)
            ·
              refine ⟨3801080685148413722400625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81089721283166159411213333 3801080685148413722400625)
              ·
                refine ⟨2850810513861310291800469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3801080685148413722400625 2850810513861310291800469)
                ·
                  refine ⟨133631742837248919928147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2850810513861310291800469 133631742837248919928147)
                  ·
                    rfl

theorem cell23_2342222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_2342222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342222 prefixEnd_2342222 := by exact prefixLift 2342222
  have htrace : WordTrace (prefixWord ++ tailWord_2342222) baseStart_2342222 baseEnd_2342222 := by
    simpa [prefixWord, tailWord_2342222, baseEnd_2342222] using wordTrace_append hprefix tailTrace_2342222
  have hstable : (prefixWord ++ tailWord_2342222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342222).length < 2 ^ (prefixWord ++ tailWord_2342222).sum := by decide
  have hdescent : baseEnd_2342222 < baseStart_2342222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342225 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_2342225 : Nat := 118140960795 + 2342225 * 2 ^ 59
def prefixEnd_2342225 : Nat := 4983230072969 + 3 ^ 40 * 2342225 * 2
def baseEnd_2342225 : Nat := 1202687225977203767615809

theorem tailTrace_2342225 : CollatzResearch.WordTrace tailWord_2342225 prefixEnd_2342225 1202687225977203767615809 := by
  unfold tailWord_2342225
  simp only [CollatzResearch.WordTrace]
  refine ⟨85427963939526320027876129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56951975959684213351917419 85427963939526320027876129)
  ·
    refine ⟨64070972954644740020907097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85427963939526320027876129 64070972954644740020907097)
    ·
      refine ⟨48053229715983555015680323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64070972954644740020907097 48053229715983555015680323)
      ·
        refine ⟨72079844573975332523520485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48053229715983555015680323 72079844573975332523520485)
        ·
          refine ⟨13514970857620374848160091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72079844573975332523520485 13514970857620374848160091)
          ·
            refine ⟨20272456286430562272240137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13514970857620374848160091 20272456286430562272240137)
            ·
              refine ⟨15204342214822921704180103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20272456286430562272240137 15204342214822921704180103)
              ·
                refine ⟨22806513322234382556270155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15204342214822921704180103 22806513322234382556270155)
                ·
                  refine ⟨34209769983351573834405233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22806513322234382556270155 34209769983351573834405233)
                  ·
                    refine ⟨25657327487513680375803925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34209769983351573834405233 25657327487513680375803925)
                    ·
                      refine ⟨1202687225977203767615809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25657327487513680375803925 1202687225977203767615809)
                      ·
                        rfl

theorem cell23_2342225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_2342225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342225 prefixEnd_2342225 := by exact prefixLift 2342225
  have htrace : WordTrace (prefixWord ++ tailWord_2342225) baseStart_2342225 baseEnd_2342225 := by
    simpa [prefixWord, tailWord_2342225, baseEnd_2342225] using wordTrace_append hprefix tailTrace_2342225
  have hstable : (prefixWord ++ tailWord_2342225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342225).length < 2 ^ (prefixWord ++ tailWord_2342225).sum := by decide
  have hdescent : baseEnd_2342225 < baseStart_2342225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342245 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2342245 : Nat := 118140960795 + 2342245 * 2 ^ 59
def prefixEnd_2342245 : Nat := 4983230072969 + 3 ^ 40 * 2342245 * 2
def baseEnd_2342245 : Nat := 1202697495590293689365717

theorem tailTrace_2342245 : CollatzResearch.WordTrace tailWord_2342245 prefixEnd_2342245 1202697495590293689365717 := by
  unfold tailWord_2342245
  simp only [CollatzResearch.WordTrace]
  refine ⟨85428693399453863443604189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56952462266302575629069459 85428693399453863443604189)
  ·
    refine ⟨32035760024795198791351571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85428693399453863443604189 32035760024795198791351571)
    ·
      refine ⟨48053640037192798187027357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32035760024795198791351571 48053640037192798187027357)
      ·
        refine ⟨18020115013947299320135259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48053640037192798187027357 18020115013947299320135259)
        ·
          refine ⟨27030172520920948980202889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18020115013947299320135259 27030172520920948980202889)
          ·
            refine ⟨20272629390690711735152167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27030172520920948980202889 20272629390690711735152167)
            ·
              refine ⟨30408944086036067602728251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20272629390690711735152167 30408944086036067602728251)
              ·
                refine ⟨45613416129054101404092377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30408944086036067602728251 45613416129054101404092377)
                ·
                  refine ⟨34210062096790576053069283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45613416129054101404092377 34210062096790576053069283)
                  ·
                    refine ⟨51315093145185864079603925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34210062096790576053069283 51315093145185864079603925)
                    ·
                      refine ⟨1202697495590293689365717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51315093145185864079603925 1202697495590293689365717)
                      ·
                        rfl

theorem cell23_2342245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2342245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342245 prefixEnd_2342245 := by exact prefixLift 2342245
  have htrace : WordTrace (prefixWord ++ tailWord_2342245) baseStart_2342245 baseEnd_2342245 := by
    simpa [prefixWord, tailWord_2342245, baseEnd_2342245] using wordTrace_append hprefix tailTrace_2342245
  have hstable : (prefixWord ++ tailWord_2342245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342245).length < 2 ^ (prefixWord ++ tailWord_2342245).sum := by decide
  have hdescent : baseEnd_2342245 < baseStart_2342245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342252 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_2342252 : Nat := 118140960795 + 2342252 * 2 ^ 59
def prefixEnd_2342252 : Nat := 4983230072969 + 3 ^ 40 * 2342252 * 2
def baseEnd_2342252 : Nat := 400900363318291720659395

theorem tailTrace_2342252 : CollatzResearch.WordTrace tailWord_2342252 prefixEnd_2342252 400900363318291720659395 := by
  unfold tailWord_2342252
  simp only [CollatzResearch.WordTrace]
  refine ⟨42714474355214251819554505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56952632473619002426072673 42714474355214251819554505)
  ·
    refine ⟨32035855766410688864665879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42714474355214251819554505 32035855766410688864665879)
    ·
      refine ⟨48053783649616033296998819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32035855766410688864665879 48053783649616033296998819)
      ·
        refine ⟨72080675474424049945498229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48053783649616033296998819 72080675474424049945498229)
        ·
          refine ⟨6757563325727254682390459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72080675474424049945498229 6757563325727254682390459)
          ·
            refine ⟨10136344988590882023585689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6757563325727254682390459 10136344988590882023585689)
            ·
              refine ⟨7602258741443161517689267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10136344988590882023585689 7602258741443161517689267)
              ·
                refine ⟨11403388112164742276533901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7602258741443161517689267 11403388112164742276533901)
                ·
                  refine ⟨4276270542061778353700213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11403388112164742276533901 4276270542061778353700213)
                  ·
                    refine ⟨400900363318291720659395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4276270542061778353700213 400900363318291720659395)
                    ·
                      rfl

theorem cell23_2342252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_2342252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342252 prefixEnd_2342252 := by exact prefixLift 2342252
  have htrace : WordTrace (prefixWord ++ tailWord_2342252) baseStart_2342252 baseEnd_2342252 := by
    simpa [prefixWord, tailWord_2342252, baseEnd_2342252] using wordTrace_append hprefix tailTrace_2342252
  have hstable : (prefixWord ++ tailWord_2342252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342252).length < 2 ^ (prefixWord ++ tailWord_2342252).sum := by decide
  have hdescent : baseEnd_2342252 < baseStart_2342252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342272 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 8, 2]
def baseStart_2342272 : Nat := 118140960795 + 2342272 * 2 ^ 59
def prefixEnd_2342272 : Nat := 4983230072969 + 3 ^ 40 * 2342272 * 2
def baseEnd_2342272 : Nat := 1202711359567965083728093

theorem tailTrace_2342272 : CollatzResearch.WordTrace tailWord_2342272 prefixEnd_2342272 1202711359567965083728093 := by
  unfold tailWord_2342272
  simp only [CollatzResearch.WordTrace]
  refine ⟨42714839085178023527418535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56953118780237364703224713 42714839085178023527418535)
  ·
    refine ⟨64072258627767035291127803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42714839085178023527418535 64072258627767035291127803)
    ·
      refine ⟨96108387941650552936691705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64072258627767035291127803 96108387941650552936691705)
      ·
        refine ⟨72081290956237914702518779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96108387941650552936691705 72081290956237914702518779)
        ·
          refine ⟨108121936434356872053778169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72081290956237914702518779 108121936434356872053778169)
          ·
            refine ⟨81091452325767654040333627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108121936434356872053778169 81091452325767654040333627)
            ·
              refine ⟨121637178488651481060500441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81091452325767654040333627 121637178488651481060500441)
              ·
                refine ⟨91227883866488610795375331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121637178488651481060500441 91227883866488610795375331)
                ·
                  refine ⟨136841825799732916193062997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91227883866488610795375331 136841825799732916193062997)
                  ·
                    refine ⟨1603615146090620111637457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 136841825799732916193062997 1603615146090620111637457)
                    ·
                      refine ⟨1202711359567965083728093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603615146090620111637457 1202711359567965083728093)
                      ·
                        rfl

theorem cell23_2342272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_2342272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342272 prefixEnd_2342272 := by exact prefixLift 2342272
  have htrace : WordTrace (prefixWord ++ tailWord_2342272) baseStart_2342272 baseEnd_2342272 := by
    simpa [prefixWord, tailWord_2342272, baseEnd_2342272] using wordTrace_append hprefix tailTrace_2342272
  have hstable : (prefixWord ++ tailWord_2342272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342272).length < 2 ^ (prefixWord ++ tailWord_2342272).sum := by decide
  have hdescent : baseEnd_2342272 < baseStart_2342272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342289 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 7, 2, 2]
def baseStart_2342289 : Nat := 118140960795 + 2342289 * 2 ^ 59
def prefixEnd_2342289 : Nat := 4983230072969 + 3 ^ 40 * 2342289 * 2
def baseEnd_2342289 : Nat := 1202720088739091517215515

theorem tailTrace_2342289 : CollatzResearch.WordTrace tailWord_2342289 prefixEnd_2342289 1202720088739091517215515 := by
  unfold tailWord_2342289
  simp only [CollatzResearch.WordTrace]
  refine ⟨85430298211294458958205921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56953532140862972638803947 85430298211294458958205921)
  ·
    refine ⟨64072723658470844218654441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85430298211294458958205921 64072723658470844218654441)
    ·
      refine ⟨48054542743853133163990831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64072723658470844218654441 48054542743853133163990831)
      ·
        refine ⟨72081814115779699745986247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48054542743853133163990831 72081814115779699745986247)
        ·
          refine ⟨108122721173669549618979371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72081814115779699745986247 108122721173669549618979371)
          ·
            refine ⟨162184081760504324428469057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108122721173669549618979371 162184081760504324428469057)
            ·
              refine ⟨121638061320378243321351793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162184081760504324428469057 121638061320378243321351793)
              ·
                refine ⟨91228545990283682491013845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121638061320378243321351793 91228545990283682491013845)
                ·
                  refine ⟨2138169046647273808383137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91228545990283682491013845 2138169046647273808383137)
                  ·
                    refine ⟨1603626784985455356287353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138169046647273808383137 1603626784985455356287353)
                    ·
                      refine ⟨1202720088739091517215515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603626784985455356287353 1202720088739091517215515)
                      ·
                        rfl

theorem cell23_2342289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_2342289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342289 prefixEnd_2342289 := by exact prefixLift 2342289
  have htrace : WordTrace (prefixWord ++ tailWord_2342289) baseStart_2342289 baseEnd_2342289 := by
    simpa [prefixWord, tailWord_2342289, baseEnd_2342289] using wordTrace_append hprefix tailTrace_2342289
  have hstable : (prefixWord ++ tailWord_2342289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342289).length < 2 ^ (prefixWord ++ tailWord_2342289).sum := by decide
  have hdescent : baseEnd_2342289 < baseStart_2342289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342295 : List Nat := [1, 1, 3, 3, 1, 1, 1, 12]
def baseStart_2342295 : Nat := 118140960795 + 2342295 * 2 ^ 59
def prefixEnd_2342295 : Nat := 4983230072969 + 3 ^ 40 * 2342295 * 2
def baseEnd_2342295 : Nat := 44545302578630314582981

theorem tailTrace_2342295 : CollatzResearch.WordTrace tailWord_2342295 prefixEnd_2342295 44545302578630314582981 := by
  unfold tailWord_2342295
  simp only [CollatzResearch.WordTrace]
  refine ⟨85430517049272721982924339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56953678032848481321949559 85430517049272721982924339)
  ·
    refine ⟨128145775573909082974386509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85430517049272721982924339 128145775573909082974386509)
    ·
      refine ⟨48054665840215906115394941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128145775573909082974386509 48054665840215906115394941)
      ·
        refine ⟨18020499690080964793273103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48054665840215906115394941 18020499690080964793273103)
        ·
          refine ⟨27030749535121447189909655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18020499690080964793273103 27030749535121447189909655)
          ·
            refine ⟨40546124302682170784864483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27030749535121447189909655 40546124302682170784864483)
            ·
              refine ⟨60819186454023256177296725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40546124302682170784864483 60819186454023256177296725)
              ·
                refine ⟨44545302578630314582981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 60819186454023256177296725 44545302578630314582981)
                ·
                  rfl

theorem cell23_2342295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 12].length) (baseStart_2342295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342295 prefixEnd_2342295 := by exact prefixLift 2342295
  have htrace : WordTrace (prefixWord ++ tailWord_2342295) baseStart_2342295 baseEnd_2342295 := by
    simpa [prefixWord, tailWord_2342295, baseEnd_2342295] using wordTrace_append hprefix tailTrace_2342295
  have hstable : (prefixWord ++ tailWord_2342295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342295).length < 2 ^ (prefixWord ++ tailWord_2342295).sum := by decide
  have hdescent : baseEnd_2342295 < baseStart_2342295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342306 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2342306 : Nat := 118140960795 + 2342306 * 2 ^ 59
def prefixEnd_2342306 : Nat := 4983230072969 + 3 ^ 40 * 2342306 * 2
def baseEnd_2342306 : Nat := 1202728817910217950702937

theorem tailTrace_2342306 : CollatzResearch.WordTrace tailWord_2342306 prefixEnd_2342306 1202728817910217950702937 := by
  unfold tailWord_2342306
  simp only [CollatzResearch.WordTrace]
  refine ⟨21357729563058217715393693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56953945501488580574383181 21357729563058217715393693)
  ·
    refine ⟨8009148586146831643272635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21357729563058217715393693 8009148586146831643272635)
    ·
      refine ⟨12013722879220247464908953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8009148586146831643272635 12013722879220247464908953)
      ·
        refine ⟨9010292159415185598681715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12013722879220247464908953 9010292159415185598681715)
        ·
          refine ⟨13515438239122778398022573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9010292159415185598681715 13515438239122778398022573)
          ·
            refine ⟨5068289339671041899258465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13515438239122778398022573 5068289339671041899258465)
            ·
              refine ⟨3801217004753281424443849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5068289339671041899258465 3801217004753281424443849)
              ·
                refine ⟨2850912753564961068332887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3801217004753281424443849 2850912753564961068332887)
                ·
                  refine ⟨4276369130347441602499331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850912753564961068332887 4276369130347441602499331)
                  ·
                    refine ⟨6414553695521162403748997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4276369130347441602499331 6414553695521162403748997)
                    ·
                      refine ⟨1202728817910217950702937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6414553695521162403748997 1202728817910217950702937)
                      ·
                        rfl

theorem cell23_2342306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2342306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342306 prefixEnd_2342306 := by exact prefixLift 2342306
  have htrace : WordTrace (prefixWord ++ tailWord_2342306) baseStart_2342306 baseEnd_2342306 := by
    simpa [prefixWord, tailWord_2342306, baseEnd_2342306] using wordTrace_append hprefix tailTrace_2342306
  have hstable : (prefixWord ++ tailWord_2342306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342306).length < 2 ^ (prefixWord ++ tailWord_2342306).sum := by decide
  have hdescent : baseEnd_2342306 < baseStart_2342306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342329 : List Nat := [1, 2, 1, 4, 5, 1, 9]
def baseStart_2342329 : Nat := 118140960795 + 2342329 * 2 ^ 59
def prefixEnd_2342329 : Nat := 4983230072969 + 3 ^ 40 * 2342329 * 2
def baseEnd_2342329 : Nat := 14848649727966313095251

theorem tailTrace_2342329 : CollatzResearch.WordTrace tailWord_2342329 prefixEnd_2342329 14848649727966313095251 := by
  unfold tailWord_2342329
  simp only [CollatzResearch.WordTrace]
  refine ⟨85431757131149545789662041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56954504754099697193108027 85431757131149545789662041)
  ·
    refine ⟨64073817848362159342246531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85431757131149545789662041 64073817848362159342246531)
    ·
      refine ⟨96110726772543239013369797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64073817848362159342246531 96110726772543239013369797)
      ·
        refine ⟨18020761269851857315006837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96110726772543239013369797 18020761269851857315006837)
        ·
          refine ⟨1689446369048611623281891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18020761269851857315006837 1689446369048611623281891)
          ·
            refine ⟨2534169553572917434922837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689446369048611623281891 2534169553572917434922837)
            ·
              refine ⟨14848649727966313095251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2534169553572917434922837 14848649727966313095251)
              ·
                rfl

theorem cell23_2342329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 9].length) (baseStart_2342329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342329 prefixEnd_2342329 := by exact prefixLift 2342329
  have htrace : WordTrace (prefixWord ++ tailWord_2342329) baseStart_2342329 baseEnd_2342329 := by
    simpa [prefixWord, tailWord_2342329, baseEnd_2342329] using wordTrace_append hprefix tailTrace_2342329
  have hstable : (prefixWord ++ tailWord_2342329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342329).length < 2 ^ (prefixWord ++ tailWord_2342329).sum := by decide
  have hdescent : baseEnd_2342329 < baseStart_2342329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342339 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 3]
def baseStart_2342339 : Nat := 118140960795 + 2342339 * 2 ^ 59
def prefixEnd_2342339 : Nat := 4983230072969 + 3 ^ 40 * 2342339 * 2
def baseEnd_2342339 : Nat := 1202745762771816321590285

theorem tailTrace_2342339 : CollatzResearch.WordTrace tailWord_2342339 prefixEnd_2342339 1202745762771816321590285 := by
  unfold tailWord_2342339
  simp only [CollatzResearch.WordTrace]
  refine ⟨85432121861113317497526071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56954747907408878331684047 85432121861113317497526071)
  ·
    refine ⟨128148182791669976246289107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85432121861113317497526071 128148182791669976246289107)
    ·
      refine ⟨192222274187504964369433661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128148182791669976246289107 192222274187504964369433661)
      ·
        refine ⟨72083352820314361638537623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192222274187504964369433661 72083352820314361638537623)
        ·
          refine ⟨108125029230471542457806435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72083352820314361638537623 108125029230471542457806435)
          ·
            refine ⟨162187543845707313686709653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108125029230471542457806435 162187543845707313686709653)
            ·
              refine ⟨7602541117767530329064515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 162187543845707313686709653 7602541117767530329064515)
              ·
                refine ⟨11403811676651295493596773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7602541117767530329064515 11403811676651295493596773)
                ·
                  refine ⟨2138214689372117905049395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11403811676651295493596773 2138214689372117905049395)
                  ·
                    refine ⟨3207322034058176857574093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2138214689372117905049395 3207322034058176857574093)
                    ·
                      refine ⟨1202745762771816321590285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3207322034058176857574093 1202745762771816321590285)
                      ·
                        rfl

theorem cell23_2342339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_2342339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342339 prefixEnd_2342339 := by exact prefixLift 2342339
  have htrace : WordTrace (prefixWord ++ tailWord_2342339) baseStart_2342339 baseEnd_2342339 := by
    simpa [prefixWord, tailWord_2342339, baseEnd_2342339] using wordTrace_append hprefix tailTrace_2342339
  have hstable : (prefixWord ++ tailWord_2342339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342339).length < 2 ^ (prefixWord ++ tailWord_2342339).sum := by decide
  have hdescent : baseEnd_2342339 < baseStart_2342339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342340 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_2342340 : Nat := 118140960795 + 2342340 * 2 ^ 59
def prefixEnd_2342340 : Nat := 4983230072969 + 3 ^ 40 * 2342340 * 2
def baseEnd_2342340 : Nat := 1202746276252470817677781

theorem tailTrace_2342340 : CollatzResearch.WordTrace tailWord_2342340 prefixEnd_2342340 1202746276252470817677781 := by
  unfold tailWord_2342340
  simp only [CollatzResearch.WordTrace]
  refine ⟨42716079167054847334156237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56954772222739796445541649 42716079167054847334156237)
  ·
    refine ⟨16018529687645567750308589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42716079167054847334156237 16018529687645567750308589)
    ·
      refine ⟨6006948632867087906365721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16018529687645567750308589 6006948632867087906365721)
      ·
        refine ⟨4505211474650315929774291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6006948632867087906365721 4505211474650315929774291)
        ·
          refine ⟨6757817211975473894661437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4505211474650315929774291 6757817211975473894661437)
          ·
            refine ⟨2534181454490802710498039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6757817211975473894661437 2534181454490802710498039)
            ·
              refine ⟨3801272181736204065747059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2534181454490802710498039 3801272181736204065747059)
              ·
                refine ⟨5701908272604306098620589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801272181736204065747059 5701908272604306098620589)
                ·
                  refine ⟨2138215602226614786982721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5701908272604306098620589 2138215602226614786982721)
                  ·
                    refine ⟨1603661701669961090237041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138215602226614786982721 1603661701669961090237041)
                    ·
                      refine ⟨1202746276252470817677781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603661701669961090237041 1202746276252470817677781)
                      ·
                        rfl

theorem cell23_2342340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_2342340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342340 prefixEnd_2342340 := by exact prefixLift 2342340
  have htrace : WordTrace (prefixWord ++ tailWord_2342340) baseStart_2342340 baseEnd_2342340 := by
    simpa [prefixWord, tailWord_2342340, baseEnd_2342340] using wordTrace_append hprefix tailTrace_2342340
  have hstable : (prefixWord ++ tailWord_2342340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342340).length < 2 ^ (prefixWord ++ tailWord_2342340).sum := by decide
  have hdescent : baseEnd_2342340 < baseStart_2342340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342396 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_2342396 : Nat := 118140960795 + 2342396 * 2 ^ 59
def prefixEnd_2342396 : Nat := 4983230072969 + 3 ^ 40 * 2342396 * 2
def baseEnd_2342396 : Nat := 1202775031169122598577523

theorem tailTrace_2342396 : CollatzResearch.WordTrace tailWord_2342396 prefixEnd_2342396 1202775031169122598577523 := by
  unfold tailWord_2342396
  simp only [CollatzResearch.WordTrace]
  refine ⟨42717100410953408116175521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56956133881271210821567361 42717100410953408116175521)
  ·
    refine ⟨32037825308215056087131641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42717100410953408116175521 32037825308215056087131641)
    ·
      refine ⟨24028368981161292065348731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32037825308215056087131641 24028368981161292065348731)
      ·
        refine ⟨36042553471741938098023097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24028368981161292065348731 36042553471741938098023097)
        ·
          refine ⟨27031915103806453573517323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36042553471741938098023097 27031915103806453573517323)
          ·
            refine ⟨40547872655709680360275985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27031915103806453573517323 40547872655709680360275985)
            ·
              refine ⟨30410904491782260270206989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40547872655709680360275985 30410904491782260270206989)
              ·
                refine ⟨11404089184418347601327621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30410904491782260270206989 11404089184418347601327621)
                ·
                  refine ⟨2138266722078440175248929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11404089184418347601327621 2138266722078440175248929)
                  ·
                    refine ⟨1603700041558830131436697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138266722078440175248929 1603700041558830131436697)
                    ·
                      refine ⟨1202775031169122598577523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603700041558830131436697 1202775031169122598577523)
                      ·
                        rfl

theorem cell23_2342396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_2342396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342396 prefixEnd_2342396 := by exact prefixLift 2342396
  have htrace : WordTrace (prefixWord ++ tailWord_2342396) baseStart_2342396 baseEnd_2342396 := by
    simpa [prefixWord, tailWord_2342396, baseEnd_2342396] using wordTrace_append hprefix tailTrace_2342396
  have hstable : (prefixWord ++ tailWord_2342396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342396).length < 2 ^ (prefixWord ++ tailWord_2342396).sum := by decide
  have hdescent : baseEnd_2342396 < baseStart_2342396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342429 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2342429 : Nat := 118140960795 + 2342429 * 2 ^ 59
def prefixEnd_2342429 : Nat := 4983230072969 + 3 ^ 40 * 2342429 * 2
def baseEnd_2342429 : Nat := 1202791976030720969464871

theorem tailTrace_2342429 : CollatzResearch.WordTrace tailWord_2342429 prefixEnd_2342429 1202791976030720969464871 := by
  unfold tailWord_2342429
  simp only [CollatzResearch.WordTrace]
  refine ⟨85435404430787262868302341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56956936287191508578868227 85435404430787262868302341)
  ·
    refine ⟨16019138330772611787806689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85435404430787262868302341 16019138330772611787806689)
    ·
      refine ⟨12014353748079458840855017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16019138330772611787806689 12014353748079458840855017)
      ·
        refine ⟨9010765311059594130641263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12014353748079458840855017 9010765311059594130641263)
        ·
          refine ⟨13516147966589391195961895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9010765311059594130641263 13516147966589391195961895)
          ·
            refine ⟨20274221949884086793942843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13516147966589391195961895 20274221949884086793942843)
            ·
              refine ⟨30411332924826130190914265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20274221949884086793942843 30411332924826130190914265)
              ·
                refine ⟨22808499693619597643185699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30411332924826130190914265 22808499693619597643185699)
                ·
                  refine ⟨34212749540429396464778549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22808499693619597643185699 34212749540429396464778549)
                  ·
                    refine ⟨3207445269415255918572989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34212749540429396464778549 3207445269415255918572989)
                    ·
                      refine ⟨1202791976030720969464871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3207445269415255918572989 1202791976030720969464871)
                      ·
                        rfl

theorem cell23_2342429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2342429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342429 prefixEnd_2342429 := by exact prefixLift 2342429
  have htrace : WordTrace (prefixWord ++ tailWord_2342429) baseStart_2342429 baseEnd_2342429 := by
    simpa [prefixWord, tailWord_2342429, baseEnd_2342429] using wordTrace_append hprefix tailTrace_2342429
  have hstable : (prefixWord ++ tailWord_2342429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342429).length < 2 ^ (prefixWord ++ tailWord_2342429).sum := by decide
  have hdescent : baseEnd_2342429 < baseStart_2342429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342446 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2342446 : Nat := 118140960795 + 2342446 * 2 ^ 59
def prefixEnd_2342446 : Nat := 4983230072969 + 3 ^ 40 * 2342446 * 2
def baseEnd_2342446 : Nat := 1202800705201847402952293

theorem tailTrace_2342446 : CollatzResearch.WordTrace tailWord_2342446 prefixEnd_2342446 1202800705201847402952293 := by
  unfold tailWord_2342446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10679503058965709346458899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56957349647817116514447461 10679503058965709346458899)
  ·
    refine ⟨16019254588448564019688349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10679503058965709346458899 16019254588448564019688349)
    ·
      refine ⟨6007220470668211507383131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16019254588448564019688349 6007220470668211507383131)
      ·
        refine ⟨9010830706002317261074697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6007220470668211507383131 9010830706002317261074697)
        ·
          refine ⟨6758123029501737945806023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9010830706002317261074697 6758123029501737945806023)
          ·
            refine ⟨10137184544252606918709035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6758123029501737945806023 10137184544252606918709035)
            ·
              refine ⟨15205776816378910378063553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10137184544252606918709035 15205776816378910378063553)
              ·
                refine ⟨11404332612284182783547665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15205776816378910378063553 11404332612284182783547665)
                ·
                  refine ⟨8553249459213137087660749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11404332612284182783547665 8553249459213137087660749)
                  ·
                    refine ⟨3207468547204926407872781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8553249459213137087660749 3207468547204926407872781)
                    ·
                      refine ⟨1202800705201847402952293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3207468547204926407872781 1202800705201847402952293)
                      ·
                        rfl

theorem cell23_2342446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2342446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342446 prefixEnd_2342446 := by exact prefixLift 2342446
  have htrace : WordTrace (prefixWord ++ tailWord_2342446) baseStart_2342446 baseEnd_2342446 := by
    simpa [prefixWord, tailWord_2342446, baseEnd_2342446] using wordTrace_append hprefix tailTrace_2342446
  have hstable : (prefixWord ++ tailWord_2342446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342446).length < 2 ^ (prefixWord ++ tailWord_2342446).sum := by decide
  have hdescent : baseEnd_2342446 < baseStart_2342446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342489 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 3]
def baseStart_2342489 : Nat := 118140960795 + 2342489 * 2 ^ 59
def prefixEnd_2342489 : Nat := 4983230072969 + 3 ^ 40 * 2342489 * 2
def baseEnd_2342489 : Nat := 1202822784869990734714595

theorem tailTrace_2342489 : CollatzResearch.WordTrace tailWord_2342489 prefixEnd_2342489 1202822784869990734714595 := by
  unfold tailWord_2342489
  simp only [CollatzResearch.WordTrace]
  refine ⟨85437592810569893115486521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56958395207046595410324347 85437592810569893115486521)
  ·
    refine ⟨64078194607927419836614891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85437592810569893115486521 64078194607927419836614891)
    ·
      refine ⟨96117291911891129754922337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64078194607927419836614891 96117291911891129754922337)
      ·
        refine ⟨72087968933918347316191753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96117291911891129754922337 72087968933918347316191753)
        ·
          refine ⟨54065976700438760487143815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72087968933918347316191753 54065976700438760487143815)
          ·
            refine ⟨81098965050658140730715723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54065976700438760487143815 81098965050658140730715723)
            ·
              refine ⟨121648447575987211096073585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81098965050658140730715723 121648447575987211096073585)
              ·
                refine ⟨91236335681990408322055189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121648447575987211096073585 91236335681990408322055189)
                ·
                  refine ⟨4276703235093300390096337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91236335681990408322055189 4276703235093300390096337)
                  ·
                    refine ⟨3207527426319975292572253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4276703235093300390096337 3207527426319975292572253)
                    ·
                      refine ⟨1202822784869990734714595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3207527426319975292572253 1202822784869990734714595)
                      ·
                        rfl

theorem cell23_2342489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_2342489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342489 prefixEnd_2342489 := by exact prefixLift 2342489
  have htrace : WordTrace (prefixWord ++ tailWord_2342489) baseStart_2342489 baseEnd_2342489 := by
    simpa [prefixWord, tailWord_2342489, baseEnd_2342489] using wordTrace_append hprefix tailTrace_2342489
  have hstable : (prefixWord ++ tailWord_2342489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342489).length < 2 ^ (prefixWord ++ tailWord_2342489).sum := by decide
  have hdescent : baseEnd_2342489 < baseStart_2342489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342506 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2342506 : Nat := 118140960795 + 2342506 * 2 ^ 59
def prefixEnd_2342506 : Nat := 4983230072969 + 3 ^ 40 * 2342506 * 2
def baseEnd_2342506 : Nat := 1202831514041117168202017

theorem tailTrace_2342506 : CollatzResearch.WordTrace tailWord_2342506 prefixEnd_2342506 1202831514041117168202017 := by
  unfold tailWord_2342506
  simp only [CollatzResearch.WordTrace]
  refine ⟨21359553212877076254713843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56958808567672203345903581 21359553212877076254713843)
  ·
    refine ⟨32039329819315614382070765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21359553212877076254713843 32039329819315614382070765)
    ·
      refine ⟨12014748682243355393276537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32039329819315614382070765 12014748682243355393276537)
      ·
        refine ⟨9011061511682516544957403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12014748682243355393276537 9011061511682516544957403)
        ·
          refine ⟨13516592267523774817436105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9011061511682516544957403 13516592267523774817436105)
          ·
            refine ⟨10137444200642831113077079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13516592267523774817436105 10137444200642831113077079)
            ·
              refine ⟨15206166300964246669615619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10137444200642831113077079 15206166300964246669615619)
              ·
                refine ⟨22809249451446370004423429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15206166300964246669615619 22809249451446370004423429)
                ·
                  refine ⟨4276734272146194375829393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22809249451446370004423429 4276734272146194375829393)
                  ·
                    refine ⟨3207550704109645781872045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4276734272146194375829393 3207550704109645781872045)
                    ·
                      refine ⟨1202831514041117168202017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3207550704109645781872045 1202831514041117168202017)
                      ·
                        rfl

theorem cell23_2342506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2342506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342506 prefixEnd_2342506 := by exact prefixLift 2342506
  have htrace : WordTrace (prefixWord ++ tailWord_2342506) baseStart_2342506 baseEnd_2342506 := by
    simpa [prefixWord, tailWord_2342506, baseEnd_2342506] using wordTrace_append hprefix tailTrace_2342506
  have hstable : (prefixWord ++ tailWord_2342506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342506).length < 2 ^ (prefixWord ++ tailWord_2342506).sum := by decide
  have hdescent : baseEnd_2342506 < baseStart_2342506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342539 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 3, 5]
def baseStart_2342539 : Nat := 118140960795 + 2342539 * 2 ^ 59
def prefixEnd_2342539 : Nat := 4983230072969 + 3 ^ 40 * 2342539 * 2
def baseEnd_2342539 : Nat := 400949486300905179696455

theorem tailTrace_2342539 : CollatzResearch.WordTrace tailWord_2342539 prefixEnd_2342539 400949486300905179696455 := by
  unfold tailWord_2342539
  simp only [CollatzResearch.WordTrace]
  refine ⟨85439416460388751654806671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56959610973592501103204447 85439416460388751654806671)
  ·
    refine ⟨128159124690583127482210007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85439416460388751654806671 128159124690583127482210007)
    ·
      refine ⟨192238687035874691223315011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128159124690583127482210007 192238687035874691223315011)
      ·
        refine ⟨288358030553812036834972517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192238687035874691223315011 288358030553812036834972517)
        ·
          refine ⟨54067130728839756906557347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288358030553812036834972517 54067130728839756906557347)
          ·
            refine ⟨81100696093259635359836021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54067130728839756906557347 81100696093259635359836021)
            ·
              refine ⟨7603190258743090814984627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81100696093259635359836021 7603190258743090814984627)
              ·
                refine ⟨11404785388114636222476941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7603190258743090814984627 11404785388114636222476941)
                ·
                  refine ⟨4276794520542988583428853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11404785388114636222476941 4276794520542988583428853)
                  ·
                    refine ⟨400949486300905179696455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4276794520542988583428853 400949486300905179696455)
                    ·
                      rfl

theorem cell23_2342539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 5].length) (baseStart_2342539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342539 prefixEnd_2342539 := by exact prefixLift 2342539
  have htrace : WordTrace (prefixWord ++ tailWord_2342539) baseStart_2342539 baseEnd_2342539 := by
    simpa [prefixWord, tailWord_2342539, baseEnd_2342539] using wordTrace_append hprefix tailTrace_2342539
  have hstable : (prefixWord ++ tailWord_2342539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342539).length < 2 ^ (prefixWord ++ tailWord_2342539).sum := by decide
  have hdescent : baseEnd_2342539 < baseStart_2342539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342579 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 5]
def baseStart_2342579 : Nat := 118140960795 + 2342579 * 2 ^ 59
def prefixEnd_2342579 : Nat := 4983230072969 + 3 ^ 40 * 2342579 * 2
def baseEnd_2342579 : Nat := 1202868998128895382589181

theorem tailTrace_2342579 : CollatzResearch.WordTrace tailWord_2342579 prefixEnd_2342579 1202868998128895382589181 := by
  unfold tailWord_2342579
  simp only [CollatzResearch.WordTrace]
  refine ⟨85440875380243838486262791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56960583586829225657508527 85440875380243838486262791)
  ·
    refine ⟨128161313070365757729394187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85440875380243838486262791 128161313070365757729394187)
    ·
      refine ⟨192241969605548636594091281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128161313070365757729394187 192241969605548636594091281)
      ·
        refine ⟨144181477204161477445568461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192241969605548636594091281 144181477204161477445568461)
        ·
          refine ⟨54068053951560554042088173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144181477204161477445568461 54068053951560554042088173)
          ·
            refine ⟨20275520231835207765783065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54068053951560554042088173 20275520231835207765783065)
            ·
              refine ⟨15206640173876405824337299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20275520231835207765783065 15206640173876405824337299)
              ·
                refine ⟨22809960260814608736505949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15206640173876405824337299 22809960260814608736505949)
                ·
                  refine ⟨8553735097805478276189731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22809960260814608736505949 8553735097805478276189731)
                  ·
                    refine ⟨12830602646708217414284597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8553735097805478276189731 12830602646708217414284597)
                    ·
                      refine ⟨1202868998128895382589181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12830602646708217414284597 1202868998128895382589181)
                      ·
                        rfl

theorem cell23_2342579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_2342579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342579 prefixEnd_2342579 := by exact prefixLift 2342579
  have htrace : WordTrace (prefixWord ++ tailWord_2342579) baseStart_2342579 baseEnd_2342579 := by
    simpa [prefixWord, tailWord_2342579, baseEnd_2342579] using wordTrace_append hprefix tailTrace_2342579
  have hstable : (prefixWord ++ tailWord_2342579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342579).length < 2 ^ (prefixWord ++ tailWord_2342579).sum := by decide
  have hdescent : baseEnd_2342579 < baseStart_2342579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342586 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_2342586 : Nat := 118140960795 + 2342586 * 2 ^ 59
def prefixEnd_2342586 : Nat := 4983230072969 + 3 ^ 40 * 2342586 * 2
def baseEnd_2342586 : Nat := 400957530831158951733883

theorem tailTrace_2342586 : CollatzResearch.WordTrace tailWord_2342586 prefixEnd_2342586 400957530831158951733883 := by
  unfold tailWord_2342586
  simp only [CollatzResearch.WordTrace]
  refine ⟨21360282672804619670441903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56960753794145652454511741 21360282672804619670441903)
  ·
    refine ⟨32040424009206929505662855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21360282672804619670441903 32040424009206929505662855)
    ·
      refine ⟨48060636013810394258494283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32040424009206929505662855 48060636013810394258494283)
      ·
        refine ⟨72090954020715591387741425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48060636013810394258494283 72090954020715591387741425)
        ·
          refine ⟨54068215515536693540806069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72090954020715591387741425 54068215515536693540806069)
          ·
            refine ⟨5068895204581565019450569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54068215515536693540806069 5068895204581565019450569)
            ·
              refine ⟨3801671403436173764587927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5068895204581565019450569 3801671403436173764587927)
              ·
                refine ⟨5702507105154260646881891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801671403436173764587927 5702507105154260646881891)
                ·
                  refine ⟨8553760657731390970322837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5702507105154260646881891 8553760657731390970322837)
                  ·
                    refine ⟨400957530831158951733883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8553760657731390970322837 400957530831158951733883)
                    ·
                      rfl

theorem cell23_2342586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_2342586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342586 prefixEnd_2342586 := by exact prefixLift 2342586
  have htrace : WordTrace (prefixWord ++ tailWord_2342586) baseStart_2342586 baseEnd_2342586 := by
    simpa [prefixWord, tailWord_2342586, baseEnd_2342586] using wordTrace_append hprefix tailTrace_2342586
  have hstable : (prefixWord ++ tailWord_2342586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342586).length < 2 ^ (prefixWord ++ tailWord_2342586).sum := by decide
  have hdescent : baseEnd_2342586 < baseStart_2342586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342606 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2342606 : Nat := 118140960795 + 2342606 * 2 ^ 59
def prefixEnd_2342606 : Nat := 4983230072969 + 3 ^ 40 * 2342606 * 2
def baseEnd_2342606 : Nat := 1202882862106566776951557

theorem tailTrace_2342606 : CollatzResearch.WordTrace tailWord_2342606 prefixEnd_2342606 1202882862106566776951557 := by
  unfold tailWord_2342606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10680232518893252762186959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56961240100764014731663781 10680232518893252762186959)
  ·
    refine ⟨16020348778339879143280439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10680232518893252762186959 16020348778339879143280439)
    ·
      refine ⟨24030523167509818714920659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16020348778339879143280439 24030523167509818714920659)
      ·
        refine ⟨36045784751264728072380989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24030523167509818714920659 36045784751264728072380989)
        ·
          refine ⟨13517169281724273027142871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36045784751264728072380989 13517169281724273027142871)
          ·
            refine ⟨20275753922586409540714307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13517169281724273027142871 20275753922586409540714307)
            ·
              refine ⟨30413630883879614311071461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20275753922586409540714307 30413630883879614311071461)
              ·
                refine ⟨5702555790727427683325899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30413630883879614311071461 5702555790727427683325899)
                ·
                  refine ⟨8553833686091141524988849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5702555790727427683325899 8553833686091141524988849)
                  ·
                    refine ⟨6415375264568356143741637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8553833686091141524988849 6415375264568356143741637)
                    ·
                      refine ⟨1202882862106566776951557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6415375264568356143741637 1202882862106566776951557)
                      ·
                        rfl

theorem cell23_2342606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2342606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342606 prefixEnd_2342606 := by exact prefixLift 2342606
  have htrace : WordTrace (prefixWord ++ tailWord_2342606) baseStart_2342606 baseEnd_2342606 := by
    simpa [prefixWord, tailWord_2342606, baseEnd_2342606] using wordTrace_append hprefix tailTrace_2342606
  have hstable : (prefixWord ++ tailWord_2342606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342606).length < 2 ^ (prefixWord ++ tailWord_2342606).sum := by decide
  have hdescent : baseEnd_2342606 < baseStart_2342606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342610 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_2342610 : Nat := 118140960795 + 2342610 * 2 ^ 59
def prefixEnd_2342610 : Nat := 4983230072969 + 3 ^ 40 * 2342610 * 2
def baseEnd_2342610 : Nat := 1202884916029184761301539

theorem tailTrace_2342610 : CollatzResearch.WordTrace tailWord_2342610 prefixEnd_2342610 1202884916029184761301539 := by
  unfold tailWord_2342610
  simp only [CollatzResearch.WordTrace]
  refine ⟨21360501510782882695160321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56961337362087687187094189 21360501510782882695160321)
  ·
    refine ⟨16020376133087162021370241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21360501510782882695160321 16020376133087162021370241)
    ·
      refine ⟨12015282099815371516027681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16020376133087162021370241 12015282099815371516027681)
      ·
        refine ⟨9011461574861528637020761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12015282099815371516027681 9011461574861528637020761)
        ·
          refine ⟨6758596181146146477765571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9011461574861528637020761 6758596181146146477765571)
          ·
            refine ⟨10137894271719219716648357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6758596181146146477765571 10137894271719219716648357)
            ·
              refine ⟨1900855175947353696871567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10137894271719219716648357 1900855175947353696871567)
              ·
                refine ⟨2851282763921030545307351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900855175947353696871567 2851282763921030545307351)
                ·
                  refine ⟨4276924145881545817961027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851282763921030545307351 4276924145881545817961027)
                  ·
                    refine ⟨6415386218822318726941541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4276924145881545817961027 6415386218822318726941541)
                    ·
                      refine ⟨1202884916029184761301539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6415386218822318726941541 1202884916029184761301539)
                      ·
                        rfl

theorem cell23_2342610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_2342610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342610 prefixEnd_2342610 := by exact prefixLift 2342610
  have htrace : WordTrace (prefixWord ++ tailWord_2342610) baseStart_2342610 baseEnd_2342610 := by
    simpa [prefixWord, tailWord_2342610, baseEnd_2342610] using wordTrace_append hprefix tailTrace_2342610
  have hstable : (prefixWord ++ tailWord_2342610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342610).length < 2 ^ (prefixWord ++ tailWord_2342610).sum := by decide
  have hdescent : baseEnd_2342610 < baseStart_2342610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342620 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2342620 : Nat := 118140960795 + 2342620 * 2 ^ 59
def prefixEnd_2342620 : Nat := 4983230072969 + 3 ^ 40 * 2342620 * 2
def baseEnd_2342620 : Nat := 400963350278576574058831

theorem tailTrace_2342620 : CollatzResearch.WordTrace tailWord_2342620 prefixEnd_2342620 400963350278576574058831 := by
  unfold tailWord_2342620
  simp only [CollatzResearch.WordTrace]
  refine ⟨42721185386547651244252657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56961580515396868325670209 42721185386547651244252657)
  ·
    refine ⟨32040889039910738433189493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42721185386547651244252657 32040889039910738433189493)
    ·
      refine ⟨3003833347491631728111515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32040889039910738433189493 3003833347491631728111515)
      ·
        refine ⟨4505750021237447592167273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003833347491631728111515 4505750021237447592167273)
        ·
          refine ⟨3379312515928085694125455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4505750021237447592167273 3379312515928085694125455)
          ·
            refine ⟨5068968773892128541188183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379312515928085694125455 5068968773892128541188183)
            ·
              refine ⟨7603453160838192811782275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5068968773892128541188183 7603453160838192811782275)
              ·
                refine ⟨11405179741257289217673413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7603453160838192811782275 11405179741257289217673413)
                ·
                  refine ⟨2138471201485741728313765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11405179741257289217673413 2138471201485741728313765)
                  ·
                    refine ⟨400963350278576574058831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2138471201485741728313765 400963350278576574058831)
                    ·
                      rfl

theorem cell23_2342620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2342620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342620 prefixEnd_2342620 := by exact prefixLift 2342620
  have htrace : WordTrace (prefixWord ++ tailWord_2342620) baseStart_2342620 baseEnd_2342620 := by
    simpa [prefixWord, tailWord_2342620, baseEnd_2342620] using wordTrace_append hprefix tailTrace_2342620
  have hstable : (prefixWord ++ tailWord_2342620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342620).length < 2 ^ (prefixWord ++ tailWord_2342620).sum := by decide
  have hdescent : baseEnd_2342620 < baseStart_2342620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342627 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 3, 2, 2]
def baseStart_2342627 : Nat := 118140960795 + 2342627 * 2 ^ 59
def prefixEnd_2342627 : Nat := 4983230072969 + 3 ^ 40 * 2342627 * 2
def baseEnd_2342627 : Nat := 1202893645200311194788961

theorem tailTrace_2342627 : CollatzResearch.WordTrace tailWord_2342627 prefixEnd_2342627 1202893645200311194788961 := by
  unfold tailWord_2342627
  simp only [CollatzResearch.WordTrace]
  refine ⟨85442626084069942684010135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56961750722713295122673423 85442626084069942684010135)
  ·
    refine ⟨128163939126104914026015203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85442626084069942684010135 128163939126104914026015203)
    ·
      refine ⟨192245908689157371039022805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128163939126104914026015203 192245908689157371039022805)
      ·
        refine ⟨4505763484902125883727097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 192245908689157371039022805 4505763484902125883727097)
        ·
          refine ⟨3379322613676594412795323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4505763484902125883727097 3379322613676594412795323)
          ·
            refine ⟨5068983920514891619192985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379322613676594412795323 5068983920514891619192985)
            ·
              refine ⟨3801737940386168714394739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5068983920514891619192985 3801737940386168714394739)
              ·
                refine ⟨5702606910579253071592109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801737940386168714394739 5702606910579253071592109)
                ·
                  refine ⟨2138477591467219901847041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5702606910579253071592109 2138477591467219901847041)
                  ·
                    refine ⟨1603858193600414926385281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138477591467219901847041 1603858193600414926385281)
                    ·
                      refine ⟨1202893645200311194788961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603858193600414926385281 1202893645200311194788961)
                      ·
                        rfl

theorem cell23_2342627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_2342627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342627 prefixEnd_2342627 := by exact prefixLift 2342627
  have htrace : WordTrace (prefixWord ++ tailWord_2342627) baseStart_2342627 baseEnd_2342627 := by
    simpa [prefixWord, tailWord_2342627, baseEnd_2342627] using wordTrace_append hprefix tailTrace_2342627
  have hstable : (prefixWord ++ tailWord_2342627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342627).length < 2 ^ (prefixWord ++ tailWord_2342627).sum := by decide
  have hdescent : baseEnd_2342627 < baseStart_2342627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342643 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 3]
def baseStart_2342643 : Nat := 118140960795 + 2342643 * 2 ^ 59
def prefixEnd_2342643 : Nat := 4983230072969 + 3 ^ 40 * 2342643 * 2
def baseEnd_2342643 : Nat := 1202901860890783132188887

theorem tailTrace_2342643 : CollatzResearch.WordTrace tailWord_2342643 prefixEnd_2342643 1202901860890783132188887 := by
  unfold tailWord_2342643
  simp only [CollatzResearch.WordTrace]
  refine ⟨85443209652011977416592583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56962139768007984944395055 85443209652011977416592583)
  ·
    refine ⟨128164814478017966124888875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85443209652011977416592583 128164814478017966124888875)
    ·
      refine ⟨192247221717026949187333313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128164814478017966124888875 192247221717026949187333313)
      ·
        refine ⟨144185416287770211890499985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192247221717026949187333313 144185416287770211890499985)
        ·
          refine ⟨108139062215827658917874989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144185416287770211890499985 108139062215827658917874989)
          ·
            refine ⟨40552148330935372094203121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108139062215827658917874989 40552148330935372094203121)
            ·
              refine ⟨30414111248201529070652341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40552148330935372094203121 30414111248201529070652341)
              ·
                refine ⟨2851322929518893350373657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30414111248201529070652341 2851322929518893350373657)
                ·
                  refine ⟨2138492197139170012780243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2851322929518893350373657 2138492197139170012780243)
                  ·
                    refine ⟨3207738295708755019170365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2138492197139170012780243 3207738295708755019170365)
                    ·
                      refine ⟨1202901860890783132188887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3207738295708755019170365 1202901860890783132188887)
                      ·
                        rfl

theorem cell23_2342643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 3].length) (baseStart_2342643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342643 prefixEnd_2342643 := by exact prefixLift 2342643
  have htrace : WordTrace (prefixWord ++ tailWord_2342643) baseStart_2342643 baseEnd_2342643 := by
    simpa [prefixWord, tailWord_2342643, baseEnd_2342643] using wordTrace_append hprefix tailTrace_2342643
  have hstable : (prefixWord ++ tailWord_2342643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342643).length < 2 ^ (prefixWord ++ tailWord_2342643).sum := by decide
  have hdescent : baseEnd_2342643 < baseStart_2342643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342644 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2342644 : Nat := 118140960795 + 2342644 * 2 ^ 59
def prefixEnd_2342644 : Nat := 4983230072969 + 3 ^ 40 * 2342644 * 2
def baseEnd_2342644 : Nat := 1202902374371437628276383

theorem tailTrace_2342644 : CollatzResearch.WordTrace tailWord_2342644 prefixEnd_2342644 1202902374371437628276383 := by
  unfold tailWord_2342644
  simp only [CollatzResearch.WordTrace]
  refine ⟨42721623062504177293689493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56962164083338903058252657 42721623062504177293689493)
  ·
    refine ⟨2002576081054883310641695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42721623062504177293689493 2002576081054883310641695)
    ·
      refine ⟨3003864121582324965962543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2002576081054883310641695 3003864121582324965962543)
      ·
        refine ⟨4505796182373487448943815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003864121582324965962543 4505796182373487448943815)
        ·
          refine ⟨6758694273560231173415723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4505796182373487448943815 6758694273560231173415723)
          ·
            refine ⟨10138041410340346760123585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6758694273560231173415723 10138041410340346760123585)
            ·
              refine ⟨7603531057755260070092689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10138041410340346760123585 7603531057755260070092689)
              ·
                refine ⟨5702648293316445052569517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7603531057755260070092689 5702648293316445052569517)
                ·
                  refine ⟨2138493109993666894713569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5702648293316445052569517 2138493109993666894713569)
                  ·
                    refine ⟨1603869832495250171035177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138493109993666894713569 1603869832495250171035177)
                    ·
                      refine ⟨1202902374371437628276383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603869832495250171035177 1202902374371437628276383)
                      ·
                        rfl

theorem cell23_2342644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2342644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342644 prefixEnd_2342644 := by exact prefixLift 2342644
  have htrace : WordTrace (prefixWord ++ tailWord_2342644) baseStart_2342644 baseEnd_2342644 := by
    simpa [prefixWord, tailWord_2342644, baseEnd_2342644] using wordTrace_append hprefix tailTrace_2342644
  have hstable : (prefixWord ++ tailWord_2342644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342644).length < 2 ^ (prefixWord ++ tailWord_2342644).sum := by decide
  have hdescent : baseEnd_2342644 < baseStart_2342644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342659 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 1, 8]
def baseStart_2342659 : Nat := 118140960795 + 2342659 * 2 ^ 59
def prefixEnd_2342659 : Nat := 4983230072969 + 3 ^ 40 * 2342659 * 2
def baseEnd_2342659 : Nat := 400970025527085023196271

theorem tailTrace_2342659 : CollatzResearch.WordTrace tailWord_2342659 prefixEnd_2342659 400970025527085023196271 := by
  unfold tailWord_2342659
  simp only [CollatzResearch.WordTrace]
  refine ⟨85443793219954012149175031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56962528813302674766116687 85443793219954012149175031)
  ·
    refine ⟨128165689829931018223762547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85443793219954012149175031 128165689829931018223762547)
    ·
      refine ⟨192248534744896527335643821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128165689829931018223762547 192248534744896527335643821)
      ·
        refine ⟨72093200529336197750866433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192248534744896527335643821 72093200529336197750866433)
        ·
          refine ⟨54069900397002148313149825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72093200529336197750866433 54069900397002148313149825)
          ·
            refine ⟨40552425297751611234862369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54069900397002148313149825 40552425297751611234862369)
            ·
              refine ⟨30414318973313708426146777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40552425297751611234862369 30414318973313708426146777)
              ·
                refine ⟨22810739229985281319610083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30414318973313708426146777 22810739229985281319610083)
                ·
                  refine ⟨34216108844977921979415125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22810739229985281319610083 34216108844977921979415125)
                  ·
                    refine ⟨400970025527085023196271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34216108844977921979415125 400970025527085023196271)
                    ·
                      rfl

theorem cell23_2342659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 8].length) (baseStart_2342659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342659 prefixEnd_2342659 := by exact prefixLift 2342659
  have htrace : WordTrace (prefixWord ++ tailWord_2342659) baseStart_2342659 baseEnd_2342659 := by
    simpa [prefixWord, tailWord_2342659, baseEnd_2342659] using wordTrace_append hprefix tailTrace_2342659
  have hstable : (prefixWord ++ tailWord_2342659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342659).length < 2 ^ (prefixWord ++ tailWord_2342659).sum := by decide
  have hdescent : baseEnd_2342659 < baseStart_2342659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342670 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_2342670 : Nat := 118140960795 + 2342670 * 2 ^ 59
def prefixEnd_2342670 : Nat := 4983230072969 + 3 ^ 40 * 2342670 * 2
def baseEnd_2342670 : Nat := 1202915724868454526551263

theorem tailTrace_2342670 : CollatzResearch.WordTrace tailWord_2342670 prefixEnd_2342670 1202915724868454526551263 := by
  unfold tailWord_2342670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10680524302864270128478183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56962796281942774018550309 10680524302864270128478183)
  ·
    refine ⟨16020786454296405192717275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10680524302864270128478183 16020786454296405192717275)
    ·
      refine ⟨24031179681444607789075913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16020786454296405192717275 24031179681444607789075913)
      ·
        refine ⟨18023384761083455841806935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24031179681444607789075913 18023384761083455841806935)
        ·
          refine ⟨27035077141625183762710403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18023384761083455841806935 27035077141625183762710403)
          ·
            refine ⟨40552615712437775644065605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27035077141625183762710403 40552615712437775644065605)
            ·
              refine ⟨7603615446082082933262301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40552615712437775644065605 7603615446082082933262301)
              ·
                refine ⟨2851355792280781099973363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7603615446082082933262301 2851355792280781099973363)
                ·
                  refine ⟨4277033688421171649960045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851355792280781099973363 4277033688421171649960045)
                  ·
                    refine ⟨1603887633157939368735017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4277033688421171649960045 1603887633157939368735017)
                    ·
                      refine ⟨1202915724868454526551263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603887633157939368735017 1202915724868454526551263)
                      ·
                        rfl

theorem cell23_2342670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_2342670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342670 prefixEnd_2342670 := by exact prefixLift 2342670
  have htrace : WordTrace (prefixWord ++ tailWord_2342670) baseStart_2342670 baseEnd_2342670 := by
    simpa [prefixWord, tailWord_2342670, baseEnd_2342670] using wordTrace_append hprefix tailTrace_2342670
  have hstable : (prefixWord ++ tailWord_2342670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342670).length < 2 ^ (prefixWord ++ tailWord_2342670).sum := by decide
  have hdescent : baseEnd_2342670 < baseStart_2342670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342699 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 7]
def baseStart_2342699 : Nat := 118140960795 + 2342699 * 2 ^ 59
def prefixEnd_2342699 : Nat := 4983230072969 + 3 ^ 40 * 2342699 * 2
def baseEnd_2342699 : Nat := 1202930615807434913088629

theorem tailTrace_2342699 : CollatzResearch.WordTrace tailWord_2342699 prefixEnd_2342699 1202930615807434913088629 := by
  unfold tailWord_2342699
  simp only [CollatzResearch.WordTrace]
  refine ⟨85445252139809098980631151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56963501426539399320420767 85445252139809098980631151)
  ·
    refine ⟨128167878209713648470946727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85445252139809098980631151 128167878209713648470946727)
    ·
      refine ⟨192251817314570472706420091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128167878209713648470946727 192251817314570472706420091)
      ·
        refine ⟨288377725971855709059630137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192251817314570472706420091 288377725971855709059630137)
        ·
          refine ⟨216283294478891781794722603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288377725971855709059630137 216283294478891781794722603)
          ·
            refine ⟨324424941718337672692083905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216283294478891781794722603 324424941718337672692083905)
            ·
              refine ⟨243318706288753254519062929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324424941718337672692083905 243318706288753254519062929)
              ·
                refine ⟨182489029716564940889297197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243318706288753254519062929 182489029716564940889297197)
                ·
                  refine ⟨68433386143711852833486449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182489029716564940889297197 68433386143711852833486449)
                  ·
                    refine ⟨51325039607783889625114837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68433386143711852833486449 51325039607783889625114837)
                    ·
                      refine ⟨1202930615807434913088629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51325039607783889625114837 1202930615807434913088629)
                      ·
                        rfl

theorem cell23_2342699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_2342699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342699 prefixEnd_2342699 := by exact prefixLift 2342699
  have htrace : WordTrace (prefixWord ++ tailWord_2342699) baseStart_2342699 baseEnd_2342699 := by
    simpa [prefixWord, tailWord_2342699, baseEnd_2342699] using wordTrace_append hprefix tailTrace_2342699
  have hstable : (prefixWord ++ tailWord_2342699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342699).length < 2 ^ (prefixWord ++ tailWord_2342699).sum := by decide
  have hdescent : baseEnd_2342699 < baseStart_2342699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342740 : List Nat := [2, 4, 1, 1, 3, 2, 1, 4, 5]
def baseStart_2342740 : Nat := 118140960795 + 2342740 * 2 ^ 59
def prefixEnd_2342740 : Nat := 4983230072969 + 3 ^ 40 * 2342740 * 2
def baseEnd_2342740 : Nat := 133661296501585472519549

theorem tailTrace_2342740 : CollatzResearch.WordTrace tailWord_2342740 prefixEnd_2342740 133661296501585472519549 := by
  unfold tailWord_2342740
  simp only [CollatzResearch.WordTrace]
  refine ⟨42723373766330281491436837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56964498355107041988582449 42723373766330281491436837)
  ·
    refine ⟨8010632581186927779644407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42723373766330281491436837 8010632581186927779644407)
    ·
      refine ⟨12015948871780391669466611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8010632581186927779644407 12015948871780391669466611)
      ·
        refine ⟨18023923307670587504199917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12015948871780391669466611 18023923307670587504199917)
        ·
          refine ⟨6758971240376470314074969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18023923307670587504199917 6758971240376470314074969)
          ·
            refine ⟨5069228430282352735556227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6758971240376470314074969 5069228430282352735556227)
            ·
              refine ⟨7603842645423529103334341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5069228430282352735556227 7603842645423529103334341)
              ·
                refine ⟨1425720496016911706875189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7603842645423529103334341 1425720496016911706875189)
                ·
                  refine ⟨133661296501585472519549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1425720496016911706875189 133661296501585472519549)
                  ·
                    rfl

theorem cell23_2342740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_2342740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342740 prefixEnd_2342740 := by exact prefixLift 2342740
  have htrace : WordTrace (prefixWord ++ tailWord_2342740) baseStart_2342740 baseEnd_2342740 := by
    simpa [prefixWord, tailWord_2342740, baseEnd_2342740] using wordTrace_append hprefix tailTrace_2342740
  have hstable : (prefixWord ++ tailWord_2342740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342740).length < 2 ^ (prefixWord ++ tailWord_2342740).sum := by decide
  have hdescent : baseEnd_2342740 < baseStart_2342740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342746 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_2342746 : Nat := 118140960795 + 2342746 * 2 ^ 59
def prefixEnd_2342746 : Nat := 4983230072969 + 3 ^ 40 * 2342746 * 2
def baseEnd_2342746 : Nat := 1202954749398196229200913

theorem tailTrace_2342746 : CollatzResearch.WordTrace tailWord_2342746 prefixEnd_2342746 1202954749398196229200913 := by
  unfold tailWord_2342746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21361741592659706501898023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56964644247092550671728061 21361741592659706501898023)
  ·
    refine ⟨32042612388989559752847035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21361741592659706501898023 32042612388989559752847035)
    ·
      refine ⟨48063918583484339629270553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32042612388989559752847035 48063918583484339629270553)
      ·
        refine ⟨36047938937613254721952915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48063918583484339629270553 36047938937613254721952915)
        ·
          refine ⟨54071908406419882082929373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36047938937613254721952915 54071908406419882082929373)
          ·
            refine ⟨20276965652407455781098515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54071908406419882082929373 20276965652407455781098515)
            ·
              refine ⟨30415448478611183671647773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20276965652407455781098515 30415448478611183671647773)
              ·
                refine ⟨11405793179479193876867915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30415448478611183671647773 11405793179479193876867915)
                ·
                  refine ⟨17108689769218790815301873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11405793179479193876867915 17108689769218790815301873)
                  ·
                    refine ⟨12831517326914093111476405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17108689769218790815301873 12831517326914093111476405)
                    ·
                      refine ⟨1202954749398196229200913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12831517326914093111476405 1202954749398196229200913)
                      ·
                        rfl

theorem cell23_2342746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_2342746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342746 prefixEnd_2342746 := by exact prefixLift 2342746
  have htrace : WordTrace (prefixWord ++ tailWord_2342746) baseStart_2342746 baseEnd_2342746 := by
    simpa [prefixWord, tailWord_2342746, baseEnd_2342746] using wordTrace_append hprefix tailTrace_2342746
  have hstable : (prefixWord ++ tailWord_2342746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342746).length < 2 ^ (prefixWord ++ tailWord_2342746).sum := by decide
  have hdescent : baseEnd_2342746 < baseStart_2342746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342773 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2342773 : Nat := 118140960795 + 2342773 * 2 ^ 59
def prefixEnd_2342773 : Nat := 4983230072969 + 3 ^ 40 * 2342773 * 2
def baseEnd_2342773 : Nat := 1202968613375867623563289

theorem tailTrace_2342773 : CollatzResearch.WordTrace tailWord_2342773 prefixEnd_2342773 1202968613375867623563289 := by
  unfold tailWord_2342773
  simp only [CollatzResearch.WordTrace]
  refine ⟨85447951141541009618824973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56965300761027339745883315 85447951141541009618824973)
  ·
    refine ⟨32042981678077878607059365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85447951141541009618824973 32042981678077878607059365)
    ·
      refine ⟨6008059064639602238823631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32042981678077878607059365 6008059064639602238823631)
      ·
        refine ⟨9012088596959403358235447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008059064639602238823631 9012088596959403358235447)
        ·
          refine ⟨13518132895439105037353171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9012088596959403358235447 13518132895439105037353171)
          ·
            refine ⟨20277199343158657556029757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13518132895439105037353171 20277199343158657556029757)
            ·
              refine ⟨7603949753684496583511159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20277199343158657556029757 7603949753684496583511159)
              ·
                refine ⟨11405924630526744875266739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7603949753684496583511159 11405924630526744875266739)
                ·
                  refine ⟨17108886945790117312900109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11405924630526744875266739 17108886945790117312900109)
                  ·
                    refine ⟨6415832604671293992337541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17108886945790117312900109 6415832604671293992337541)
                    ·
                      refine ⟨1202968613375867623563289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6415832604671293992337541 1202968613375867623563289)
                      ·
                        rfl

theorem cell23_2342773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2342773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342773 prefixEnd_2342773 := by exact prefixLift 2342773
  have htrace : WordTrace (prefixWord ++ tailWord_2342773) baseStart_2342773 baseEnd_2342773 := by
    simpa [prefixWord, tailWord_2342773, baseEnd_2342773] using wordTrace_append hprefix tailTrace_2342773
  have hstable : (prefixWord ++ tailWord_2342773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342773).length < 2 ^ (prefixWord ++ tailWord_2342773).sum := by decide
  have hdescent : baseEnd_2342773 < baseStart_2342773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342793 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 3]
def baseStart_2342793 : Nat := 118140960795 + 2342793 * 2 ^ 59
def prefixEnd_2342793 : Nat := 4983230072969 + 3 ^ 40 * 2342793 * 2
def baseEnd_2342793 : Nat := 1202978882988957545313197

theorem tailTrace_2342793 : CollatzResearch.WordTrace tailWord_2342793 prefixEnd_2342793 1202978882988957545313197 := by
  unfold tailWord_2342793
  simp only [CollatzResearch.WordTrace]
  refine ⟨85448680601468553034553033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56965787067645702023035355 85448680601468553034553033)
  ·
    refine ⟨64086510451101414775914775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85448680601468553034553033 64086510451101414775914775)
    ·
      refine ⟨96129765676652122163872163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64086510451101414775914775 96129765676652122163872163)
      ·
        refine ⟨144194648514978183245808245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96129765676652122163872163 144194648514978183245808245)
        ·
          refine ⟨13518248298279204679294523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144194648514978183245808245 13518248298279204679294523)
          ·
            refine ⟨20277372447418807018941785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13518248298279204679294523 20277372447418807018941785)
            ·
              refine ⟨15208029335564105264206339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20277372447418807018941785 15208029335564105264206339)
              ·
                refine ⟨22812044003346157896309509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15208029335564105264206339 22812044003346157896309509)
                ·
                  refine ⟨4277258250627404605558033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22812044003346157896309509 4277258250627404605558033)
                  ·
                    refine ⟨3207943687970553454168525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4277258250627404605558033 3207943687970553454168525)
                    ·
                      refine ⟨1202978882988957545313197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3207943687970553454168525 1202978882988957545313197)
                      ·
                        rfl

theorem cell23_2342793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_2342793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342793 prefixEnd_2342793 := by exact prefixLift 2342793
  have htrace : WordTrace (prefixWord ++ tailWord_2342793) baseStart_2342793 baseEnd_2342793 := by
    simpa [prefixWord, tailWord_2342793, baseEnd_2342793] using wordTrace_append hprefix tailTrace_2342793
  have hstable : (prefixWord ++ tailWord_2342793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342793).length < 2 ^ (prefixWord ++ tailWord_2342793).sum := by decide
  have hdescent : baseEnd_2342793 < baseStart_2342793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342816 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2342816 : Nat := 118140960795 + 2342816 * 2 ^ 59
def prefixEnd_2342816 : Nat := 4983230072969 + 3 ^ 40 * 2342816 * 2
def baseEnd_2342816 : Nat := 1202990693044010955325591

theorem tailTrace_2342816 : CollatzResearch.WordTrace tailWord_2342816 prefixEnd_2342816 1202990693044010955325591 := by
  unfold tailWord_2342816
  simp only [CollatzResearch.WordTrace]
  refine ⟨42724759740192613981320151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56966346320256818641760201 42724759740192613981320151)
  ·
    refine ⟨64087139610288920971980227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42724759740192613981320151 64087139610288920971980227)
    ·
      refine ⟨96130709415433381457970341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64087139610288920971980227 96130709415433381457970341)
      ·
        refine ⟨18024508015393759023369439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96130709415433381457970341 18024508015393759023369439)
        ·
          refine ⟨27036762023090638535054159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18024508015393759023369439 27036762023090638535054159)
          ·
            refine ⟨40555143034635957802581239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27036762023090638535054159 40555143034635957802581239)
            ·
              refine ⟨60832714551953936703871859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40555143034635957802581239 60832714551953936703871859)
              ·
                refine ⟨91249071827930905055807789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60832714551953936703871859 91249071827930905055807789)
                ·
                  refine ⟨34218401935474089395927921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91249071827930905055807789 34218401935474089395927921)
                  ·
                    refine ⟨25663801451605567046945941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34218401935474089395927921 25663801451605567046945941)
                    ·
                      refine ⟨1202990693044010955325591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25663801451605567046945941 1202990693044010955325591)
                      ·
                        rfl

theorem cell23_2342816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2342816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342816 prefixEnd_2342816 := by exact prefixLift 2342816
  have htrace : WordTrace (prefixWord ++ tailWord_2342816) baseStart_2342816 baseEnd_2342816 := by
    simpa [prefixWord, tailWord_2342816, baseEnd_2342816] using wordTrace_append hprefix tailTrace_2342816
  have hstable : (prefixWord ++ tailWord_2342816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342816).length < 2 ^ (prefixWord ++ tailWord_2342816).sum := by decide
  have hdescent : baseEnd_2342816 < baseStart_2342816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342863 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_2342863 : Nat := 118140960795 + 2342863 * 2 ^ 59
def prefixEnd_2342863 : Nat := 4983230072969 + 3 ^ 40 * 2342863 * 2
def baseEnd_2342863 : Nat := 1203014826634772271437875

theorem tailTrace_2342863 : CollatzResearch.WordTrace tailWord_2342863 prefixEnd_2342863 1203014826634772271437875 := by
  unfold tailWord_2342863
  simp only [CollatzResearch.WordTrace]
  refine ⟨85451233711214954989601243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56967489140809969993067495 85451233711214954989601243)
  ·
    refine ⟨128176850566822432484401865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85451233711214954989601243 128176850566822432484401865)
    ·
      refine ⟨96132637925116824363301399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128176850566822432484401865 96132637925116824363301399)
      ·
        refine ⟨144198956887675236544952099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96132637925116824363301399 144198956887675236544952099)
        ·
          refine ⟨216298435331512854817428149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144198956887675236544952099 216298435331512854817428149)
          ·
            refine ⟨20277978312329330139133889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 216298435331512854817428149 20277978312329330139133889)
            ·
              refine ⟨15208483734246997604350417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20277978312329330139133889 15208483734246997604350417)
              ·
                refine ⟨11406362800685248203262813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15208483734246997604350417 11406362800685248203262813)
                ·
                  refine ⟨4277386050256968076223555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11406362800685248203262813 4277386050256968076223555)
                  ·
                    refine ⟨6416079075385452114335333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4277386050256968076223555 6416079075385452114335333)
                    ·
                      refine ⟨1203014826634772271437875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6416079075385452114335333 1203014826634772271437875)
                      ·
                        rfl

theorem cell23_2342863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_2342863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342863 prefixEnd_2342863 := by exact prefixLift 2342863
  have htrace : WordTrace (prefixWord ++ tailWord_2342863) baseStart_2342863 baseEnd_2342863 := by
    simpa [prefixWord, tailWord_2342863, baseEnd_2342863] using wordTrace_append hprefix tailTrace_2342863
  have hstable : (prefixWord ++ tailWord_2342863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342863).length < 2 ^ (prefixWord ++ tailWord_2342863).sum := by decide
  have hdescent : baseEnd_2342863 < baseStart_2342863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342943 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2342943 : Nat := 118140960795 + 2342943 * 2 ^ 59
def prefixEnd_2342943 : Nat := 4983230072969 + 3 ^ 40 * 2342943 * 2
def baseEnd_2342943 : Nat := 1203055905087131958437507

theorem tailTrace_2342943 : CollatzResearch.WordTrace tailWord_2342943 prefixEnd_2342943 1203055905087131958437507 := by
  unfold tailWord_2342943
  simp only [CollatzResearch.WordTrace]
  refine ⟨85454151550925128652513483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56969434367283419101675655 85454151550925128652513483)
  ·
    refine ⟨128181227326387692978770225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85454151550925128652513483 128181227326387692978770225)
    ·
      refine ⟨96135920494790769734077669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128181227326387692978770225 96135920494790769734077669)
      ·
        refine ⟨18025485092773269325139563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96135920494790769734077669 18025485092773269325139563)
        ·
          refine ⟨27038227639159903987709345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18025485092773269325139563 27038227639159903987709345)
          ·
            refine ⟨20278670729369927990782009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27038227639159903987709345 20278670729369927990782009)
            ·
              refine ⟨15209003047027445993086507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20278670729369927990782009 15209003047027445993086507)
              ·
                refine ⟨22813504570541168989629761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15209003047027445993086507 22813504570541168989629761)
                ·
                  refine ⟨17110128427905876742222321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22813504570541168989629761 17110128427905876742222321)
                  ·
                    refine ⟨12832596320929407556666741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17110128427905876742222321 12832596320929407556666741)
                    ·
                      refine ⟨1203055905087131958437507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12832596320929407556666741 1203055905087131958437507)
                      ·
                        rfl

theorem cell23_2342943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2342943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342943 prefixEnd_2342943 := by exact prefixLift 2342943
  have htrace : WordTrace (prefixWord ++ tailWord_2342943) baseStart_2342943 baseEnd_2342943 := by
    simpa [prefixWord, tailWord_2342943, baseEnd_2342943] using wordTrace_append hprefix tailTrace_2342943
  have hstable : (prefixWord ++ tailWord_2342943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342943).length < 2 ^ (prefixWord ++ tailWord_2342943).sum := by decide
  have hdescent : baseEnd_2342943 < baseStart_2342943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342948 : List Nat := [2, 3, 1, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_2342948 : Nat := 118140960795 + 2342948 * 2 ^ 59
def prefixEnd_2342948 : Nat := 4983230072969 + 3 ^ 40 * 2342948 * 2
def baseEnd_2342948 : Nat := 1203058472490404438874985

theorem tailTrace_2342948 : CollatzResearch.WordTrace tailWord_2342948 prefixEnd_2342948 1203058472490404438874985 := by
  unfold tailWord_2342948
  simp only [CollatzResearch.WordTrace]
  refine ⟨42727166957953507253222749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56969555943938009670963665 42727166957953507253222749)
  ·
    refine ⟨16022687609232565219958531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42727166957953507253222749 16022687609232565219958531)
    ·
      refine ⟨24034031413848847829937797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16022687609232565219958531 24034031413848847829937797)
      ·
        refine ⟨4506380890096658968113337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24034031413848847829937797 4506380890096658968113337)
        ·
          refine ⟨3379785667572494226085003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4506380890096658968113337 3379785667572494226085003)
          ·
            refine ⟨5069678501358741339127505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379785667572494226085003 5069678501358741339127505)
            ·
              refine ⟨3802258876019056004345629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5069678501358741339127505 3802258876019056004345629)
              ·
                refine ⟨1425847078507146001629611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3802258876019056004345629 1425847078507146001629611)
                ·
                  refine ⟨2138770617760719002444417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425847078507146001629611 2138770617760719002444417)
                  ·
                    refine ⟨1604077963320539251833313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138770617760719002444417 1604077963320539251833313)
                    ·
                      refine ⟨1203058472490404438874985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604077963320539251833313 1203058472490404438874985)
                      ·
                        rfl

theorem cell23_2342948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_2342948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342948 prefixEnd_2342948 := by exact prefixLift 2342948
  have htrace : WordTrace (prefixWord ++ tailWord_2342948) baseStart_2342948 baseEnd_2342948 := by
    simpa [prefixWord, tailWord_2342948, baseEnd_2342948] using wordTrace_append hprefix tailTrace_2342948
  have hstable : (prefixWord ++ tailWord_2342948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342948).length < 2 ^ (prefixWord ++ tailWord_2342948).sum := by decide
  have hdescent : baseEnd_2342948 < baseStart_2342948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342963 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 2, 6]
def baseStart_2342963 : Nat := 118140960795 + 2342963 * 2 ^ 59
def prefixEnd_2342963 : Nat := 4983230072969 + 3 ^ 40 * 2342963 * 2
def baseEnd_2342963 : Nat := 401022058233407293395805

theorem tailTrace_2342963 : CollatzResearch.WordTrace tailWord_2342963 prefixEnd_2342963 401022058233407293395805 := by
  unfold tailWord_2342963
  simp only [CollatzResearch.WordTrace]
  refine ⟨85454881010852672068241543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56969920673901781378827695 85454881010852672068241543)
  ·
    refine ⟨128182321516279008102362315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85454881010852672068241543 128182321516279008102362315)
    ·
      refine ⟨192273482274418512153543473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128182321516279008102362315 192273482274418512153543473)
      ·
        refine ⟨144205111705813884115157605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192273482274418512153543473 144205111705813884115157605)
        ·
          refine ⟨27038458444840103271592051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144205111705813884115157605 27038458444840103271592051)
          ·
            refine ⟨40557687667260154907388077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27038458444840103271592051 40557687667260154907388077)
            ·
              refine ⟨15209132875222558090270529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40557687667260154907388077 15209132875222558090270529)
              ·
                refine ⟨11406849656416918567702897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15209132875222558090270529 11406849656416918567702897)
                ·
                  refine ⟨8555137242312688925777173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11406849656416918567702897 8555137242312688925777173)
                  ·
                    refine ⟨401022058233407293395805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8555137242312688925777173 401022058233407293395805)
                    ·
                      rfl

theorem cell23_2342963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 6].length) (baseStart_2342963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2342963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2342963 prefixEnd_2342963 := by exact prefixLift 2342963
  have htrace : WordTrace (prefixWord ++ tailWord_2342963) baseStart_2342963 baseEnd_2342963 := by
    simpa [prefixWord, tailWord_2342963, baseEnd_2342963] using wordTrace_append hprefix tailTrace_2342963
  have hstable : (prefixWord ++ tailWord_2342963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342963).length < 2 ^ (prefixWord ++ tailWord_2342963).sum := by decide
  have hdescent : baseEnd_2342963 < baseStart_2342963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343004 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_2343004 : Nat := 118140960795 + 2343004 * 2 ^ 59
def prefixEnd_2343004 : Nat := 4983230072969 + 3 ^ 40 * 2343004 * 2
def baseEnd_2343004 : Nat := 1203087227407056219774727

theorem tailTrace_2343004 : CollatzResearch.WordTrace tailWord_2343004 prefixEnd_2343004 1203087227407056219774727 := by
  unfold tailWord_2343004
  simp only [CollatzResearch.WordTrace]
  refine ⟨42728188201852068035242033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56970917602469424046989377 42728188201852068035242033)
  ·
    refine ⟨32046141151389051026431525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42728188201852068035242033 32046141151389051026431525)
    ·
      refine ⟨6008651465885447067455911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32046141151389051026431525 6008651465885447067455911)
      ·
        refine ⟨9012977198828170601183867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008651465885447067455911 9012977198828170601183867)
        ·
          refine ⟨13519465798242255901775801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9012977198828170601183867 13519465798242255901775801)
          ·
            refine ⟨10139599348681691926331851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13519465798242255901775801 10139599348681691926331851)
            ·
              refine ⟨15209399023022537889497777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10139599348681691926331851 15209399023022537889497777)
              ·
                refine ⟨11407049267266903417123333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15209399023022537889497777 11407049267266903417123333)
                ·
                  refine ⟨2138821737612544390710625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11407049267266903417123333 2138821737612544390710625)
                  ·
                    refine ⟨1604116303209408293032969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138821737612544390710625 1604116303209408293032969)
                    ·
                      refine ⟨1203087227407056219774727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604116303209408293032969 1203087227407056219774727)
                      ·
                        rfl

theorem cell23_2343004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_2343004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343004 prefixEnd_2343004 := by exact prefixLift 2343004
  have htrace : WordTrace (prefixWord ++ tailWord_2343004) baseStart_2343004 baseEnd_2343004 := by
    simpa [prefixWord, tailWord_2343004, baseEnd_2343004] using wordTrace_append hprefix tailTrace_2343004
  have hstable : (prefixWord ++ tailWord_2343004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343004).length < 2 ^ (prefixWord ++ tailWord_2343004).sum := by decide
  have hdescent : baseEnd_2343004 < baseStart_2343004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343077 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 2, 4, 2]
def baseStart_2343077 : Nat := 118140960795 + 2343077 * 2 ^ 59
def prefixEnd_2343077 : Nat := 4983230072969 + 3 ^ 40 * 2343077 * 2
def baseEnd_2343077 : Nat := 1203124711494834434161891

theorem tailTrace_2343077 : CollatzResearch.WordTrace tailWord_2343077 prefixEnd_2343077 1203124711494834434161891 := by
  unfold tailWord_2343077
  simp only [CollatzResearch.WordTrace]
  refine ⟨85459038932439669537891485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56972692621626446358594323 85459038932439669537891485)
  ·
    refine ⟨32047139599664876076709307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85459038932439669537891485 32047139599664876076709307)
    ·
      refine ⟨48070709399497314115063961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32047139599664876076709307 48070709399497314115063961)
      ·
        refine ⟨36053032049622985586297971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48070709399497314115063961 36053032049622985586297971)
        ·
          refine ⟨54079548074434478379446957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36053032049622985586297971 54079548074434478379446957)
          ·
            refine ⟨20279830527912929392292609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54079548074434478379446957 20279830527912929392292609)
            ·
              refine ⟨15209872895934697044219457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20279830527912929392292609 15209872895934697044219457)
              ·
                refine ⟨11407404671951022783164593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15209872895934697044219457 11407404671951022783164593)
                ·
                  refine ⟨8555553503963267087373445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11407404671951022783164593 8555553503963267087373445)
                  ·
                    refine ⟨1604166281993112578882521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8555553503963267087373445 1604166281993112578882521)
                    ·
                      refine ⟨1203124711494834434161891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604166281993112578882521 1203124711494834434161891)
                      ·
                        rfl

theorem cell23_2343077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_2343077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343077 prefixEnd_2343077 := by exact prefixLift 2343077
  have htrace : WordTrace (prefixWord ++ tailWord_2343077) baseStart_2343077 baseEnd_2343077 := by
    simpa [prefixWord, tailWord_2343077, baseEnd_2343077] using wordTrace_append hprefix tailTrace_2343077
  have hstable : (prefixWord ++ tailWord_2343077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343077).length < 2 ^ (prefixWord ++ tailWord_2343077).sum := by decide
  have hdescent : baseEnd_2343077 < baseStart_2343077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343083 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 14]
def baseStart_2343083 : Nat := 118140960795 + 2343083 * 2 ^ 59
def prefixEnd_2343083 : Nat := 4983230072969 + 3 ^ 40 * 2343083 * 2
def baseEnd_2343083 : Nat := 133680865819862378965207

theorem tailTrace_2343083 : CollatzResearch.WordTrace tailWord_2343083 prefixEnd_2343083 133680865819862378965207 := by
  unfold tailWord_2343083
  simp only [CollatzResearch.WordTrace]
  refine ⟨85459257770417932562609903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56972838513611955041739935 85459257770417932562609903)
  ·
    refine ⟨128188886655626898843914855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85459257770417932562609903 128188886655626898843914855)
    ·
      refine ⟨192283329983440348265872283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128188886655626898843914855 192283329983440348265872283)
      ·
        refine ⟨288424994975160522398808425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192283329983440348265872283 288424994975160522398808425)
        ·
          refine ⟨216318746231370391799106319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288424994975160522398808425 216318746231370391799106319)
          ·
            refine ⟨324478119347055587698659479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216318746231370391799106319 324478119347055587698659479)
            ·
              refine ⟨486717179020583381547989219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324478119347055587698659479 486717179020583381547989219)
              ·
                refine ⟨730075768530875072321983829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486717179020583381547989219 730075768530875072321983829)
                ·
                  refine ⟨133680865819862378965207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 14 730075768530875072321983829 133680865819862378965207)
                  ·
                    rfl

theorem cell23_2343083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 14].length) (baseStart_2343083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343083 prefixEnd_2343083 := by exact prefixLift 2343083
  have htrace : WordTrace (prefixWord ++ tailWord_2343083) baseStart_2343083 baseEnd_2343083 := by
    simpa [prefixWord, tailWord_2343083, baseEnd_2343083] using wordTrace_append hprefix tailTrace_2343083
  have hstable : (prefixWord ++ tailWord_2343083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343083).length < 2 ^ (prefixWord ++ tailWord_2343083).sum := by decide
  have hdescent : baseEnd_2343083 < baseStart_2343083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343127 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_2343127 : Nat := 118140960795 + 2343127 * 2 ^ 59
def prefixEnd_2343127 : Nat := 4983230072969 + 3 ^ 40 * 2343127 * 2
def baseEnd_2343127 : Nat := 1203150385527559238536661

theorem tailTrace_2343127 : CollatzResearch.WordTrace tailWord_2343127 prefixEnd_2343127 1203150385527559238536661 := by
  unfold tailWord_2343127
  simp only [CollatzResearch.WordTrace]
  refine ⟨85460862582258528077211635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56973908388172352051474423 85460862582258528077211635)
  ·
    refine ⟨128191293873387792115817453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85460862582258528077211635 128191293873387792115817453)
    ·
      refine ⟨48071735202520422043431545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128191293873387792115817453 48071735202520422043431545)
      ·
        refine ⟨36053801401890316532573659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48071735202520422043431545 36053801401890316532573659)
        ·
          refine ⟨54080702102835474798860489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36053801401890316532573659 54080702102835474798860489)
          ·
            refine ⟨40560526577126606099145367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54080702102835474798860489 40560526577126606099145367)
            ·
              refine ⟨60840789865689909148718051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40560526577126606099145367 60840789865689909148718051)
              ·
                refine ⟨91261184798534863723077077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60840789865689909148718051 91261184798534863723077077)
                ·
                  refine ⟨2138934018715660868509619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91261184798534863723077077 2138934018715660868509619)
                  ·
                    refine ⟨3208401028073491302764429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2138934018715660868509619 3208401028073491302764429)
                    ·
                      refine ⟨1203150385527559238536661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3208401028073491302764429 1203150385527559238536661)
                      ·
                        rfl

theorem cell23_2343127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_2343127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343127 prefixEnd_2343127 := by exact prefixLift 2343127
  have htrace : WordTrace (prefixWord ++ tailWord_2343127) baseStart_2343127 baseEnd_2343127 := by
    simpa [prefixWord, tailWord_2343127, baseEnd_2343127] using wordTrace_append hprefix tailTrace_2343127
  have hstable : (prefixWord ++ tailWord_2343127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343127).length < 2 ^ (prefixWord ++ tailWord_2343127).sum := by decide
  have hdescent : baseEnd_2343127 < baseStart_2343127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343144 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_2343144 : Nat := 118140960795 + 2343144 * 2 ^ 59
def prefixEnd_2343144 : Nat := 4983230072969 + 3 ^ 40 * 2343144 * 2
def baseEnd_2343144 : Nat := 1203159114698685672024083

theorem tailTrace_2343144 : CollatzResearch.WordTrace tailWord_2343144 prefixEnd_2343144 1203159114698685672024083 := by
  unfold tailWord_2343144
  simp only [CollatzResearch.WordTrace]
  refine ⟨42730741311598469990290243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56974321748797959987053657 42730741311598469990290243)
  ·
    refine ⟨64096111967397704985435365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42730741311598469990290243 64096111967397704985435365)
    ·
      refine ⟨12018020993887069684769131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64096111967397704985435365 12018020993887069684769131)
      ·
        refine ⟨18027031490830604527153697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12018020993887069684769131 18027031490830604527153697)
        ·
          refine ⟨13520273618122953395365273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18027031490830604527153697 13520273618122953395365273)
          ·
            refine ⟨10140205213592215046523955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13520273618122953395365273 10140205213592215046523955)
            ·
              refine ⟨15210307820388322569785933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10140205213592215046523955 15210307820388322569785933)
              ·
                refine ⟨5703865432645620963669725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15210307820388322569785933 5703865432645620963669725)
                ·
                  refine ⟨2138949537242107861376147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5703865432645620963669725 2138949537242107861376147)
                  ·
                    refine ⟨3208424305863161792064221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2138949537242107861376147 3208424305863161792064221)
                    ·
                      refine ⟨1203159114698685672024083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3208424305863161792064221 1203159114698685672024083)
                      ·
                        rfl

theorem cell23_2343144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_2343144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343144 prefixEnd_2343144 := by exact prefixLift 2343144
  have htrace : WordTrace (prefixWord ++ tailWord_2343144) baseStart_2343144 baseEnd_2343144 := by
    simpa [prefixWord, tailWord_2343144, baseEnd_2343144] using wordTrace_append hprefix tailTrace_2343144
  have hstable : (prefixWord ++ tailWord_2343144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343144).length < 2 ^ (prefixWord ++ tailWord_2343144).sum := by decide
  have hdescent : baseEnd_2343144 < baseStart_2343144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343154 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_2343154 : Nat := 118140960795 + 2343154 * 2 ^ 59
def prefixEnd_2343154 : Nat := 4983230072969 + 3 ^ 40 * 2343154 * 2
def baseEnd_2343154 : Nat := 1203164249505230632899037

theorem tailTrace_2343154 : CollatzResearch.WordTrace tailWord_2343154 prefixEnd_2343154 1203164249505230632899037 := by
  unfold tailWord_2343154
  simp only [CollatzResearch.WordTrace]
  refine ⟨21365461838290177922111129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56974564902107141125629677 21365461838290177922111129)
  ·
    refine ⟨16024096378717633441583347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21365461838290177922111129 16024096378717633441583347)
    ·
      refine ⟨24036144568076450162375021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16024096378717633441583347 24036144568076450162375021)
      ·
        refine ⟨9013554213028668810890633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24036144568076450162375021 9013554213028668810890633)
        ·
          refine ⟨6760165659771501608167975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9013554213028668810890633 6760165659771501608167975)
          ·
            refine ⟨10140248489657252412251963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6760165659771501608167975 10140248489657252412251963)
            ·
              refine ⟨15210372734485878618377945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10140248489657252412251963 15210372734485878618377945)
              ·
                refine ⟨11407779550864408963783459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15210372734485878618377945 11407779550864408963783459)
                ·
                  refine ⟨17111669326296613445675189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11407779550864408963783459 17111669326296613445675189)
                  ·
                    refine ⟨1604218999340307510532049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17111669326296613445675189 1604218999340307510532049)
                    ·
                      refine ⟨1203164249505230632899037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604218999340307510532049 1203164249505230632899037)
                      ·
                        rfl

theorem cell23_2343154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_2343154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343154 prefixEnd_2343154 := by exact prefixLift 2343154
  have htrace : WordTrace (prefixWord ++ tailWord_2343154) baseStart_2343154 baseEnd_2343154 := by
    simpa [prefixWord, tailWord_2343154, baseEnd_2343154] using wordTrace_append hprefix tailTrace_2343154
  have hstable : (prefixWord ++ tailWord_2343154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343154).length < 2 ^ (prefixWord ++ tailWord_2343154).sum := by decide
  have hdescent : baseEnd_2343154 < baseStart_2343154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343164 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_2343164 : Nat := 118140960795 + 2343164 * 2 ^ 59
def prefixEnd_2343164 : Nat := 4983230072969 + 3 ^ 40 * 2343164 * 2
def baseEnd_2343164 : Nat := 401056461437258531257997

theorem tailTrace_2343164 : CollatzResearch.WordTrace tailWord_2343164 prefixEnd_2343164 401056461437258531257997 := by
  unfold tailWord_2343164
  simp only [CollatzResearch.WordTrace]
  refine ⟨42731106041562241698154273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56974808055416322264205697 42731106041562241698154273)
  ·
    refine ⟨32048329531171681273615705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42731106041562241698154273 32048329531171681273615705)
    ·
      refine ⟨24036247148378760955211779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32048329531171681273615705 24036247148378760955211779)
      ·
        refine ⟨36054370722568141432817669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24036247148378760955211779 36054370722568141432817669)
        ·
          refine ⟨6760194510481526518653313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36054370722568141432817669 6760194510481526518653313)
          ·
            refine ⟨5070145882861144888989985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6760194510481526518653313 5070145882861144888989985)
            ·
              refine ⟨3802609412145858666742489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5070145882861144888989985 3802609412145858666742489)
              ·
                refine ⟨2851957059109394000056867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3802609412145858666742489 2851957059109394000056867)
                ·
                  refine ⟨4277935588664091000085301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851957059109394000056867 4277935588664091000085301)
                  ·
                    refine ⟨401056461437258531257997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4277935588664091000085301 401056461437258531257997)
                    ·
                      rfl

theorem cell23_2343164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_2343164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343164 prefixEnd_2343164 := by exact prefixLift 2343164
  have htrace : WordTrace (prefixWord ++ tailWord_2343164) baseStart_2343164 baseEnd_2343164 := by
    simpa [prefixWord, tailWord_2343164, baseEnd_2343164] using wordTrace_append hprefix tailTrace_2343164
  have hstable : (prefixWord ++ tailWord_2343164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343164).length < 2 ^ (prefixWord ++ tailWord_2343164).sum := by decide
  have hdescent : baseEnd_2343164 < baseStart_2343164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343167 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 2, 6, 2]
def baseStart_2343167 : Nat := 118140960795 + 2343167 * 2 ^ 59
def prefixEnd_2343167 : Nat := 4983230072969 + 3 ^ 40 * 2343167 * 2
def baseEnd_2343167 : Nat := 1203170924753739082036477

theorem tailTrace_2343167 : CollatzResearch.WordTrace tailWord_2343167 prefixEnd_2343167 1203170924753739082036477 := by
  unfold tailWord_2343167
  simp only [CollatzResearch.WordTrace]
  refine ⟨85462321502113614908667755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56974881001409076605778503 85462321502113614908667755)
  ·
    refine ⟨128193482253170422363001633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85462321502113614908667755 128193482253170422363001633)
    ·
      refine ⟨96145111689877816772251225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128193482253170422363001633 96145111689877816772251225)
      ·
        refine ⟨72108833767408362579188419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96145111689877816772251225 72108833767408362579188419)
        ·
          refine ⟨108163250651112543868782629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72108833767408362579188419 108163250651112543868782629)
          ·
            refine ⟨20280609497083601975396743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108163250651112543868782629 20280609497083601975396743)
            ·
              refine ⟨30420914245625402963095115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20280609497083601975396743 30420914245625402963095115)
              ·
                refine ⟨45631371368438104444642673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30420914245625402963095115 45631371368438104444642673)
                ·
                  refine ⟨34223528526328578333482005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45631371368438104444642673 34223528526328578333482005)
                  ·
                    refine ⟨1604227899671652109381969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34223528526328578333482005 1604227899671652109381969)
                    ·
                      refine ⟨1203170924753739082036477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604227899671652109381969 1203170924753739082036477)
                      ·
                        rfl

theorem cell23_2343167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_2343167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343167 prefixEnd_2343167 := by exact prefixLift 2343167
  have htrace : WordTrace (prefixWord ++ tailWord_2343167) baseStart_2343167 baseEnd_2343167 := by
    simpa [prefixWord, tailWord_2343167, baseEnd_2343167] using wordTrace_append hprefix tailTrace_2343167
  have hstable : (prefixWord ++ tailWord_2343167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343167).length < 2 ^ (prefixWord ++ tailWord_2343167).sum := by decide
  have hdescent : baseEnd_2343167 < baseStart_2343167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343177 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 4, 4]
def baseStart_2343177 : Nat := 118140960795 + 2343177 * 2 ^ 59
def prefixEnd_2343177 : Nat := 4983230072969 + 3 ^ 40 * 2343177 * 2
def baseEnd_2343177 : Nat := 401058686520094680970477

theorem tailTrace_2343177 : CollatzResearch.WordTrace tailWord_2343177 prefixEnd_2343177 401058686520094680970477 := by
  unfold tailWord_2343177
  simp only [CollatzResearch.WordTrace]
  refine ⟨85462686232077386616531785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56975124154718257744354523 85462686232077386616531785)
  ·
    refine ⟨64097014674058039962398839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85462686232077386616531785 64097014674058039962398839)
    ·
      refine ⟨96145522011087059943598259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64097014674058039962398839 96145522011087059943598259)
      ·
        refine ⟨144218283016630589915397389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96145522011087059943598259 144218283016630589915397389)
        ·
          refine ⟨54081856131236471218274021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144218283016630589915397389 54081856131236471218274021)
          ·
            refine ⟨10140348024606838353426379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54081856131236471218274021 10140348024606838353426379)
            ·
              refine ⟨15210522036910257530139569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10140348024606838353426379 15210522036910257530139569)
              ·
                refine ⟨11407891527682693147604677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15210522036910257530139569 11407891527682693147604677)
                ·
                  refine ⟨2138979661440504965175877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11407891527682693147604677 2138979661440504965175877)
                  ·
                    refine ⟨401058686520094680970477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2138979661440504965175877 401058686520094680970477)
                    ·
                      rfl

theorem cell23_2343177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 4].length) (baseStart_2343177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343177 prefixEnd_2343177 := by exact prefixLift 2343177
  have htrace : WordTrace (prefixWord ++ tailWord_2343177) baseStart_2343177 baseEnd_2343177 := by
    simpa [prefixWord, tailWord_2343177, baseEnd_2343177] using wordTrace_append hprefix tailTrace_2343177
  have hstable : (prefixWord ++ tailWord_2343177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343177).length < 2 ^ (prefixWord ++ tailWord_2343177).sum := by decide
  have hdescent : baseEnd_2343177 < baseStart_2343177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343201 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_2343201 : Nat := 118140960795 + 2343201 * 2 ^ 59
def prefixEnd_2343201 : Nat := 4983230072969 + 3 ^ 40 * 2343201 * 2
def baseEnd_2343201 : Nat := 1203188383095991949011321

theorem tailTrace_2343201 : CollatzResearch.WordTrace tailWord_2343201 prefixEnd_2343201 1203188383095991949011321 := by
  unfold tailWord_2343201
  simp only [CollatzResearch.WordTrace]
  refine ⟨85463561583990438715405457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56975707722660292476936971 85463561583990438715405457)
  ·
    refine ⟨64097671187992829036554093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85463561583990438715405457 64097671187992829036554093)
    ·
      refine ⟨24036626695497310888707785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64097671187992829036554093 24036626695497310888707785)
      ·
        refine ⟨18027470021622983166530839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24036626695497310888707785 18027470021622983166530839)
        ·
          refine ⟨27041205032434474749796259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18027470021622983166530839 27041205032434474749796259)
          ·
            refine ⟨40561807548651712124694389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27041205032434474749796259 40561807548651712124694389)
            ·
              refine ⟨3802669457686098011690099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40561807548651712124694389 3802669457686098011690099)
              ·
                refine ⟨5704004186529147017535149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802669457686098011690099 5704004186529147017535149)
                ·
                  refine ⟨2139001569948430131575681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5704004186529147017535149 2139001569948430131575681)
                  ·
                    refine ⟨1604251177461322598681761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139001569948430131575681 1604251177461322598681761)
                    ·
                      refine ⟨1203188383095991949011321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604251177461322598681761 1203188383095991949011321)
                      ·
                        rfl

theorem cell23_2343201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_2343201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343201 prefixEnd_2343201 := by exact prefixLift 2343201
  have htrace : WordTrace (prefixWord ++ tailWord_2343201) baseStart_2343201 baseEnd_2343201 := by
    simpa [prefixWord, tailWord_2343201, baseEnd_2343201] using wordTrace_append hprefix tailTrace_2343201
  have hstable : (prefixWord ++ tailWord_2343201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343201).length < 2 ^ (prefixWord ++ tailWord_2343201).sum := by decide
  have hdescent : baseEnd_2343201 < baseStart_2343201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343218 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_2343218 : Nat := 118140960795 + 2343218 * 2 ^ 59
def prefixEnd_2343218 : Nat := 4983230072969 + 3 ^ 40 * 2343218 * 2
def baseEnd_2343218 : Nat := 1203197112267118382498743

theorem tailTrace_2343218 : CollatzResearch.WordTrace tailWord_2343218 prefixEnd_2343218 1203197112267118382498743 := by
  unfold tailWord_2343218
  simp only [CollatzResearch.WordTrace]
  refine ⟨21366045406232212654693577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56976121083285900412516205 21366045406232212654693577)
  ·
    refine ⟨16024534054674159491020183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21366045406232212654693577 16024534054674159491020183)
    ·
      refine ⟨24036801082011239236530275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16024534054674159491020183 24036801082011239236530275)
      ·
        refine ⟨36055201623016858854795413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24036801082011239236530275 36055201623016858854795413)
        ·
          refine ⟨1690087576078915258818535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36055201623016858854795413 1690087576078915258818535)
          ·
            refine ⟨2535131364118372888227803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690087576078915258818535 2535131364118372888227803)
            ·
              refine ⟨3802697046177559332341705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535131364118372888227803 3802697046177559332341705)
              ·
                refine ⟨2852022784633169499256279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3802697046177559332341705 2852022784633169499256279)
                ·
                  refine ⟨4278034176949754248884419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2852022784633169499256279 4278034176949754248884419)
                  ·
                    refine ⟨6417051265424631373326629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4278034176949754248884419 6417051265424631373326629)
                    ·
                      refine ⟨1203197112267118382498743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6417051265424631373326629 1203197112267118382498743)
                      ·
                        rfl

theorem cell23_2343218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_2343218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343218 prefixEnd_2343218 := by exact prefixLift 2343218
  have htrace : WordTrace (prefixWord ++ tailWord_2343218) baseStart_2343218 baseEnd_2343218 := by
    simpa [prefixWord, tailWord_2343218, baseEnd_2343218] using wordTrace_append hprefix tailTrace_2343218
  have hstable : (prefixWord ++ tailWord_2343218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343218).length < 2 ^ (prefixWord ++ tailWord_2343218).sum := by decide
  have hdescent : baseEnd_2343218 < baseStart_2343218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343252 : List Nat := [2, 4, 1, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_2343252 : Nat := 118140960795 + 2343252 * 2 ^ 59
def prefixEnd_2343252 : Nat := 4983230072969 + 3 ^ 40 * 2343252 * 2
def baseEnd_2343252 : Nat := 1203214570609371249473587

theorem tailTrace_2343252 : CollatzResearch.WordTrace tailWord_2343252 prefixEnd_2343252 1203214570609371249473587 := by
  unfold tailWord_2343252
  simp only [CollatzResearch.WordTrace]
  refine ⟨42732710853402837212756005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56976947804537116283674673 42732710853402837212756005)
  ·
    refine ⟨8012383285013031977391751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42732710853402837212756005 8012383285013031977391751)
    ·
      refine ⟨12018574927519547966087627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8012383285013031977391751 12018574927519547966087627)
      ·
        refine ⟨18027862391279321949131441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12018574927519547966087627 18027862391279321949131441)
        ·
          refine ⟨13520896793459491461848581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18027862391279321949131441 13520896793459491461848581)
          ·
            refine ⟨2535168148773654649096609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13520896793459491461848581 2535168148773654649096609)
            ·
              refine ⟨1901376111580240986822457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535168148773654649096609 1901376111580240986822457)
              ·
                refine ⟨1426032083685180740116843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901376111580240986822457 1426032083685180740116843)
                ·
                  refine ⟨2139048125527771110175265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426032083685180740116843 2139048125527771110175265)
                  ·
                    refine ⟨1604286094145828332631449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139048125527771110175265 1604286094145828332631449)
                    ·
                      refine ⟨1203214570609371249473587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604286094145828332631449 1203214570609371249473587)
                      ·
                        rfl

theorem cell23_2343252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_2343252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343252 prefixEnd_2343252 := by exact prefixLift 2343252
  have htrace : WordTrace (prefixWord ++ tailWord_2343252) baseStart_2343252 baseEnd_2343252 := by
    simpa [prefixWord, tailWord_2343252, baseEnd_2343252] using wordTrace_append hprefix tailTrace_2343252
  have hstable : (prefixWord ++ tailWord_2343252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343252).length < 2 ^ (prefixWord ++ tailWord_2343252).sum := by decide
  have hdescent : baseEnd_2343252 < baseStart_2343252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343267 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 2, 6]
def baseStart_2343267 : Nat := 118140960795 + 2343267 * 2 ^ 59
def prefixEnd_2343267 : Nat := 4983230072969 + 3 ^ 40 * 2343267 * 2
def baseEnd_2343267 : Nat := 401074090939729563595339

theorem tailTrace_2343267 : CollatzResearch.WordTrace tailWord_2343267 prefixEnd_2343267 401074090939729563595339 := by
  unfold tailWord_2343267
  simp only [CollatzResearch.WordTrace]
  refine ⟨85465968801751331987308055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56977312534500887991538703 85465968801751331987308055)
  ·
    refine ⟨128198953202626997980962083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85465968801751331987308055 128198953202626997980962083)
    ·
      refine ⟨192298429803940496971443125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128198953202626997980962083 192298429803940496971443125)
      ·
        refine ⟨18027977794119421591072793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192298429803940496971443125 18027977794119421591072793)
        ·
          refine ⟨13520983345589566193304595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18027977794119421591072793 13520983345589566193304595)
          ·
            refine ⟨20281475018384349289956893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13520983345589566193304595 20281475018384349289956893)
            ·
              refine ⟨7605553131894130983733835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20281475018384349289956893 7605553131894130983733835)
              ·
                refine ⟨11408329697841196475600753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7605553131894130983733835 11408329697841196475600753)
                ·
                  refine ⟨8556247273380897356700565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11408329697841196475600753 8556247273380897356700565)
                  ·
                    refine ⟨401074090939729563595339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8556247273380897356700565 401074090939729563595339)
                    ·
                      rfl

theorem cell23_2343267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 6].length) (baseStart_2343267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343267 prefixEnd_2343267 := by exact prefixLift 2343267
  have htrace : WordTrace (prefixWord ++ tailWord_2343267) baseStart_2343267 baseEnd_2343267 := by
    simpa [prefixWord, tailWord_2343267, baseEnd_2343267] using wordTrace_append hprefix tailTrace_2343267
  have hstable : (prefixWord ++ tailWord_2343267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343267).length < 2 ^ (prefixWord ++ tailWord_2343267).sum := by decide
  have hdescent : baseEnd_2343267 < baseStart_2343267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343308 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 2, 2, 2]
def baseStart_2343308 : Nat := 118140960795 + 2343308 * 2 ^ 59
def prefixEnd_2343308 : Nat := 4983230072969 + 3 ^ 40 * 2343308 * 2
def baseEnd_2343308 : Nat := 1203243325526023030373329

theorem tailTrace_2343308 : CollatzResearch.WordTrace tailWord_2343308 prefixEnd_2343308 1203243325526023030373329 := by
  unfold tailWord_2343308
  simp only [CollatzResearch.WordTrace]
  refine ⟨42733732097301397994775289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56978309463068530659700385 42733732097301397994775289)
  ·
    refine ⟨32050299072976048496081467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42733732097301397994775289 32050299072976048496081467)
    ·
      refine ⟨48075448609464072744122201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32050299072976048496081467 48075448609464072744122201)
      ·
        refine ⟨36056586457098054558091651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48075448609464072744122201 36056586457098054558091651)
        ·
          refine ⟨54084879685647081837137477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36056586457098054558091651 54084879685647081837137477)
          ·
            refine ⟨10140914941058827844463277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54084879685647081837137477 10140914941058827844463277)
            ·
              refine ⟨3802843102897060441673729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10140914941058827844463277 3802843102897060441673729)
              ·
                refine ⟨2852132327172795331255297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3802843102897060441673729 2852132327172795331255297)
                ·
                  refine ⟨2139099245379596498441473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2852132327172795331255297 2139099245379596498441473)
                  ·
                    refine ⟨1604324434034697373831105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139099245379596498441473 1604324434034697373831105)
                    ·
                      refine ⟨1203243325526023030373329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604324434034697373831105 1203243325526023030373329)
                      ·
                        rfl

theorem cell23_2343308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_2343308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343308 prefixEnd_2343308 := by exact prefixLift 2343308
  have htrace : WordTrace (prefixWord ++ tailWord_2343308) baseStart_2343308 baseEnd_2343308 := by
    simpa [prefixWord, tailWord_2343308, baseEnd_2343308] using wordTrace_append hprefix tailTrace_2343308
  have hstable : (prefixWord ++ tailWord_2343308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343308).length < 2 ^ (prefixWord ++ tailWord_2343308).sum := by decide
  have hdescent : baseEnd_2343308 < baseStart_2343308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343325 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_2343325 : Nat := 118140960795 + 2343325 * 2 ^ 59
def prefixEnd_2343325 : Nat := 4983230072969 + 3 ^ 40 * 2343325 * 2
def baseEnd_2343325 : Nat := 1203252054697149463860751

theorem tailTrace_2343325 : CollatzResearch.WordTrace tailWord_2343325 prefixEnd_2343325 1203252054697149463860751 := by
  unfold tailWord_2343325
  simp only [CollatzResearch.WordTrace]
  refine ⟨85468084235541207892919429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56978722823694138595279619 85468084235541207892919429)
  ·
    refine ⟨16025265794163976479922393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85468084235541207892919429 16025265794163976479922393)
    ·
      refine ⟨12018949345622982359941795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16025265794163976479922393 12018949345622982359941795)
      ·
        refine ⟨18028424018434473539912693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12018949345622982359941795 18028424018434473539912693)
        ·
          refine ⟨1690164751728231894366815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18028424018434473539912693 1690164751728231894366815)
          ·
            refine ⟨2535247127592347841550223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690164751728231894366815 2535247127592347841550223)
            ·
              refine ⟨3802870691388521762325335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535247127592347841550223 3802870691388521762325335)
              ·
                refine ⟨5704306037082782643488003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802870691388521762325335 5704306037082782643488003)
                ·
                  refine ⟨8556459055624173965232005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5704306037082782643488003 8556459055624173965232005)
                  ·
                    refine ⟨1604336072929532618481001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8556459055624173965232005 1604336072929532618481001)
                    ·
                      refine ⟨1203252054697149463860751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604336072929532618481001 1203252054697149463860751)
                      ·
                        rfl

theorem cell23_2343325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_2343325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343325 prefixEnd_2343325 := by exact prefixLift 2343325
  have htrace : WordTrace (prefixWord ++ tailWord_2343325) baseStart_2343325 baseEnd_2343325 := by
    simpa [prefixWord, tailWord_2343325, baseEnd_2343325] using wordTrace_append hprefix tailTrace_2343325
  have hstable : (prefixWord ++ tailWord_2343325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343325).length < 2 ^ (prefixWord ++ tailWord_2343325).sum := by decide
  have hdescent : baseEnd_2343325 < baseStart_2343325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343327 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 3, 7]
def baseStart_2343327 : Nat := 118140960795 + 2343327 * 2 ^ 59
def prefixEnd_2343327 : Nat := 4983230072969 + 3 ^ 40 * 2343327 * 2
def baseEnd_2343327 : Nat := 401084360552819485345247

theorem tailTrace_2343327 : CollatzResearch.WordTrace tailWord_2343327 prefixEnd_2343327 401084360552819485345247 := by
  unfold tailWord_2343327
  simp only [CollatzResearch.WordTrace]
  refine ⟨85468157181533962234492235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56978771454355974822994823 85468157181533962234492235)
  ·
    refine ⟨128202235772300943351738353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85468157181533962234492235 128202235772300943351738353)
    ·
      refine ⟨96151676829225707513803765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128202235772300943351738353 96151676829225707513803765)
      ·
        refine ⟨9014219702739910079419103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96151676829225707513803765 9014219702739910079419103)
        ·
          refine ⟨13521329554109865119128655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9014219702739910079419103 13521329554109865119128655)
          ·
            refine ⟨20281994331164797678692983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13521329554109865119128655 20281994331164797678692983)
            ·
              refine ⟨30422991496747196518039475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20281994331164797678692983 30422991496747196518039475)
              ·
                refine ⟨45634487245120794777059213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30422991496747196518039475 45634487245120794777059213)
                ·
                  refine ⟨17112932716920298041397205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45634487245120794777059213 17112932716920298041397205)
                  ·
                    refine ⟨401084360552819485345247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17112932716920298041397205 401084360552819485345247)
                    ·
                      rfl

theorem cell23_2343327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_2343327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343327 prefixEnd_2343327 := by exact prefixLift 2343327
  have htrace : WordTrace (prefixWord ++ tailWord_2343327) baseStart_2343327 baseEnd_2343327 := by
    simpa [prefixWord, tailWord_2343327, baseEnd_2343327] using wordTrace_append hprefix tailTrace_2343327
  have hstable : (prefixWord ++ tailWord_2343327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343327).length < 2 ^ (prefixWord ++ tailWord_2343327).sum := by decide
  have hdescent : baseEnd_2343327 < baseStart_2343327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343377 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_2343377 : Nat := 118140960795 + 2343377 * 2 ^ 59
def prefixEnd_2343377 : Nat := 4983230072969 + 3 ^ 40 * 2343377 * 2
def baseEnd_2343377 : Nat := 1203278755691183260410511

theorem tailTrace_2343377 : CollatzResearch.WordTrace tailWord_2343377 prefixEnd_2343377 1203278755691183260410511 := by
  unfold tailWord_2343377
  simp only [CollatzResearch.WordTrace]
  refine ⟨85469980831352820773812385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56979987220901880515874923 85469980831352820773812385)
  ·
    refine ⟨64102485623514615580359289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85469980831352820773812385 64102485623514615580359289)
    ·
      refine ⟨48076864217635961685269467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64102485623514615580359289 48076864217635961685269467)
      ·
        refine ⟨72115296326453942527904201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48076864217635961685269467 72115296326453942527904201)
        ·
          refine ⟨54086472244840456895928151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72115296326453942527904201 54086472244840456895928151)
          ·
            refine ⟨81129708367260685343892227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54086472244840456895928151 81129708367260685343892227)
            ·
              refine ⟨121694562550891028015838341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81129708367260685343892227 121694562550891028015838341)
              ·
                refine ⟨22817730478292067752969689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121694562550891028015838341 22817730478292067752969689)
                ·
                  refine ⟨17113297858719050814727267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22817730478292067752969689 17113297858719050814727267)
                  ·
                    refine ⟨25669946788078576222090901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17113297858719050814727267 25669946788078576222090901)
                    ·
                      refine ⟨1203278755691183260410511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25669946788078576222090901 1203278755691183260410511)
                      ·
                        rfl

theorem cell23_2343377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_2343377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343377 prefixEnd_2343377 := by exact prefixLift 2343377
  have htrace : WordTrace (prefixWord ++ tailWord_2343377) baseStart_2343377 baseEnd_2343377 := by
    simpa [prefixWord, tailWord_2343377, baseEnd_2343377] using wordTrace_append hprefix tailTrace_2343377
  have hstable : (prefixWord ++ tailWord_2343377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343377).length < 2 ^ (prefixWord ++ tailWord_2343377).sum := by decide
  have hdescent : baseEnd_2343377 < baseStart_2343377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343384 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2343384 : Nat := 118140960795 + 2343384 * 2 ^ 59
def prefixEnd_2343384 : Nat := 4983230072969 + 3 ^ 40 * 2343384 * 2
def baseEnd_2343384 : Nat := 1203282350055764733022979

theorem tailTrace_2343384 : CollatzResearch.WordTrace tailWord_2343384 prefixEnd_2343384 1203282350055764733022979 := by
  unfold tailWord_2343384
  simp only [CollatzResearch.WordTrace]
  refine ⟨42735118071163730484658603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56980157428218307312878137 42735118071163730484658603)
  ·
    refine ⟨64102677106745595726987905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42735118071163730484658603 64102677106745595726987905)
    ·
      refine ⟨48077007830059196795240929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64102677106745595726987905 48077007830059196795240929)
      ·
        refine ⟨36057755872544397596430697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48077007830059196795240929 36057755872544397596430697)
        ·
          refine ⟨27043316904408298197323023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36057755872544397596430697 27043316904408298197323023)
          ·
            refine ⟨40564975356612447295984535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27043316904408298197323023 40564975356612447295984535)
            ·
              refine ⟨60847463034918670943976803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40564975356612447295984535 60847463034918670943976803)
              ·
                refine ⟨91271194552378006415965205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60847463034918670943976803 91271194552378006415965205)
                ·
                  refine ⟨4278337244642719050748369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91271194552378006415965205 4278337244642719050748369)
                  ·
                    refine ⟨3208752933482039288061277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4278337244642719050748369 3208752933482039288061277)
                    ·
                      refine ⟨1203282350055764733022979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3208752933482039288061277 1203282350055764733022979)
                      ·
                        rfl

theorem cell23_2343384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2343384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343384 prefixEnd_2343384 := by exact prefixLift 2343384
  have htrace : WordTrace (prefixWord ++ tailWord_2343384) baseStart_2343384 baseEnd_2343384 := by
    simpa [prefixWord, tailWord_2343384, baseEnd_2343384] using wordTrace_append hprefix tailTrace_2343384
  have hstable : (prefixWord ++ tailWord_2343384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343384).length < 2 ^ (prefixWord ++ tailWord_2343384).sum := by decide
  have hdescent : baseEnd_2343384 < baseStart_2343384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343407 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_2343407 : Nat := 118140960795 + 2343407 * 2 ^ 59
def prefixEnd_2343407 : Nat := 4983230072969 + 3 ^ 40 * 2343407 * 2
def baseEnd_2343407 : Nat := 1203294160110818143035373

theorem tailTrace_2343407 : CollatzResearch.WordTrace tailWord_2343407 prefixEnd_2343407 1203294160110818143035373 := by
  unfold tailWord_2343407
  simp only [CollatzResearch.WordTrace]
  refine ⟨85471075021244135897404475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56980716680829423931602983 85471075021244135897404475)
  ·
    refine ⟨128206612531866203846106713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85471075021244135897404475 128206612531866203846106713)
    ·
      refine ⟨96154959398899652884580035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128206612531866203846106713 96154959398899652884580035)
      ·
        refine ⟨144232439098349479326870053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96154959398899652884580035 144232439098349479326870053)
        ·
          refine ⟨27043582330940527373788135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144232439098349479326870053 27043582330940527373788135)
          ·
            refine ⟨40565373496410791060682203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27043582330940527373788135 40565373496410791060682203)
            ·
              refine ⟨60848060244616186591023305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40565373496410791060682203 60848060244616186591023305)
              ·
                refine ⟨45636045183462139943267479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60848060244616186591023305 45636045183462139943267479)
                ·
                  refine ⟨68454067775193209914901219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45636045183462139943267479 68454067775193209914901219)
                  ·
                    refine ⟨102681101662789814872351829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68454067775193209914901219 102681101662789814872351829)
                    ·
                      refine ⟨1203294160110818143035373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 102681101662789814872351829 1203294160110818143035373)
                      ·
                        rfl

theorem cell23_2343407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_2343407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343407 prefixEnd_2343407 := by exact prefixLift 2343407
  have htrace : WordTrace (prefixWord ++ tailWord_2343407) baseStart_2343407 baseEnd_2343407 := by
    simpa [prefixWord, tailWord_2343407, baseEnd_2343407] using wordTrace_append hprefix tailTrace_2343407
  have hstable : (prefixWord ++ tailWord_2343407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343407).length < 2 ^ (prefixWord ++ tailWord_2343407).sum := by decide
  have hdescent : baseEnd_2343407 < baseStart_2343407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343425 : List Nat := [1, 2, 4, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2343425 : Nat := 118140960795 + 2343425 * 2 ^ 59
def prefixEnd_2343425 : Nat := 4983230072969 + 3 ^ 40 * 2343425 * 2
def baseEnd_2343425 : Nat := 401101134254199690870097

theorem tailTrace_2343425 : CollatzResearch.WordTrace tailWord_2343425 prefixEnd_2343425 401101134254199690870097 := by
  unfold tailWord_2343425
  simp only [CollatzResearch.WordTrace]
  refine ⟨85471731535178924971559729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56981154356785949981039819 85471731535178924971559729)
  ·
    refine ⟨64103798651384193728669797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85471731535178924971559729 64103798651384193728669797)
    ·
      refine ⟨12019462247134536324125587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64103798651384193728669797 12019462247134536324125587)
      ·
        refine ⟨18029193370701804486188381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12019462247134536324125587 18029193370701804486188381)
        ·
          refine ⟨6760947514013176682320643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18029193370701804486188381 6760947514013176682320643)
          ·
            refine ⟨10141421271019765023480965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6760947514013176682320643 10141421271019765023480965)
            ·
              refine ⟨1901516488316205941902681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10141421271019765023480965 1901516488316205941902681)
              ·
                refine ⟨1426137366237154456427011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901516488316205941902681 1426137366237154456427011)
                ·
                  refine ⟨2139206049355731684640517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426137366237154456427011 2139206049355731684640517)
                  ·
                    refine ⟨401101134254199690870097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2139206049355731684640517 401101134254199690870097)
                    ·
                      rfl

theorem cell23_2343425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2343425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343425 prefixEnd_2343425 := by exact prefixLift 2343425
  have htrace : WordTrace (prefixWord ++ tailWord_2343425) baseStart_2343425 baseEnd_2343425 := by
    simpa [prefixWord, tailWord_2343425, baseEnd_2343425] using wordTrace_append hprefix tailTrace_2343425
  have hstable : (prefixWord ++ tailWord_2343425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343425).length < 2 ^ (prefixWord ++ tailWord_2343425).sum := by decide
  have hdescent : baseEnd_2343425 < baseStart_2343425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343434 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_2343434 : Nat := 118140960795 + 2343434 * 2 ^ 59
def prefixEnd_2343434 : Nat := 4983230072969 + 3 ^ 40 * 2343434 * 2
def baseEnd_2343434 : Nat := 401102674696163179132583

theorem tailTrace_2343434 : CollatzResearch.WordTrace tailWord_2343434 prefixEnd_2343434 401102674696163179132583 := by
  unfold tailWord_2343434
  simp only [CollatzResearch.WordTrace]
  refine ⟨21368014948036579877159339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56981373194764213005758237 21368014948036579877159339)
  ·
    refine ⟨32052022422054869815739009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21368014948036579877159339 32052022422054869815739009)
    ·
      refine ⟨24039016816541152361804257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32052022422054869815739009 24039016816541152361804257)
      ·
        refine ⟨18029262612405864271353193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24039016816541152361804257 18029262612405864271353193)
        ·
          refine ⟨13521946959304398203514895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18029262612405864271353193 13521946959304398203514895)
          ·
            refine ⟨20282920438956597305272343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13521946959304398203514895 20282920438956597305272343)
            ·
              refine ⟨30424380658434895957908515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20282920438956597305272343 30424380658434895957908515)
              ·
                refine ⟨45636570987652343936862773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30424380658434895957908515 45636570987652343936862773)
                ·
                  refine ⟨4278428530092407244080885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45636570987652343936862773 4278428530092407244080885)
                  ·
                    refine ⟨401102674696163179132583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4278428530092407244080885 401102674696163179132583)
                    ·
                      rfl

theorem cell23_2343434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_2343434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343434 prefixEnd_2343434 := by exact prefixLift 2343434
  have htrace : WordTrace (prefixWord ++ tailWord_2343434) baseStart_2343434 baseEnd_2343434 := by
    simpa [prefixWord, tailWord_2343434, baseEnd_2343434] using wordTrace_append hprefix tailTrace_2343434
  have hstable : (prefixWord ++ tailWord_2343434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343434).length < 2 ^ (prefixWord ++ tailWord_2343434).sum := by decide
  have hdescent : baseEnd_2343434 < baseStart_2343434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343448 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2343448 : Nat := 118140960795 + 2343448 * 2 ^ 59
def prefixEnd_2343448 : Nat := 4983230072969 + 3 ^ 40 * 2343448 * 2
def baseEnd_2343448 : Nat := 1203315212817652482622685

theorem tailTrace_2343448 : CollatzResearch.WordTrace tailWord_2343448 prefixEnd_2343448 1203315212817652482622685 := by
  unfold tailWord_2343448
  simp only [CollatzResearch.WordTrace]
  refine ⟨42736285207047799949823499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56981713609397066599764665 42736285207047799949823499)
  ·
    refine ⟨64104427810571699924735249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42736285207047799949823499 64104427810571699924735249)
    ·
      refine ⟨48078320857928774943551437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64104427810571699924735249 48078320857928774943551437)
      ·
        refine ⟨18029370321723290603831789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48078320857928774943551437 18029370321723290603831789)
        ·
          refine ⟨6761013870646233976436921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18029370321723290603831789 6761013870646233976436921)
          ·
            refine ⟨5070760402984675482327691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6761013870646233976436921 5070760402984675482327691)
            ·
              refine ⟨7606140604477013223491537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070760402984675482327691 7606140604477013223491537)
              ·
                refine ⟨5704605453357759917618653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7606140604477013223491537 5704605453357759917618653)
                ·
                  refine ⟨2139227045009159969106995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5704605453357759917618653 2139227045009159969106995)
                  ·
                    refine ⟨3208840567513739953660493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2139227045009159969106995 3208840567513739953660493)
                    ·
                      refine ⟨1203315212817652482622685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3208840567513739953660493 1203315212817652482622685)
                      ·
                        rfl

theorem cell23_2343448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2343448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343448 prefixEnd_2343448 := by exact prefixLift 2343448
  have htrace : WordTrace (prefixWord ++ tailWord_2343448) baseStart_2343448 baseEnd_2343448 := by
    simpa [prefixWord, tailWord_2343448, baseEnd_2343448] using wordTrace_append hprefix tailTrace_2343448
  have hstable : (prefixWord ++ tailWord_2343448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343448).length < 2 ^ (prefixWord ++ tailWord_2343448).sum := by decide
  have hdescent : baseEnd_2343448 < baseStart_2343448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343481 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 4, 4]
def baseStart_2343481 : Nat := 118140960795 + 2343481 * 2 ^ 59
def prefixEnd_2343481 : Nat := 4983230072969 + 3 ^ 40 * 2343481 * 2
def baseEnd_2343481 : Nat := 401110719226416951170011

theorem tailTrace_2343481 : CollatzResearch.WordTrace tailWord_2343481 prefixEnd_2343481 401110719226416951170011 := by
  unfold tailWord_2343481
  simp only [CollatzResearch.WordTrace]
  refine ⟨85473774022976046535598297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56982516015317364357065531 85473774022976046535598297)
  ·
    refine ⟨64105330517232034901698723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85473774022976046535598297 64105330517232034901698723)
    ·
      refine ⟨96157995775848052352548085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64105330517232034901698723 96157995775848052352548085)
      ·
        refine ⟨9014812103985754908051383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96157995775848052352548085 9014812103985754908051383)
        ·
          refine ⟨13522218155978632362077075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9014812103985754908051383 13522218155978632362077075)
          ·
            refine ⟨20283327233967948543115613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13522218155978632362077075 20283327233967948543115613)
            ·
              refine ⟨7606247712737980703668355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20283327233967948543115613 7606247712737980703668355)
              ·
                refine ⟨11409371569106971055502533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7606247712737980703668355 11409371569106971055502533)
                ·
                  refine ⟨2139257169207557072906725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11409371569106971055502533 2139257169207557072906725)
                  ·
                    refine ⟨401110719226416951170011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2139257169207557072906725 401110719226416951170011)
                    ·
                      rfl

theorem cell23_2343481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 4].length) (baseStart_2343481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343481 prefixEnd_2343481 := by exact prefixLift 2343481
  have htrace : WordTrace (prefixWord ++ tailWord_2343481) baseStart_2343481 baseEnd_2343481 := by
    simpa [prefixWord, tailWord_2343481, baseEnd_2343481] using wordTrace_append hprefix tailTrace_2343481
  have hstable : (prefixWord ++ tailWord_2343481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343481).length < 2 ^ (prefixWord ++ tailWord_2343481).sum := by decide
  have hdescent : baseEnd_2343481 < baseStart_2343481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343488 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 3, 2, 2]
def baseStart_2343488 : Nat := 118140960795 + 2343488 * 2 ^ 59
def prefixEnd_2343488 : Nat := 4983230072969 + 3 ^ 40 * 2343488 * 2
def baseEnd_2343488 : Nat := 1203335752043832326122501

theorem tailTrace_2343488 : CollatzResearch.WordTrace tailWord_2343488 prefixEnd_2343488 1203335752043832326122501 := by
  unfold tailWord_2343488
  simp only [CollatzResearch.WordTrace]
  refine ⟨42737014666975343365551559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56982686222633791154068745 42737014666975343365551559)
  ·
    refine ⟨64105522000463015048327339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42737014666975343365551559 64105522000463015048327339)
    ·
      refine ⟨96158283000694522572491009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64105522000463015048327339 96158283000694522572491009)
      ·
        refine ⟨72118712250520891929368257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96158283000694522572491009 72118712250520891929368257)
        ·
          refine ⟨54089034187890668947026193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72118712250520891929368257 54089034187890668947026193)
          ·
            refine ⟨40566775640918001710269645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54089034187890668947026193 40566775640918001710269645)
            ·
              refine ⟨15212540865344250641351117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40566775640918001710269645 15212540865344250641351117)
              ·
                refine ⟨5704702824504093990506669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15212540865344250641351117 5704702824504093990506669)
                ·
                  refine ⟨2139263559189035246440001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5704702824504093990506669 2139263559189035246440001)
                  ·
                    refine ⟨1604447669391776434830001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139263559189035246440001 1604447669391776434830001)
                    ·
                      refine ⟨1203335752043832326122501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604447669391776434830001 1203335752043832326122501)
                      ·
                        rfl

theorem cell23_2343488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_2343488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343488 prefixEnd_2343488 := by exact prefixLift 2343488
  have htrace : WordTrace (prefixWord ++ tailWord_2343488) baseStart_2343488 baseEnd_2343488 := by
    simpa [prefixWord, tailWord_2343488, baseEnd_2343488] using wordTrace_append hprefix tailTrace_2343488
  have hstable : (prefixWord ++ tailWord_2343488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343488).length < 2 ^ (prefixWord ++ tailWord_2343488).sum := by decide
  have hdescent : baseEnd_2343488 < baseStart_2343488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343508 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_2343508 : Nat := 118140960795 + 2343508 * 2 ^ 59
def prefixEnd_2343508 : Nat := 4983230072969 + 3 ^ 40 * 2343508 * 2
def baseEnd_2343508 : Nat := 1203346021656922247872409

theorem tailTrace_2343508 : CollatzResearch.WordTrace tailWord_2343508 prefixEnd_2343508 1203346021656922247872409 := by
  unfold tailWord_2343508
  simp only [CollatzResearch.WordTrace]
  refine ⟨42737379396939115073415589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56983172529252153431220785 42737379396939115073415589)
  ·
    refine ⟨8013258636926084076265423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42737379396939115073415589 8013258636926084076265423)
    ·
      refine ⟨12019887955389126114398135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8013258636926084076265423 12019887955389126114398135)
      ·
        refine ⟨18029831933083689171597203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12019887955389126114398135 18029831933083689171597203)
        ·
          refine ⟨27044747899625533757395805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18029831933083689171597203 27044747899625533757395805)
          ·
            refine ⟨10141780462359575159023427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27044747899625533757395805 10141780462359575159023427)
            ·
              refine ⟨15212670693539362738535141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10141780462359575159023427 15212670693539362738535141)
              ·
                refine ⟨2852375755038630513475339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15212670693539362738535141 2852375755038630513475339)
                ·
                  refine ⟨4278563632557945770213009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2852375755038630513475339 4278563632557945770213009)
                  ·
                    refine ⟨3208922724418459327659757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4278563632557945770213009 3208922724418459327659757)
                    ·
                      refine ⟨1203346021656922247872409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3208922724418459327659757 1203346021656922247872409)
                      ·
                        rfl

theorem cell23_2343508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_2343508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343508 prefixEnd_2343508 := by exact prefixLift 2343508
  have htrace : WordTrace (prefixWord ++ tailWord_2343508) baseStart_2343508 baseEnd_2343508 := by
    simpa [prefixWord, tailWord_2343508, baseEnd_2343508] using wordTrace_append hprefix tailTrace_2343508
  have hstable : (prefixWord ++ tailWord_2343508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343508).length < 2 ^ (prefixWord ++ tailWord_2343508).sum := by decide
  have hdescent : baseEnd_2343508 < baseStart_2343508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343528 : List Nat := [2, 1, 4, 3, 3, 1, 9]
def baseStart_2343528 : Nat := 118140960795 + 2343528 * 2 ^ 59
def prefixEnd_2343528 : Nat := 4983230072969 + 3 ^ 40 * 2343528 * 2
def baseEnd_2343528 : Nat := 14856250509506323081757

theorem tailTrace_2343528 : CollatzResearch.WordTrace tailWord_2343528 prefixEnd_2343528 14856250509506323081757 := by
  unfold tailWord_2343528
  simp only [CollatzResearch.WordTrace]
  refine ⟨42737744126902886781279619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56983658835870515708372825 42737744126902886781279619)
  ·
    refine ⟨64106616190354330171919429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42737744126902886781279619 64106616190354330171919429)
    ·
      refine ⟨12019990535691436907234893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64106616190354330171919429 12019990535691436907234893)
      ·
        refine ⟨4507496450884288840213085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12019990535691436907234893 4507496450884288840213085)
        ·
          refine ⟨1690311169081608315079907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4507496450884288840213085 1690311169081608315079907)
          ·
            refine ⟨2535466753622412472619861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690311169081608315079907 2535466753622412472619861)
            ·
              refine ⟨14856250509506323081757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2535466753622412472619861 14856250509506323081757)
              ·
                rfl

theorem cell23_2343528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 9].length) (baseStart_2343528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343528 prefixEnd_2343528 := by exact prefixLift 2343528
  have htrace : WordTrace (prefixWord ++ tailWord_2343528) baseStart_2343528 baseEnd_2343528 := by
    simpa [prefixWord, tailWord_2343528, baseEnd_2343528] using wordTrace_append hprefix tailTrace_2343528
  have hstable : (prefixWord ++ tailWord_2343528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343528).length < 2 ^ (prefixWord ++ tailWord_2343528).sum := by decide
  have hdescent : baseEnd_2343528 < baseStart_2343528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343544 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2343544 : Nat := 118140960795 + 2343544 * 2 ^ 59
def prefixEnd_2343544 : Nat := 4983230072969 + 3 ^ 40 * 2343544 * 2
def baseEnd_2343544 : Nat := 1203364506960484107022243

theorem tailTrace_2343544 : CollatzResearch.WordTrace tailWord_2343544 prefixEnd_2343544 1203364506960484107022243 := by
  unfold tailWord_2343544
  simp only [CollatzResearch.WordTrace]
  refine ⟨42738035910873904147570843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56984047881165205530094457 42738035910873904147570843)
  ·
    refine ⟨64107053866310856221356265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42738035910873904147570843 64107053866310856221356265)
    ·
      refine ⟨48080290399733142166017199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64107053866310856221356265 48080290399733142166017199)
      ·
        refine ⟨72120435599599713249025799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48080290399733142166017199 72120435599599713249025799)
        ·
          refine ⟨108180653399399569873538699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72120435599599713249025799 108180653399399569873538699)
          ·
            refine ⟨162270980099099354810308049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108180653399399569873538699 162270980099099354810308049)
            ·
              refine ⟨121703235074324516107731037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162270980099099354810308049 121703235074324516107731037)
              ·
                refine ⟨45638713152871693540399139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121703235074324516107731037 45638713152871693540399139)
                ·
                  refine ⟨68458069729307540310598709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45638713152871693540399139 68458069729307540310598709)
                  ·
                    refine ⟨6417944037122581904118629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68458069729307540310598709 6417944037122581904118629)
                    ·
                      refine ⟨1203364506960484107022243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6417944037122581904118629 1203364506960484107022243)
                      ·
                        rfl

theorem cell23_2343544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2343544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343544 prefixEnd_2343544 := by exact prefixLift 2343544
  have htrace : WordTrace (prefixWord ++ tailWord_2343544) baseStart_2343544 baseEnd_2343544 := by
    simpa [prefixWord, tailWord_2343544, baseEnd_2343544] using wordTrace_append hprefix tailTrace_2343544
  have hstable : (prefixWord ++ tailWord_2343544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343544).length < 2 ^ (prefixWord ++ tailWord_2343544).sum := by decide
  have hdescent : baseEnd_2343544 < baseStart_2343544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343555 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 2, 1, 3]
def baseStart_2343555 : Nat := 118140960795 + 2343555 * 2 ^ 59
def prefixEnd_2343555 : Nat := 4983230072969 + 3 ^ 40 * 2343555 * 2
def baseEnd_2343555 : Nat := 1203370155247683563984693

theorem tailTrace_2343555 : CollatzResearch.WordTrace tailWord_2343555 prefixEnd_2343555 1203370155247683563984693 := by
  unfold tailWord_2343555
  simp only [CollatzResearch.WordTrace]
  refine ⟨85476473024707957173792119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56984315349805304782528079 85476473024707957173792119)
  ·
    refine ⟨128214709537061935760688179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85476473024707957173792119 128214709537061935760688179)
    ·
      refine ⟨192322064305592903641032269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128214709537061935760688179 192322064305592903641032269)
      ·
        refine ⟨72120774114597338865387101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192322064305592903641032269 72120774114597338865387101)
        ·
          refine ⟨27045290292974002074520163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72120774114597338865387101 27045290292974002074520163)
          ·
            refine ⟨40567935439461003111780245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27045290292974002074520163 40567935439461003111780245)
            ·
              refine ⟨1901621973724734520864699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40567935439461003111780245 1901621973724734520864699)
              ·
                refine ⟨2852432960587101781297049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901621973724734520864699 2852432960587101781297049)
                ·
                  refine ⟨2139324720440326335972787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2852432960587101781297049 2139324720440326335972787)
                  ·
                    refine ⟨3208987080660489503959181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2139324720440326335972787 3208987080660489503959181)
                    ·
                      refine ⟨1203370155247683563984693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3208987080660489503959181 1203370155247683563984693)
                      ·
                        rfl

theorem cell23_2343555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_2343555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343555 prefixEnd_2343555 := by exact prefixLift 2343555
  have htrace : WordTrace (prefixWord ++ tailWord_2343555) baseStart_2343555 baseEnd_2343555 := by
    simpa [prefixWord, tailWord_2343555, baseEnd_2343555] using wordTrace_append hprefix tailTrace_2343555
  have hstable : (prefixWord ++ tailWord_2343555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343555).length < 2 ^ (prefixWord ++ tailWord_2343555).sum := by decide
  have hdescent : baseEnd_2343555 < baseStart_2343555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343581 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2343581 : Nat := 118140960795 + 2343581 * 2 ^ 59
def prefixEnd_2343581 : Nat := 4983230072969 + 3 ^ 40 * 2343581 * 2
def baseEnd_2343581 : Nat := 1203383505744700462259573

theorem tailTrace_2343581 : CollatzResearch.WordTrace tailWord_2343581 prefixEnd_2343581 1203383505744700462259573 := by
  unfold tailWord_2343581
  simp only [CollatzResearch.WordTrace]
  refine ⟨85477421322613763614238597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56984947548409175742825731 85477421322613763614238597)
  ·
    refine ⟨16027016497990080677669737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85477421322613763614238597 16027016497990080677669737)
    ·
      refine ⟨12020262373492560508252303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16027016497990080677669737 12020262373492560508252303)
      ·
        refine ⟨18030393560238840762378455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12020262373492560508252303 18030393560238840762378455)
        ·
          refine ⟨27045590340358261143567683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18030393560238840762378455 27045590340358261143567683)
          ·
            refine ⟨40568385510537391715351525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27045590340358261143567683 40568385510537391715351525)
            ·
              refine ⟨7606572283225760946628411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40568385510537391715351525 7606572283225760946628411)
              ·
                refine ⟨11409858424838641419942617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7606572283225760946628411 11409858424838641419942617)
                ·
                  refine ⟨8557393818628981064956963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11409858424838641419942617 8557393818628981064956963)
                  ·
                    refine ⟨12836090727943471597435445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8557393818628981064956963 12836090727943471597435445)
                    ·
                      refine ⟨1203383505744700462259573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12836090727943471597435445 1203383505744700462259573)
                      ·
                        rfl

theorem cell23_2343581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2343581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343581 prefixEnd_2343581 := by exact prefixLift 2343581
  have htrace : WordTrace (prefixWord ++ tailWord_2343581) baseStart_2343581 baseEnd_2343581 := by
    simpa [prefixWord, tailWord_2343581, baseEnd_2343581] using wordTrace_append hprefix tailTrace_2343581
  have hstable : (prefixWord ++ tailWord_2343581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343581).length < 2 ^ (prefixWord ++ tailWord_2343581).sum := by decide
  have hdescent : baseEnd_2343581 < baseStart_2343581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343681 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2343681 : Nat := 118140960795 + 2343681 * 2 ^ 59
def prefixEnd_2343681 : Nat := 4983230072969 + 3 ^ 40 * 2343681 * 2
def baseEnd_2343681 : Nat := 1203434853810150071009113

theorem tailTrace_2343681 : CollatzResearch.WordTrace tailWord_2343681 prefixEnd_2343681 1203434853810150071009113 := by
  unfold tailWord_2343681
  simp only [CollatzResearch.WordTrace]
  refine ⟨85481068622251480692878897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56987379081500987128585931 85481068622251480692878897)
  ·
    refine ⟨64110801466688610519659173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85481068622251480692878897 64110801466688610519659173)
    ·
      refine ⟨12020775275004114472436095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64110801466688610519659173 12020775275004114472436095)
      ·
        refine ⟨18031162912506171708654143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12020775275004114472436095 18031162912506171708654143)
        ·
          refine ⟨27046744368759257562981215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18031162912506171708654143 27046744368759257562981215)
          ·
            refine ⟨40570116553138886344471823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27046744368759257562981215 40570116553138886344471823)
            ·
              refine ⟨60855174829708329516707735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40570116553138886344471823 60855174829708329516707735)
              ·
                refine ⟨91282762244562494275061603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60855174829708329516707735 91282762244562494275061603)
                ·
                  refine ⟨136924143366843741412592405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91282762244562494275061603 136924143366843741412592405)
                  ·
                    refine ⟨6418319220320800378715269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136924143366843741412592405 6418319220320800378715269)
                    ·
                      refine ⟨1203434853810150071009113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6418319220320800378715269 1203434853810150071009113)
                      ·
                        rfl

theorem cell23_2343681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2343681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343681 prefixEnd_2343681 := by exact prefixLift 2343681
  have htrace : WordTrace (prefixWord ++ tailWord_2343681) baseStart_2343681 baseEnd_2343681 := by
    simpa [prefixWord, tailWord_2343681, baseEnd_2343681] using wordTrace_append hprefix tailTrace_2343681
  have hstable : (prefixWord ++ tailWord_2343681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343681).length < 2 ^ (prefixWord ++ tailWord_2343681).sum := by decide
  have hdescent : baseEnd_2343681 < baseStart_2343681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343688 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_2343688 : Nat := 118140960795 + 2343688 * 2 ^ 59
def prefixEnd_2343688 : Nat := 4983230072969 + 3 ^ 40 * 2343688 * 2
def baseEnd_2343688 : Nat := 1203438448174731543621581

theorem tailTrace_2343688 : CollatzResearch.WordTrace tailWord_2343688 prefixEnd_2343688 1203438448174731543621581 := by
  unfold tailWord_2343688
  simp only [CollatzResearch.WordTrace]
  refine ⟨42740661966613060444191859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56987549288817413925589145 42740661966613060444191859)
  ·
    refine ⟨64110992949919590666287789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42740661966613060444191859 64110992949919590666287789)
    ·
      refine ⟨24041622356219846499857921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64110992949919590666287789 24041622356219846499857921)
      ·
        refine ⟨18031216767164884874893441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24041622356219846499857921 18031216767164884874893441)
        ·
          refine ⟨13523412575373663656170081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18031216767164884874893441 13523412575373663656170081)
          ·
            refine ⟨10142559431530247742127561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13523412575373663656170081 10142559431530247742127561)
            ·
              refine ⟨7606919573647685806595671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10142559431530247742127561 7606919573647685806595671)
              ·
                refine ⟨11410379360471528709893507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7606919573647685806595671 11410379360471528709893507)
                ·
                  refine ⟨17115569040707293064840261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11410379360471528709893507 17115569040707293064840261)
                  ·
                    refine ⟨3209169195132617449657549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17115569040707293064840261 3209169195132617449657549)
                    ·
                      refine ⟨1203438448174731543621581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3209169195132617449657549 1203438448174731543621581)
                      ·
                        rfl

theorem cell23_2343688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_2343688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343688 prefixEnd_2343688 := by exact prefixLift 2343688
  have htrace : WordTrace (prefixWord ++ tailWord_2343688) baseStart_2343688 baseEnd_2343688 := by
    simpa [prefixWord, tailWord_2343688, baseEnd_2343688] using wordTrace_append hprefix tailTrace_2343688
  have hstable : (prefixWord ++ tailWord_2343688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343688).length < 2 ^ (prefixWord ++ tailWord_2343688).sum := by decide
  have hdescent : baseEnd_2343688 < baseStart_2343688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343721 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 5, 5]
def baseStart_2343721 : Nat := 118140960795 + 2343721 * 2 ^ 59
def prefixEnd_2343721 : Nat := 4983230072969 + 3 ^ 40 * 2343721 * 2
def baseEnd_2343721 : Nat := 401151797678776638169643

theorem tailTrace_2343721 : CollatzResearch.WordTrace tailWord_2343721 prefixEnd_2343721 401151797678776638169643 := by
  unfold tailWord_2343721
  simp only [CollatzResearch.WordTrace]
  refine ⟨85482527542106567524335017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56988351694737711682890011 85482527542106567524335017)
  ·
    refine ⟨64111895656579925643251263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85482527542106567524335017 64111895656579925643251263)
    ·
      refine ⟨96167843484869888464876895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64111895656579925643251263 96167843484869888464876895)
      ·
        refine ⟨144251765227304832697315343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96167843484869888464876895 144251765227304832697315343)
        ·
          refine ⟨216377647840957249045973015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144251765227304832697315343 216377647840957249045973015)
          ·
            refine ⟨324566471761435873568959523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216377647840957249045973015 324566471761435873568959523)
            ·
              refine ⟨486849707642153810353439285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324566471761435873568959523 486849707642153810353439285)
              ·
                refine ⟨45642160091451919720634933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 486849707642153810353439285 45642160091451919720634933)
                ·
                  refine ⟨4278952508573617473809525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45642160091451919720634933 4278952508573617473809525)
                  ·
                    refine ⟨401151797678776638169643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4278952508573617473809525 401151797678776638169643)
                    ·
                      rfl

theorem cell23_2343721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_2343721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343721 prefixEnd_2343721 := by exact prefixLift 2343721
  have htrace : WordTrace (prefixWord ++ tailWord_2343721) baseStart_2343721 baseEnd_2343721 := by
    simpa [prefixWord, tailWord_2343721, baseEnd_2343721] using wordTrace_append hprefix tailTrace_2343721
  have hstable : (prefixWord ++ tailWord_2343721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343721).length < 2 ^ (prefixWord ++ tailWord_2343721).sum := by decide
  have hdescent : baseEnd_2343721 < baseStart_2343721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343728 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 3, 5, 2]
def baseStart_2343728 : Nat := 118140960795 + 2343728 * 2 ^ 59
def prefixEnd_2343728 : Nat := 4983230072969 + 3 ^ 40 * 2343728 * 2
def baseEnd_2343728 : Nat := 1203458987400911387121397

theorem tailTrace_2343728 : CollatzResearch.WordTrace tailWord_2343728 prefixEnd_2343728 1203458987400911387121397 := by
  unfold tailWord_2343728
  simp only [CollatzResearch.WordTrace]
  refine ⟨42741391426540603859919919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56988521902054138479893225 42741391426540603859919919)
  ·
    refine ⟨64112087139810905789879879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42741391426540603859919919 64112087139810905789879879)
    ·
      refine ⟨96168130709716358684819819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64112087139810905789879879 96168130709716358684819819)
      ·
        refine ⟨144252196064574538027229729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96168130709716358684819819 144252196064574538027229729)
        ·
          refine ⟨108189147048430903520422297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144252196064574538027229729 108189147048430903520422297)
          ·
            refine ⟨81141860286323177640316723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108189147048430903520422297 81141860286323177640316723)
            ·
              refine ⟨121712790429484766460475085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81141860286323177640316723 121712790429484766460475085)
              ·
                refine ⟨45642296411056787422678157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121712790429484766460475085 45642296411056787422678157)
                ·
                  refine ⟨17115861154146295283504309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45642296411056787422678157 17115861154146295283504309)
                  ·
                    refine ⟨1604611983201215182828529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17115861154146295283504309 1604611983201215182828529)
                    ·
                      refine ⟨1203458987400911387121397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604611983201215182828529 1203458987400911387121397)
                      ·
                        rfl

theorem cell23_2343728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 5, 2].length) (baseStart_2343728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343728 prefixEnd_2343728 := by exact prefixLift 2343728
  have htrace : WordTrace (prefixWord ++ tailWord_2343728) baseStart_2343728 baseEnd_2343728 := by
    simpa [prefixWord, tailWord_2343728, baseEnd_2343728] using wordTrace_append hprefix tailTrace_2343728
  have hstable : (prefixWord ++ tailWord_2343728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343728).length < 2 ^ (prefixWord ++ tailWord_2343728).sum := by decide
  have hdescent : baseEnd_2343728 < baseStart_2343728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343752 : List Nat := [2, 1, 3, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_2343752 : Nat := 118140960795 + 2343752 * 2 ^ 59
def prefixEnd_2343752 : Nat := 4983230072969 + 3 ^ 40 * 2343752 * 2
def baseEnd_2343752 : Nat := 1203471310936619293221287

theorem tailTrace_2343752 : CollatzResearch.WordTrace tailWord_2343752 prefixEnd_2343752 1203471310936619293221287 := by
  unfold tailWord_2343752
  simp only [CollatzResearch.WordTrace]
  refine ⟨42741829102497129909356755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56989105469996173212475673 42741829102497129909356755)
  ·
    refine ⟨64112743653745694864035133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42741829102497129909356755 64112743653745694864035133)
    ·
      refine ⟨24042278870154635574013175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64112743653745694864035133 24042278870154635574013175)
      ·
        refine ⟨36063418305231953361019763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24042278870154635574013175 36063418305231953361019763)
        ·
          refine ⟨54095127457847930041529645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36063418305231953361019763 54095127457847930041529645)
          ·
            refine ⟨20285672796692973765573617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54095127457847930041529645 20285672796692973765573617)
            ·
              refine ⟨15214254597519730324180213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20285672796692973765573617 15214254597519730324180213)
              ·
                refine ⟨1426336368517474717891895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15214254597519730324180213 1426336368517474717891895)
                ·
                  refine ⟨2139504552776212076837843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426336368517474717891895 2139504552776212076837843)
                  ·
                    refine ⟨3209256829164318115256765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2139504552776212076837843 3209256829164318115256765)
                    ·
                      refine ⟨1203471310936619293221287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3209256829164318115256765 1203471310936619293221287)
                      ·
                        rfl

theorem cell23_2343752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_2343752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343752 prefixEnd_2343752 := by exact prefixLift 2343752
  have htrace : WordTrace (prefixWord ++ tailWord_2343752) baseStart_2343752 baseEnd_2343752 := by
    simpa [prefixWord, tailWord_2343752, baseEnd_2343752] using wordTrace_append hprefix tailTrace_2343752
  have hstable : (prefixWord ++ tailWord_2343752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343752).length < 2 ^ (prefixWord ++ tailWord_2343752).sum := by decide
  have hdescent : baseEnd_2343752 < baseStart_2343752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343768 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 4, 4]
def baseStart_2343768 : Nat := 118140960795 + 2343768 * 2 ^ 59
def prefixEnd_2343768 : Nat := 4983230072969 + 3 ^ 40 * 2343768 * 2
def baseEnd_2343768 : Nat := 401159842209030410207071

theorem tailTrace_2343768 : CollatzResearch.WordTrace tailWord_2343768 prefixEnd_2343768 401159842209030410207071 := by
  unfold tailWord_2343768
  simp only [CollatzResearch.WordTrace]
  refine ⟨42742120886468147275647979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56989494515290863034197305 42742120886468147275647979)
  ·
    refine ⟨64113181329702220913471969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42742120886468147275647979 64113181329702220913471969)
    ·
      refine ⟨48084885997276665685103977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64113181329702220913471969 48084885997276665685103977)
      ·
        refine ⟨36063664497957499263827983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48084885997276665685103977 36063664497957499263827983)
        ·
          refine ⟨54095496746936248895741975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36063664497957499263827983 54095496746936248895741975)
          ·
            refine ⟨81143245120404373343612963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54095496746936248895741975 81143245120404373343612963)
            ·
              refine ⟨121714867680606560015419445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81143245120404373343612963 121714867680606560015419445)
              ·
                refine ⟨11410768845056865001445573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121714867680606560015419445 11410768845056865001445573)
                ·
                  refine ⟨2139519158448162187771045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11410768845056865001445573 2139519158448162187771045)
                  ·
                    refine ⟨401159842209030410207071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2139519158448162187771045 401159842209030410207071)
                    ·
                      rfl

theorem cell23_2343768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_2343768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343768 prefixEnd_2343768 := by exact prefixLift 2343768
  have htrace : WordTrace (prefixWord ++ tailWord_2343768) baseStart_2343768 baseEnd_2343768 := by
    simpa [prefixWord, tailWord_2343768, baseEnd_2343768] using wordTrace_append hprefix tailTrace_2343768
  have hstable : (prefixWord ++ tailWord_2343768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343768).length < 2 ^ (prefixWord ++ tailWord_2343768).sum := by decide
  have hdescent : baseEnd_2343768 < baseStart_2343768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343769 : List Nat := [1, 2, 1, 2, 2, 4, 4, 2, 1, 1, 3]
def baseStart_2343769 : Nat := 118140960795 + 2343769 * 2 ^ 59
def prefixEnd_2343769 : Nat := 4983230072969 + 3 ^ 40 * 2343769 * 2
def baseEnd_2343769 : Nat := 1203480040107745726708709

theorem tailTrace_2343769 : CollatzResearch.WordTrace tailWord_2343769 prefixEnd_2343769 1203480040107745726708709 := by
  unfold tailWord_2343769
  simp only [CollatzResearch.WordTrace]
  refine ⟨85484278245932671722082361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56989518830621781148054907 85484278245932671722082361)
  ·
    refine ⟨64113208684449503791561771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85484278245932671722082361 64113208684449503791561771)
    ·
      refine ⟨96169813026674255687342657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64113208684449503791561771 96169813026674255687342657)
      ·
        refine ⟨72127359770005691765506993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96169813026674255687342657 72127359770005691765506993)
        ·
          refine ⟨54095519827504268824130245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72127359770005691765506993 54095519827504268824130245)
          ·
            refine ⟨10142909967657050404524421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54095519827504268824130245 10142909967657050404524421)
            ·
              refine ⟨1901795618935696950848329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10142909967657050404524421 1901795618935696950848329)
              ·
                refine ⟨1426346714201772713136247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901795618935696950848329 1426346714201772713136247)
                ·
                  refine ⟨2139520071302659069704371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426346714201772713136247 2139520071302659069704371)
                  ·
                    refine ⟨3209280106953988604556557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2139520071302659069704371 3209280106953988604556557)
                    ·
                      refine ⟨1203480040107745726708709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3209280106953988604556557 1203480040107745726708709)
                      ·
                        rfl

theorem cell23_2343769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_2343769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343769 prefixEnd_2343769 := by exact prefixLift 2343769
  have htrace : WordTrace (prefixWord ++ tailWord_2343769) baseStart_2343769 baseEnd_2343769 := by
    simpa [prefixWord, tailWord_2343769, baseEnd_2343769] using wordTrace_append hprefix tailTrace_2343769
  have hstable : (prefixWord ++ tailWord_2343769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343769).length < 2 ^ (prefixWord ++ tailWord_2343769).sum := by decide
  have hdescent : baseEnd_2343769 < baseStart_2343769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343791 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_2343791 : Nat := 118140960795 + 2343791 * 2 ^ 59
def prefixEnd_2343791 : Nat := 4983230072969 + 3 ^ 40 * 2343791 * 2
def baseEnd_2343791 : Nat := 1203491336682144640633607

theorem tailTrace_2343791 : CollatzResearch.WordTrace tailWord_2343791 prefixEnd_2343791 1203491336682144640633607 := by
  unfold tailWord_2343791
  simp only [CollatzResearch.WordTrace]
  refine ⟨85485080651852969479383227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56990053767901979652922151 85485080651852969479383227)
  ·
    refine ⟨128227620977779454219074841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85485080651852969479383227 128227620977779454219074841)
    ·
      refine ⟨96170715733334590664306131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128227620977779454219074841 96170715733334590664306131)
      ·
        refine ⟨144256073600001885996459197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96170715733334590664306131 144256073600001885996459197)
        ·
          refine ⟨54096027600000707248672199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144256073600001885996459197 54096027600000707248672199)
          ·
            refine ⟨81144041400001060873008299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54096027600000707248672199 81144041400001060873008299)
            ·
              refine ⟨121716062100001591309512449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81144041400001060873008299 121716062100001591309512449)
              ·
                refine ⟨91287046575001193482134337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121716062100001591309512449 91287046575001193482134337)
                ·
                  refine ⟨68465284931250895111600753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91287046575001193482134337 68465284931250895111600753)
                  ·
                    refine ⟨51348963698438171333700565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68465284931250895111600753 51348963698438171333700565)
                    ·
                      refine ⟨1203491336682144640633607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51348963698438171333700565 1203491336682144640633607)
                      ·
                        rfl

theorem cell23_2343791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_2343791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343791 prefixEnd_2343791 := by exact prefixLift 2343791
  have htrace : WordTrace (prefixWord ++ tailWord_2343791) baseStart_2343791 baseEnd_2343791 := by
    simpa [prefixWord, tailWord_2343791, baseEnd_2343791] using wordTrace_append hprefix tailTrace_2343791
  have hstable : (prefixWord ++ tailWord_2343791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343791).length < 2 ^ (prefixWord ++ tailWord_2343791).sum := by decide
  have hdescent : baseEnd_2343791 < baseStart_2343791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343806 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2343806 : Nat := 118140960795 + 2343806 * 2 ^ 59
def prefixEnd_2343806 : Nat := 4983230072969 + 3 ^ 40 * 2343806 * 2
def baseEnd_2343806 : Nat := 401166346297320693982013

theorem tailTrace_2343806 : CollatzResearch.WordTrace tailWord_2343806 prefixEnd_2343806 401166346297320693982013 := by
  unfold tailWord_2343806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10685703468349828380147409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56990418497865751360786181 10685703468349828380147409)
  ·
    refine ⟨8014277601262371285110557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10685703468349828380147409 8014277601262371285110557)
    ·
      refine ⟨3005354100473389231916459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8014277601262371285110557 3005354100473389231916459)
      ·
        refine ⟨4508031150710083847874689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005354100473389231916459 4508031150710083847874689)
        ·
          refine ⟨3381023363032562885906017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4508031150710083847874689 3381023363032562885906017)
          ·
            refine ⟨2535767522274422164429513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3381023363032562885906017 2535767522274422164429513)
            ·
              refine ⟨1901825641705816623322135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535767522274422164429513 1901825641705816623322135)
              ·
                refine ⟨2852738462558724934983203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901825641705816623322135 2852738462558724934983203)
                ·
                  refine ⟨4279107693838087402474805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2852738462558724934983203 4279107693838087402474805)
                  ·
                    refine ⟨401166346297320693982013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4279107693838087402474805 401166346297320693982013)
                    ·
                      rfl

theorem cell23_2343806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2343806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343806 prefixEnd_2343806 := by exact prefixLift 2343806
  have htrace : WordTrace (prefixWord ++ tailWord_2343806) baseStart_2343806 baseEnd_2343806 := by
    simpa [prefixWord, tailWord_2343806, baseEnd_2343806] using wordTrace_append hprefix tailTrace_2343806
  have hstable : (prefixWord ++ tailWord_2343806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343806).length < 2 ^ (prefixWord ++ tailWord_2343806).sum := by decide
  have hdescent : baseEnd_2343806 < baseStart_2343806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343808 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3]
def baseStart_2343808 : Nat := 118140960795 + 2343808 * 2 ^ 59
def prefixEnd_2343808 : Nat := 4983230072969 + 3 ^ 40 * 2343808 * 2
def baseEnd_2343808 : Nat := 1203500065853271074121029

theorem tailTrace_2343808 : CollatzResearch.WordTrace tailWord_2343808 prefixEnd_2343808 1203500065853271074121029 := by
  unfold tailWord_2343808
  simp only [CollatzResearch.WordTrace]
  refine ⟨42742850346395690691376039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56990467128527587588501385 42742850346395690691376039)
  ·
    refine ⟨64114275519593536037064059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42742850346395690691376039 64114275519593536037064059)
    ·
      refine ⟨96171413279390304055596089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64114275519593536037064059 96171413279390304055596089)
      ·
        refine ⟨72128559959542728041697067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96171413279390304055596089 72128559959542728041697067)
        ·
          refine ⟨108192839939314092062545601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72128559959542728041697067 108192839939314092062545601)
          ·
            refine ⟨81144629954485569046909201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108192839939314092062545601 81144629954485569046909201)
            ·
              refine ⟨60858472465864176785181901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81144629954485569046909201 60858472465864176785181901)
              ·
                refine ⟨22821927174699066294443213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60858472465864176785181901 22821927174699066294443213)
                ·
                  refine ⟨8558222690512149860416205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22821927174699066294443213 8558222690512149860416205)
                  ·
                    refine ⟨3209333508942056197656077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8558222690512149860416205 3209333508942056197656077)
                    ·
                      refine ⟨1203500065853271074121029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3209333508942056197656077 1203500065853271074121029)
                      ·
                        rfl

theorem cell23_2343808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_2343808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343808 prefixEnd_2343808 := by exact prefixLift 2343808
  have htrace : WordTrace (prefixWord ++ tailWord_2343808) baseStart_2343808 baseEnd_2343808 := by
    simpa [prefixWord, tailWord_2343808, baseEnd_2343808] using wordTrace_append hprefix tailTrace_2343808
  have hstable : (prefixWord ++ tailWord_2343808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343808).length < 2 ^ (prefixWord ++ tailWord_2343808).sum := by decide
  have hdescent : baseEnd_2343808 < baseStart_2343808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343826 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_2343826 : Nat := 118140960795 + 2343826 * 2 ^ 59
def prefixEnd_2343826 : Nat := 4983230072969 + 3 ^ 40 * 2343826 * 2
def baseEnd_2343826 : Nat := 1203509308505052003695947

theorem tailTrace_2343826 : CollatzResearch.WordTrace tailWord_2343826 prefixEnd_2343826 1203509308505052003695947 := by
  unfold tailWord_2343826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21371589301681542614226833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56990904804484113637938221 21371589301681542614226833)
  ·
    refine ⟨16028691976261156960670125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21371589301681542614226833 16028691976261156960670125)
    ·
      refine ⟨6010759491097933860251297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16028691976261156960670125 6010759491097933860251297)
      ·
        refine ⟨4508069618323450395188473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6010759491097933860251297 4508069618323450395188473)
        ·
          refine ⟨3381052213742587796391355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4508069618323450395188473 3381052213742587796391355)
          ·
            refine ⟨5071578320613881694587033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381052213742587796391355 5071578320613881694587033)
            ·
              refine ⟨3803683740460411270940275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5071578320613881694587033 3803683740460411270940275)
              ·
                refine ⟨5705525610690616906410413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803683740460411270940275 5705525610690616906410413)
                ·
                  refine ⟨2139572104008981339903905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5705525610690616906410413 2139572104008981339903905)
                  ·
                    refine ⟨1604679078006736004927929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139572104008981339903905 1604679078006736004927929)
                    ·
                      refine ⟨1203509308505052003695947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604679078006736004927929 1203509308505052003695947)
                      ·
                        rfl

theorem cell23_2343826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_2343826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343826 prefixEnd_2343826 := by exact prefixLift 2343826
  have htrace : WordTrace (prefixWord ++ tailWord_2343826) baseStart_2343826 baseEnd_2343826 := by
    simpa [prefixWord, tailWord_2343826, baseEnd_2343826] using wordTrace_append hprefix tailTrace_2343826
  have hstable : (prefixWord ++ tailWord_2343826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343826).length < 2 ^ (prefixWord ++ tailWord_2343826).sum := by decide
  have hdescent : baseEnd_2343826 < baseStart_2343826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343842 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2343842 : Nat := 118140960795 + 2343842 * 2 ^ 59
def prefixEnd_2343842 : Nat := 4983230072969 + 3 ^ 40 * 2343842 * 2
def baseEnd_2343842 : Nat := 1203517524195523941095873

theorem tailTrace_2343842 : CollatzResearch.WordTrace tailWord_2343842 prefixEnd_2343842 1203517524195523941095873 := by
  unfold tailWord_2343842
  simp only [CollatzResearch.WordTrace]
  refine ⟨21371735193667051297372445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56991293849778803459659853 21371735193667051297372445)
  ·
    refine ⟨8014400697625144236514667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21371735193667051297372445 8014400697625144236514667)
    ·
      refine ⟨12021601046437716354772001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8014400697625144236514667 12021601046437716354772001)
      ·
        refine ⟨9016200784828287266079001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12021601046437716354772001 9016200784828287266079001)
        ·
          refine ⟨6762150588621215449559251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9016200784828287266079001 6762150588621215449559251)
          ·
            refine ⟨10143225882931823174338877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6762150588621215449559251 10143225882931823174338877)
            ·
              refine ⟨3803709706099433690377079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10143225882931823174338877 3803709706099433690377079)
              ·
                refine ⟨5705564559149150535565619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803709706099433690377079 5705564559149150535565619)
                ·
                  refine ⟨8558346838723725803348429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5705564559149150535565619 8558346838723725803348429)
                  ·
                    refine ⟨3209380064521397176255661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8558346838723725803348429 3209380064521397176255661)
                    ·
                      refine ⟨1203517524195523941095873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3209380064521397176255661 1203517524195523941095873)
                      ·
                        rfl

theorem cell23_2343842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2343842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343842 prefixEnd_2343842 := by exact prefixLift 2343842
  have htrace : WordTrace (prefixWord ++ tailWord_2343842) baseStart_2343842 baseEnd_2343842 := by
    simpa [prefixWord, tailWord_2343842, baseEnd_2343842] using wordTrace_append hprefix tailTrace_2343842
  have hstable : (prefixWord ++ tailWord_2343842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343842).length < 2 ^ (prefixWord ++ tailWord_2343842).sum := by decide
  have hdescent : baseEnd_2343842 < baseStart_2343842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343860 : List Nat := [2, 5, 2, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_2343860 : Nat := 118140960795 + 2343860 * 2 ^ 59
def prefixEnd_2343860 : Nat := 4983230072969 + 3 ^ 40 * 2343860 * 2
def baseEnd_2343860 : Nat := 1203526766847304870670791

theorem tailTrace_2343860 : CollatzResearch.WordTrace tailWord_2343860 prefixEnd_2343860 1203526766847304870670791 := by
  unfold tailWord_2343860
  simp only [CollatzResearch.WordTrace]
  refine ⟨42743798644301497131822517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56991731525735329509096689 42743798644301497131822517)
  ·
    refine ⟨4007231122903265356108361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42743798644301497131822517 4007231122903265356108361)
    ·
      refine ⟨3005423342177449017081271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4007231122903265356108361 3005423342177449017081271)
      ·
        refine ⟨4508135013266173525621907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005423342177449017081271 4508135013266173525621907)
        ·
          refine ⟨6762202519899260288432861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508135013266173525621907 6762202519899260288432861)
          ·
            refine ⟨2535825944962222608162323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6762202519899260288432861 2535825944962222608162323)
            ·
              refine ⟨3803738917443333912243485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535825944962222608162323 3803738917443333912243485)
              ·
                refine ⟨1426402094041250217091307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3803738917443333912243485 1426402094041250217091307)
                ·
                  refine ⟨2139603141061875325636961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426402094041250217091307 2139603141061875325636961)
                  ·
                    refine ⟨1604702355796406494227721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139603141061875325636961 1604702355796406494227721)
                    ·
                      refine ⟨1203526766847304870670791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604702355796406494227721 1203526766847304870670791)
                      ·
                        rfl

theorem cell23_2343860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_2343860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343860 prefixEnd_2343860 := by exact prefixLift 2343860
  have htrace : WordTrace (prefixWord ++ tailWord_2343860) baseStart_2343860 baseEnd_2343860 := by
    simpa [prefixWord, tailWord_2343860, baseEnd_2343860] using wordTrace_append hprefix tailTrace_2343860
  have hstable : (prefixWord ++ tailWord_2343860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343860).length < 2 ^ (prefixWord ++ tailWord_2343860).sum := by decide
  have hdescent : baseEnd_2343860 < baseStart_2343860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343893 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_2343893 : Nat := 118140960795 + 2343893 * 2 ^ 59
def prefixEnd_2343893 : Nat := 4983230072969 + 3 ^ 40 * 2343893 * 2
def baseEnd_2343893 : Nat := 1203543711708903241558139

theorem tailTrace_2343893 : CollatzResearch.WordTrace tailWord_2343893 prefixEnd_2343893 1203543711708903241558139 := by
  unfold tailWord_2343893
  simp only [CollatzResearch.WordTrace]
  refine ⟨85488800897483440899596333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56992533931655627266397555 85488800897483440899596333)
  ·
    refine ⟨32058300336556290337348625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85488800897483440899596333 32058300336556290337348625)
    ·
      refine ⟨24043725252417217753011469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32058300336556290337348625 24043725252417217753011469)
      ·
        refine ⟨9016396969656456657379301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24043725252417217753011469 9016396969656456657379301)
        ·
          refine ⟨1690574431810585623258619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9016396969656456657379301 1690574431810585623258619)
          ·
            refine ⟨2535861647715878434887929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690574431810585623258619 2535861647715878434887929)
            ·
              refine ⟨1901896235786908826165947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535861647715878434887929 1901896235786908826165947)
              ·
                refine ⟨2852844353680363239248921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901896235786908826165947 2852844353680363239248921)
                ·
                  refine ⟨2139633265260272429436691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2852844353680363239248921 2139633265260272429436691)
                  ·
                    refine ⟨3209449897890408644155037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2139633265260272429436691 3209449897890408644155037)
                    ·
                      refine ⟨1203543711708903241558139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3209449897890408644155037 1203543711708903241558139)
                      ·
                        rfl

theorem cell23_2343893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_2343893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343893 prefixEnd_2343893 := by exact prefixLift 2343893
  have htrace : WordTrace (prefixWord ++ tailWord_2343893) baseStart_2343893 baseEnd_2343893 := by
    simpa [prefixWord, tailWord_2343893, baseEnd_2343893] using wordTrace_append hprefix tailTrace_2343893
  have hstable : (prefixWord ++ tailWord_2343893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343893).length < 2 ^ (prefixWord ++ tailWord_2343893).sum := by decide
  have hdescent : baseEnd_2343893 < baseStart_2343893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343972 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2343972 : Nat := 118140960795 + 2343972 * 2 ^ 59
def prefixEnd_2343972 : Nat := 4983230072969 + 3 ^ 40 * 2343972 * 2
def baseEnd_2343972 : Nat := 1203584276680608432470275

theorem tailTrace_2343972 : CollatzResearch.WordTrace tailWord_2343972 prefixEnd_2343972 1203584276680608432470275 := by
  unfold tailWord_2343972
  simp only [CollatzResearch.WordTrace]
  refine ⟨42745841132098618695861085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56994454842798158261148113 42745841132098618695861085)
  ·
    refine ⟨16029690424536982010947907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42745841132098618695861085 16029690424536982010947907)
    ·
      refine ⟨24044535636805473016421861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16029690424536982010947907 24044535636805473016421861)
      ·
        refine ⟨4508350431901026190579099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24044535636805473016421861 4508350431901026190579099)
        ·
          refine ⟨6762525647851539285868649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508350431901026190579099 6762525647851539285868649)
          ·
            refine ⟨5071894235888654464401487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6762525647851539285868649 5071894235888654464401487)
            ·
              refine ⟨7607841353832981696602231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071894235888654464401487 7607841353832981696602231)
              ·
                refine ⟨11411762030749472544903347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7607841353832981696602231 11411762030749472544903347)
                ·
                  refine ⟨17117643046124208817355021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11411762030749472544903347 17117643046124208817355021)
                  ·
                    refine ⟨6419116142296578306508133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17117643046124208817355021 6419116142296578306508133)
                    ·
                      refine ⟨1203584276680608432470275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6419116142296578306508133 1203584276680608432470275)
                      ·
                        rfl

theorem cell23_2343972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2343972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343972 prefixEnd_2343972 := by exact prefixLift 2343972
  have htrace : WordTrace (prefixWord ++ tailWord_2343972) baseStart_2343972 baseEnd_2343972 := by
    simpa [prefixWord, tailWord_2343972, baseEnd_2343972] using wordTrace_append hprefix tailTrace_2343972
  have hstable : (prefixWord ++ tailWord_2343972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343972).length < 2 ^ (prefixWord ++ tailWord_2343972).sum := by decide
  have hdescent : baseEnd_2343972 < baseStart_2343972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343982 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2343982 : Nat := 118140960795 + 2343982 * 2 ^ 59
def prefixEnd_2343982 : Nat := 4983230072969 + 3 ^ 40 * 2343982 * 2
def baseEnd_2343982 : Nat := 401196470495717797781743

theorem tailTrace_2343982 : CollatzResearch.WordTrace tailWord_2343982 prefixEnd_2343982 401196470495717797781743 := by
  unfold tailWord_2343982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10686505874270126137448275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56994697996107339399724133 10686505874270126137448275)
  ·
    refine ⟨16029758811405189206172413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10686505874270126137448275 16029758811405189206172413)
    ·
      refine ⟨6011159554276945952314655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16029758811405189206172413 6011159554276945952314655)
      ·
        refine ⟨9016739331415418928471983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6011159554276945952314655 9016739331415418928471983)
        ·
          refine ⟨13525108997123128392707975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9016739331415418928471983 13525108997123128392707975)
          ·
            refine ⟨20287663495684692589061963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13525108997123128392707975 20287663495684692589061963)
            ·
              refine ⟨30431495243527038883592945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20287663495684692589061963 30431495243527038883592945)
              ·
                refine ⟨22823621432645279162694709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30431495243527038883592945 22823621432645279162694709)
                ·
                  refine ⟨2139714509310494921502629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22823621432645279162694709 2139714509310494921502629)
                  ·
                    refine ⟨401196470495717797781743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2139714509310494921502629 401196470495717797781743)
                    ·
                      rfl

theorem cell23_2343982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2343982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2343982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2343982 prefixEnd_2343982 := by exact prefixLift 2343982
  have htrace : WordTrace (prefixWord ++ tailWord_2343982) baseStart_2343982 baseEnd_2343982 := by
    simpa [prefixWord, tailWord_2343982, baseEnd_2343982] using wordTrace_append hprefix tailTrace_2343982
  have hstable : (prefixWord ++ tailWord_2343982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343982).length < 2 ^ (prefixWord ++ tailWord_2343982).sum := by decide
  have hdescent : baseEnd_2343982 < baseStart_2343982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344006 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_2344006 : Nat := 118140960795 + 2344006 * 2 ^ 59
def prefixEnd_2344006 : Nat := 4983230072969 + 3 ^ 40 * 2344006 * 2
def baseEnd_2344006 : Nat := 1203601735022861299445119

theorem tailTrace_2344006 : CollatzResearch.WordTrace tailWord_2344006 prefixEnd_2344006 1203601735022861299445119 := by
  unfold tailWord_2344006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671653823314814412451871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56995281564049374132306581 2671653823314814412451871)
  ·
    refine ⟨4007480734972221618677807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2671653823314814412451871 4007480734972221618677807)
    ·
      refine ⟨6011221102458332428016711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4007480734972221618677807 6011221102458332428016711)
      ·
        refine ⟨9016831653687498642025067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6011221102458332428016711 9016831653687498642025067)
        ·
          refine ⟨13525247480531247963037601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9016831653687498642025067 13525247480531247963037601)
          ·
            refine ⟨10143935610398435972278201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13525247480531247963037601 10143935610398435972278201)
            ·
              refine ⟨7607951707798826979208651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10143935610398435972278201 7607951707798826979208651)
              ·
                refine ⟨11411927561698240468812977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7607951707798826979208651 11411927561698240468812977)
                ·
                  refine ⟨8558945671273680351609733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11411927561698240468812977 8558945671273680351609733)
                  ·
                    refine ⟨1604802313363815065926825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8558945671273680351609733 1604802313363815065926825)
                    ·
                      refine ⟨1203601735022861299445119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604802313363815065926825 1203601735022861299445119)
                      ·
                        rfl

theorem cell23_2344006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_2344006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344006 prefixEnd_2344006 := by exact prefixLift 2344006
  have htrace : WordTrace (prefixWord ++ tailWord_2344006) baseStart_2344006 baseEnd_2344006 := by
    simpa [prefixWord, tailWord_2344006, baseEnd_2344006] using wordTrace_append hprefix tailTrace_2344006
  have hstable : (prefixWord ++ tailWord_2344006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344006).length < 2 ^ (prefixWord ++ tailWord_2344006).sum := by decide
  have hdescent : baseEnd_2344006 < baseStart_2344006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344032 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 1, 5, 2]
def baseStart_2344032 : Nat := 118140960795 + 2344032 * 2 ^ 59
def prefixEnd_2344032 : Nat := 4983230072969 + 3 ^ 40 * 2344032 * 2
def baseEnd_2344032 : Nat := 1203615085519878197719999

theorem tailTrace_2344032 : CollatzResearch.WordTrace tailWord_2344032 prefixEnd_2344032 1203615085519878197719999 := by
  unfold tailWord_2344032
  simp only [CollatzResearch.WordTrace]
  refine ⟨42746935321989933819453175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56995913762653245092604233 42746935321989933819453175)
  ·
    refine ⟨64120402982984900729179763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42746935321989933819453175 64120402982984900729179763)
    ·
      refine ⟨96180604474477351093769645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64120402982984900729179763 96180604474477351093769645)
      ·
        refine ⟨36067726677929006660163617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96180604474477351093769645 36067726677929006660163617)
        ·
          refine ⟨27050795008446754995122713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36067726677929006660163617 27050795008446754995122713)
          ·
            refine ⟨20288096256335066246342035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27050795008446754995122713 20288096256335066246342035)
            ·
              refine ⟨30432144384502599369513053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20288096256335066246342035 30432144384502599369513053)
              ·
                refine ⟨11412054144188474763567395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30432144384502599369513053 11412054144188474763567395)
                ·
                  refine ⟨17118081216282712145351093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11412054144188474763567395 17118081216282712145351093)
                  ·
                    refine ⟨1604820114026504263626665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17118081216282712145351093 1604820114026504263626665)
                    ·
                      refine ⟨1203615085519878197719999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604820114026504263626665 1203615085519878197719999)
                      ·
                        rfl

theorem cell23_2344032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_2344032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344032 prefixEnd_2344032 := by exact prefixLift 2344032
  have htrace : WordTrace (prefixWord ++ tailWord_2344032) baseStart_2344032 baseEnd_2344032 := by
    simpa [prefixWord, tailWord_2344032, baseEnd_2344032] using wordTrace_append hprefix tailTrace_2344032
  have hstable : (prefixWord ++ tailWord_2344032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344032).length < 2 ^ (prefixWord ++ tailWord_2344032).sum := by decide
  have hdescent : baseEnd_2344032 < baseStart_2344032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344075 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 4]
def baseStart_2344075 : Nat := 118140960795 + 2344075 * 2 ^ 59
def prefixEnd_2344075 : Nat := 4983230072969 + 3 ^ 40 * 2344075 * 2
def baseEnd_2344075 : Nat := 1203637165188021529482301

theorem tailTrace_2344075 : CollatzResearch.WordTrace tailWord_2344075 prefixEnd_2344075 1203637165188021529482301 := by
  unfold tailWord_2344075
  simp only [CollatzResearch.WordTrace]
  refine ⟨85495438982824085982721679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56996959321882723988481119 85495438982824085982721679)
  ·
    refine ⟨128243158474236128974082519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85495438982824085982721679 128243158474236128974082519)
    ·
      refine ⟨192364737711354193461123779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128243158474236128974082519 192364737711354193461123779)
      ·
        refine ⟨288547106567031290191685669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192364737711354193461123779 288547106567031290191685669)
        ·
          refine ⟨54102582481318366910941063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288547106567031290191685669 54102582481318366910941063)
          ·
            refine ⟨81153873721977550366411595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54102582481318366910941063 81153873721977550366411595)
            ·
              refine ⟨121730810582966325549617393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81153873721977550366411595 121730810582966325549617393)
              ·
                refine ⟨91298107937224744162213045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121730810582966325549617393 91298107937224744162213045)
                ·
                  refine ⟨8559197619114819765207473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91298107937224744162213045 8559197619114819765207473)
                  ·
                    refine ⟨6419398214336114823905605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8559197619114819765207473 6419398214336114823905605)
                    ·
                      refine ⟨1203637165188021529482301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6419398214336114823905605 1203637165188021529482301)
                      ·
                        rfl

theorem cell23_2344075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 4].length) (baseStart_2344075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344075 prefixEnd_2344075 := by exact prefixLift 2344075
  have htrace : WordTrace (prefixWord ++ tailWord_2344075) baseStart_2344075 baseEnd_2344075 := by
    simpa [prefixWord, tailWord_2344075, baseEnd_2344075] using wordTrace_append hprefix tailTrace_2344075
  have hstable : (prefixWord ++ tailWord_2344075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344075).length < 2 ^ (prefixWord ++ tailWord_2344075).sum := by decide
  have hdescent : baseEnd_2344075 < baseStart_2344075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344092 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2344092 : Nat := 118140960795 + 2344092 * 2 ^ 59
def prefixEnd_2344092 : Nat := 4983230072969 + 3 ^ 40 * 2344092 * 2
def baseEnd_2344092 : Nat := 1203645894359147962969723

theorem tailTrace_2344092 : CollatzResearch.WordTrace tailWord_2344092 prefixEnd_2344092 1203645894359147962969723 := by
  unfold tailWord_2344092
  simp only [CollatzResearch.WordTrace]
  refine ⟨42748029511881248943045265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56997372682508331924060353 42748029511881248943045265)
  ·
    refine ⟨32061022133910936707283949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42748029511881248943045265 32061022133910936707283949)
    ·
      refine ⟨12022883300216601265231481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32061022133910936707283949 12022883300216601265231481)
      ·
        refine ⟨9017162475162450948923611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12022883300216601265231481 9017162475162450948923611)
        ·
          refine ⟨13525743712743676423385417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9017162475162450948923611 13525743712743676423385417)
          ·
            refine ⟨10144307784557757317539063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13525743712743676423385417 10144307784557757317539063)
            ·
              refine ⟨15216461676836635976308595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10144307784557757317539063 15216461676836635976308595)
              ·
                refine ⟨22824692515254953964462893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15216461676836635976308595 22824692515254953964462893)
                ·
                  refine ⟨8559259693220607736673585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22824692515254953964462893 8559259693220607736673585)
                  ·
                    refine ⟨6419444769915455802505189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8559259693220607736673585 6419444769915455802505189)
                    ·
                      refine ⟨1203645894359147962969723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6419444769915455802505189 1203645894359147962969723)
                      ·
                        rfl

theorem cell23_2344092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2344092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344092 prefixEnd_2344092 := by exact prefixLift 2344092
  have htrace : WordTrace (prefixWord ++ tailWord_2344092) baseStart_2344092 baseEnd_2344092 := by
    simpa [prefixWord, tailWord_2344092, baseEnd_2344092] using wordTrace_append hprefix tailTrace_2344092
  have hstable : (prefixWord ++ tailWord_2344092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344092).length < 2 ^ (prefixWord ++ tailWord_2344092).sum := by decide
  have hdescent : baseEnd_2344092 < baseStart_2344092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344106 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2344106 : Nat := 118140960795 + 2344106 * 2 ^ 59
def prefixEnd_2344106 : Nat := 4983230072969 + 3 ^ 40 * 2344106 * 2
def baseEnd_2344106 : Nat := 401217694362770302731553

theorem tailTrace_2344106 : CollatzResearch.WordTrace tailWord_2344106 prefixEnd_2344106 401217694362770302731553 := by
  unfold tailWord_2344106
  simp only [CollatzResearch.WordTrace]
  refine ⟨21374142411427944569275043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56997713097141185518066781 21374142411427944569275043)
  ·
    refine ⟨32061213617141916853912565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21374142411427944569275043 32061213617141916853912565)
    ·
      refine ⟨3005738776607054705054303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32061213617141916853912565 3005738776607054705054303)
      ·
        refine ⟨4508608164910582057581455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005738776607054705054303 4508608164910582057581455)
        ·
          refine ⟨6762912247365873086372183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508608164910582057581455 6762912247365873086372183)
          ·
            refine ⟨10144368371048809629558275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6762912247365873086372183 10144368371048809629558275)
            ·
              refine ⟨15216552556573214444337413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10144368371048809629558275 15216552556573214444337413)
              ·
                refine ⟨2853103604357477708313265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15216552556573214444337413 2853103604357477708313265)
                ·
                  refine ⟨2139827703268108281234949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2853103604357477708313265 2139827703268108281234949)
                  ·
                    refine ⟨401217694362770302731553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2139827703268108281234949 401217694362770302731553)
                    ·
                      rfl

theorem cell23_2344106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2344106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344106 prefixEnd_2344106 := by exact prefixLift 2344106
  have htrace : WordTrace (prefixWord ++ tailWord_2344106) baseStart_2344106 baseEnd_2344106 := by
    simpa [prefixWord, tailWord_2344106, baseEnd_2344106] using wordTrace_append hprefix tailTrace_2344106
  have hstable : (prefixWord ++ tailWord_2344106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344106).length < 2 ^ (prefixWord ++ tailWord_2344106).sum := by decide
  have hdescent : baseEnd_2344106 < baseStart_2344106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344115 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 2, 7]
def baseStart_2344115 : Nat := 118140960795 + 2344115 * 2 ^ 59
def prefixEnd_2344115 : Nat := 4983230072969 + 3 ^ 40 * 2344115 * 2
def baseEnd_2344115 : Nat := 401219234804733790994039

theorem tailTrace_2344115 : CollatzResearch.WordTrace tailWord_2344115 prefixEnd_2344115 401219234804733790994039 := by
  unfold tailWord_2344115
  simp only [CollatzResearch.WordTrace]
  refine ⟨85496897902679172814177799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56997931935119448542785199 85496897902679172814177799)
  ·
    refine ⟨128245346854018759221266699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85496897902679172814177799 128245346854018759221266699)
    ·
      refine ⟨192368020281028138831900049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128245346854018759221266699 192368020281028138831900049)
      ·
        refine ⟨144276015210771104123925037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192368020281028138831900049 144276015210771104123925037)
        ·
          refine ⟨54103505704039164046471889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144276015210771104123925037 54103505704039164046471889)
          ·
            refine ⟨40577629278029373034853917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54103505704039164046471889 40577629278029373034853917)
            ·
              refine ⟨15216610979261014888070219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40577629278029373034853917 15216610979261014888070219)
              ·
                refine ⟨22824916468891522332105329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15216610979261014888070219 22824916468891522332105329)
                ·
                  refine ⟨17118687351668641749078997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22824916468891522332105329 17118687351668641749078997)
                  ·
                    refine ⟨401219234804733790994039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17118687351668641749078997 401219234804733790994039)
                    ·
                      rfl

theorem cell23_2344115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 7].length) (baseStart_2344115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344115 prefixEnd_2344115 := by exact prefixLift 2344115
  have htrace : WordTrace (prefixWord ++ tailWord_2344115) baseStart_2344115 baseEnd_2344115 := by
    simpa [prefixWord, tailWord_2344115, baseEnd_2344115] using wordTrace_append hprefix tailTrace_2344115
  have hstable : (prefixWord ++ tailWord_2344115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344115).length < 2 ^ (prefixWord ++ tailWord_2344115).sum := by decide
  have hdescent : baseEnd_2344115 < baseStart_2344115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344134 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2344134 : Nat := 118140960795 + 2344134 * 2 ^ 59
def prefixEnd_2344134 : Nat := 4983230072969 + 3 ^ 40 * 2344134 * 2
def baseEnd_2344134 : Nat := 1203667460546636798644531

theorem tailTrace_2344134 : CollatzResearch.WordTrace tailWord_2344134 prefixEnd_2344134 1203667460546636798644531 := by
  unfold tailWord_2344134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671799715300323095597483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56998393926406892706079637 2671799715300323095597483)
  ·
    refine ⟨4007699572950484643396225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2671799715300323095597483 4007699572950484643396225)
    ·
      refine ⟨3005774679712863482547169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4007699572950484643396225 3005774679712863482547169)
      ·
        refine ⟨2254331009784647611910377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3005774679712863482547169 2254331009784647611910377)
        ·
          refine ⟨1690748257338485708932783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2254331009784647611910377 1690748257338485708932783)
          ·
            refine ⟨2536122386007728563399175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690748257338485708932783 2536122386007728563399175)
            ·
              refine ⟨3804183579011592845098763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536122386007728563399175 3804183579011592845098763)
              ·
                refine ⟨5706275368517389267648145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3804183579011592845098763 5706275368517389267648145)
                ·
                  refine ⟨4279706526388041950736109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5706275368517389267648145 4279706526388041950736109)
                  ·
                    refine ⟨1604889947395515731526041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4279706526388041950736109 1604889947395515731526041)
                    ·
                      refine ⟨1203667460546636798644531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604889947395515731526041 1203667460546636798644531)
                      ·
                        rfl

theorem cell23_2344134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2344134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344134 prefixEnd_2344134 := by exact prefixLift 2344134
  have htrace : WordTrace (prefixWord ++ tailWord_2344134) baseStart_2344134 baseEnd_2344134 := by
    simpa [prefixWord, tailWord_2344134, baseEnd_2344134] using wordTrace_append hprefix tailTrace_2344134
  have hstable : (prefixWord ++ tailWord_2344134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344134).length < 2 ^ (prefixWord ++ tailWord_2344134).sum := by decide
  have hdescent : baseEnd_2344134 < baseStart_2344134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344145 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 3, 8]
def baseStart_2344145 : Nat := 118140960795 + 2344145 * 2 ^ 59
def prefixEnd_2344145 : Nat := 4983230072969 + 3 ^ 40 * 2344145 * 2
def baseEnd_2344145 : Nat := 401224369611278751868993

theorem tailTrace_2344145 : CollatzResearch.WordTrace tailWord_2344145 prefixEnd_2344145 401224369611278751868993 := by
  unfold tailWord_2344145
  simp only [CollatzResearch.WordTrace]
  refine ⟨85497992092570487937769889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56998661395046991958513259 85497992092570487937769889)
  ·
    refine ⟨64123494069427865953327417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85497992092570487937769889 64123494069427865953327417)
    ·
      refine ⟨48092620552070899464995563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64123494069427865953327417 48092620552070899464995563)
      ·
        refine ⟨72138930828106349197493345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48092620552070899464995563 72138930828106349197493345)
        ·
          refine ⟨54104198121079761898120009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72138930828106349197493345 54104198121079761898120009)
          ·
            refine ⟨40578148590809821423590007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54104198121079761898120009 40578148590809821423590007)
            ·
              refine ⟨60867222886214732135385011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40578148590809821423590007 60867222886214732135385011)
              ·
                refine ⟨91300834329322098203077517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60867222886214732135385011 91300834329322098203077517)
                ·
                  refine ⟨34237812873495786826154069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91300834329322098203077517 34237812873495786826154069)
                  ·
                    refine ⟨401224369611278751868993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34237812873495786826154069 401224369611278751868993)
                    ·
                      rfl

theorem cell23_2344145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_2344145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344145 prefixEnd_2344145 := by exact prefixLift 2344145
  have htrace : WordTrace (prefixWord ++ tailWord_2344145) baseStart_2344145 baseEnd_2344145 := by
    simpa [prefixWord, tailWord_2344145, baseEnd_2344145] using wordTrace_append hprefix tailTrace_2344145
  have hstable : (prefixWord ++ tailWord_2344145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344145).length < 2 ^ (prefixWord ++ tailWord_2344145).sum := by decide
  have hdescent : baseEnd_2344145 < baseStart_2344145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344226 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 7]
def baseStart_2344226 : Nat := 118140960795 + 2344226 * 2 ^ 59
def prefixEnd_2344226 : Nat := 4983230072969 + 3 ^ 40 * 2344226 * 2
def baseEnd_2344226 : Nat := 133746077862983382077123

theorem tailTrace_2344226 : CollatzResearch.WordTrace tailWord_2344226 prefixEnd_2344226 133746077862983382077123 := by
  unfold tailWord_2344226
  simp only [CollatzResearch.WordTrace]
  refine ⟨21375236601319259692867133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57000630936851359180979021 21375236601319259692867133)
  ·
    refine ⟨8015713725494722384825175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21375236601319259692867133 8015713725494722384825175)
    ·
      refine ⟨12023570588242083577237763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8015713725494722384825175 12023570588242083577237763)
      ·
        refine ⟨18035355882363125365856645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12023570588242083577237763 18035355882363125365856645)
        ·
          refine ⟨3381629227943086006098121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18035355882363125365856645 3381629227943086006098121)
          ·
            refine ⟨2536221920957314504573591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3381629227943086006098121 2536221920957314504573591)
            ·
              refine ⟨3804332881435971756860387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536221920957314504573591 3804332881435971756860387)
              ·
                refine ⟨5706499322153957635290581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3804332881435971756860387 5706499322153957635290581)
                ·
                  refine ⟨133746077862983382077123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5706499322153957635290581 133746077862983382077123)
                  ·
                    rfl

theorem cell23_2344226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_2344226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344226 prefixEnd_2344226 := by exact prefixLift 2344226
  have htrace : WordTrace (prefixWord ++ tailWord_2344226) baseStart_2344226 baseEnd_2344226 := by
    simpa [prefixWord, tailWord_2344226, baseEnd_2344226] using wordTrace_append hprefix tailTrace_2344226
  have hstable : (prefixWord ++ tailWord_2344226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344226).length < 2 ^ (prefixWord ++ tailWord_2344226).sum := by decide
  have hdescent : baseEnd_2344226 < baseStart_2344226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344237 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_2344237 : Nat := 118140960795 + 2344237 * 2 ^ 59
def prefixEnd_2344237 : Nat := 4983230072969 + 3 ^ 40 * 2344237 * 2
def baseEnd_2344237 : Nat := 1203720349054049895656557

theorem tailTrace_2344237 : CollatzResearch.WordTrace tailWord_2344237 prefixEnd_2344237 1203720349054049895656557 := by
  unfold tailWord_2344237
  simp only [CollatzResearch.WordTrace]
  refine ⟨85501347608237187650118965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57000898405491458433412643 85501347608237187650118965)
  ·
    refine ⟨8015751338272236342198653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85501347608237187650118965 8015751338272236342198653)
    ·
      refine ⟨3005906751852088628324495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8015751338272236342198653 3005906751852088628324495)
      ·
        refine ⟨4508860127778132942486743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005906751852088628324495 4508860127778132942486743)
        ·
          refine ⟨6763290191667199413730115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508860127778132942486743 6763290191667199413730115)
          ·
            refine ⟨10144935287500799120595173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6763290191667199413730115 10144935287500799120595173)
            ·
              refine ⟨1902175366406399835111595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10144935287500799120595173 1902175366406399835111595)
              ·
                refine ⟨2853263049609599752667393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902175366406399835111595 2853263049609599752667393)
                ·
                  refine ⟨2139947287207199814500545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2853263049609599752667393 2139947287207199814500545)
                  ·
                    refine ⟨1604960465405399860875409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139947287207199814500545 1604960465405399860875409)
                    ·
                      refine ⟨1203720349054049895656557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604960465405399860875409 1203720349054049895656557)
                      ·
                        rfl

theorem cell23_2344237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_2344237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344237 prefixEnd_2344237 := by exact prefixLift 2344237
  have htrace : WordTrace (prefixWord ++ tailWord_2344237) baseStart_2344237 baseEnd_2344237 := by
    simpa [prefixWord, tailWord_2344237, baseEnd_2344237] using wordTrace_append hprefix tailTrace_2344237
  have hstable : (prefixWord ++ tailWord_2344237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344237).length < 2 ^ (prefixWord ++ tailWord_2344237).sum := by decide
  have hdescent : baseEnd_2344237 < baseStart_2344237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344259 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 4, 4, 2]
def baseStart_2344259 : Nat := 118140960795 + 2344259 * 2 ^ 59
def prefixEnd_2344259 : Nat := 4983230072969 + 3 ^ 40 * 2344259 * 2
def baseEnd_2344259 : Nat := 1203731645628448809581455

theorem tailTrace_2344259 : CollatzResearch.WordTrace tailWord_2344259 prefixEnd_2344259 1203731645628448809581455 := by
  unfold tailWord_2344259
  simp only [CollatzResearch.WordTrace]
  refine ⟨85502150014157485407419831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57001433342771656938279887 85502150014157485407419831)
  ·
    refine ⟨128253225021236228111129747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85502150014157485407419831 128253225021236228111129747)
    ·
      refine ⟨192379837531854342166694621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128253225021236228111129747 192379837531854342166694621)
      ·
        refine ⟨72142439074445378312510483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192379837531854342166694621 72142439074445378312510483)
        ·
          refine ⟨108213658611668067468765725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72142439074445378312510483 108213658611668067468765725)
          ·
            refine ⟨40580121979375525300787147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108213658611668067468765725 40580121979375525300787147)
            ·
              refine ⟨60870182969063287951180721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40580121979375525300787147 60870182969063287951180721)
              ·
                refine ⟨45652637226797465963385541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60870182969063287951180721 45652637226797465963385541)
                ·
                  refine ⟨8559869480024524868134789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45652637226797465963385541 8559869480024524868134789)
                  ·
                    refine ⟨1604975527504598412775273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8559869480024524868134789 1604975527504598412775273)
                    ·
                      refine ⟨1203731645628448809581455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604975527504598412775273 1203731645628448809581455)
                      ·
                        rfl

theorem cell23_2344259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_2344259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344259 prefixEnd_2344259 := by exact prefixLift 2344259
  have htrace : WordTrace (prefixWord ++ tailWord_2344259) baseStart_2344259 baseEnd_2344259 := by
    simpa [prefixWord, tailWord_2344259, baseEnd_2344259] using wordTrace_append hprefix tailTrace_2344259
  have hstable : (prefixWord ++ tailWord_2344259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344259).length < 2 ^ (prefixWord ++ tailWord_2344259).sum := by decide
  have hdescent : baseEnd_2344259 < baseStart_2344259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344272 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_2344272 : Nat := 118140960795 + 2344272 * 2 ^ 59
def prefixEnd_2344272 : Nat := 4983230072969 + 3 ^ 40 * 2344272 * 2
def baseEnd_2344272 : Nat := 1203738320876957258718895

theorem tailTrace_2344272 : CollatzResearch.WordTrace tailWord_2344272 prefixEnd_2344272 1203738320876957258718895 := by
  unfold tailWord_2344272
  simp only [CollatzResearch.WordTrace]
  refine ⟨42751312081555194313821535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57001749442073592418428713 42751312081555194313821535)
  ·
    refine ⟨64126968122332791470732303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42751312081555194313821535 64126968122332791470732303)
    ·
      refine ⟨96190452183499187206098455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64126968122332791470732303 96190452183499187206098455)
      ·
        refine ⟨144285678275248780809147683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96190452183499187206098455 144285678275248780809147683)
        ·
          refine ⟨216428517412873171213721525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144285678275248780809147683 216428517412873171213721525)
          ·
            refine ⟨20290173507456859801286393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 216428517412873171213721525 20290173507456859801286393)
            ·
              refine ⟨15217630130592644850964795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20290173507456859801286393 15217630130592644850964795)
              ·
                refine ⟨22826445195888967276447193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15217630130592644850964795 22826445195888967276447193)
                ·
                  refine ⟨17119833896916725457335395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22826445195888967276447193 17119833896916725457335395)
                  ·
                    refine ⟨25679750845375088186003093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17119833896916725457335395 25679750845375088186003093)
                    ·
                      refine ⟨1203738320876957258718895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25679750845375088186003093 1203738320876957258718895)
                      ·
                        rfl

theorem cell23_2344272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_2344272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344272 prefixEnd_2344272 := by exact prefixLift 2344272
  have htrace : WordTrace (prefixWord ++ tailWord_2344272) baseStart_2344272 baseEnd_2344272 := by
    simpa [prefixWord, tailWord_2344272, baseEnd_2344272] using wordTrace_append hprefix tailTrace_2344272
  have hstable : (prefixWord ++ tailWord_2344272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344272).length < 2 ^ (prefixWord ++ tailWord_2344272).sum := by decide
  have hdescent : baseEnd_2344272 < baseStart_2344272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344276 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_2344276 : Nat := 118140960795 + 2344276 * 2 ^ 59
def prefixEnd_2344276 : Nat := 4983230072969 + 3 ^ 40 * 2344276 * 2
def baseEnd_2344276 : Nat := 1203740374799575243068877

theorem tailTrace_2344276 : CollatzResearch.WordTrace tailWord_2344276 prefixEnd_2344276 1203740374799575243068877 := by
  unfold tailWord_2344276
  simp only [CollatzResearch.WordTrace]
  refine ⟨42751385027547948655394341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57001846703397264873859121 42751385027547948655394341)
  ·
    refine ⟨8015884692665240372886439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42751385027547948655394341 8015884692665240372886439)
    ·
      refine ⟨12023827038997860559329659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8015884692665240372886439 12023827038997860559329659)
      ·
        refine ⟨18035740558496790838994489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12023827038997860559329659 18035740558496790838994489)
        ·
          refine ⟨13526805418872593129245867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18035740558496790838994489 13526805418872593129245867)
          ·
            refine ⟨20290208128308889693868801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13526805418872593129245867 20290208128308889693868801)
            ·
              refine ⟨15217656096231667270401601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20290208128308889693868801 15217656096231667270401601)
              ·
                refine ⟨11413242072173750452801201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15217656096231667270401601 11413242072173750452801201)
                ·
                  refine ⟨8559931554130312839600901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11413242072173750452801201 8559931554130312839600901)
                  ·
                    refine ⟨1604987166399433657425169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8559931554130312839600901 1604987166399433657425169)
                    ·
                      refine ⟨1203740374799575243068877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1604987166399433657425169 1203740374799575243068877)
                      ·
                        rfl

theorem cell23_2344276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_2344276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344276 prefixEnd_2344276 := by exact prefixLift 2344276
  have htrace : WordTrace (prefixWord ++ tailWord_2344276) baseStart_2344276 baseEnd_2344276 := by
    simpa [prefixWord, tailWord_2344276, baseEnd_2344276] using wordTrace_append hprefix tailTrace_2344276
  have hstable : (prefixWord ++ tailWord_2344276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344276).length < 2 ^ (prefixWord ++ tailWord_2344276).sum := by decide
  have hdescent : baseEnd_2344276 < baseStart_2344276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344282 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 8]
def baseStart_2344282 : Nat := 118140960795 + 2344282 * 2 ^ 59
def prefixEnd_2344282 : Nat := 4983230072969 + 3 ^ 40 * 2344282 * 2
def baseEnd_2344282 : Nat := 133749272853722468843761

theorem tailTrace_2344282 : CollatzResearch.WordTrace tailWord_2344282 prefixEnd_2344282 133749272853722468843761 := by
  unfold tailWord_2344282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21375747223268540083876775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57001992595382773557004733 21375747223268540083876775)
  ·
    refine ⟨32063620834902810125815163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21375747223268540083876775 32063620834902810125815163)
    ·
      refine ⟨48095431252354215188722745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32063620834902810125815163 48095431252354215188722745)
      ·
        refine ⟨36071573439265661391542059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48095431252354215188722745 36071573439265661391542059)
        ·
          refine ⟨54107360158898492087313089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36071573439265661391542059 54107360158898492087313089)
          ·
            refine ⟨40580520119173869065484817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54107360158898492087313089 40580520119173869065484817)
            ·
              refine ⟨30435390089380401799113613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40580520119173869065484817 30435390089380401799113613)
              ·
                refine ⟨11413271283517650674667605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30435390089380401799113613 11413271283517650674667605)
                ·
                  refine ⟨133749272853722468843761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11413271283517650674667605 133749272853722468843761)
                  ·
                    rfl

theorem cell23_2344282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_2344282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344282 prefixEnd_2344282 := by exact prefixLift 2344282
  have htrace : WordTrace (prefixWord ++ tailWord_2344282) baseStart_2344282 baseEnd_2344282 := by
    simpa [prefixWord, tailWord_2344282, baseEnd_2344282] using wordTrace_append hprefix tailTrace_2344282
  have hstable : (prefixWord ++ tailWord_2344282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344282).length < 2 ^ (prefixWord ++ tailWord_2344282).sum := by decide
  have hdescent : baseEnd_2344282 < baseStart_2344282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344350 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2344350 : Nat := 118140960795 + 2344350 * 2 ^ 59
def prefixEnd_2344350 : Nat := 4983230072969 + 3 ^ 40 * 2344350 * 2
def baseEnd_2344350 : Nat := 133753152485334217060393

theorem tailTrace_2344350 : CollatzResearch.WordTrace tailWord_2344350 prefixEnd_2344350 133753152485334217060393 := by
  unfold tailWord_2344350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10688183632103475993622813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57003646037885205299321669 10688183632103475993622813)
  ·
    refine ⟨4008068862038803497608555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10688183632103475993622813 4008068862038803497608555)
    ·
      refine ⟨6012103293058205246412833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4008068862038803497608555 6012103293058205246412833)
      ·
        refine ⟨4509077469793653934809625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6012103293058205246412833 4509077469793653934809625)
        ·
          refine ⟨3381808102345240451107219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4509077469793653934809625 3381808102345240451107219)
          ·
            refine ⟨5072712153517860676660829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381808102345240451107219 5072712153517860676660829)
            ·
              refine ⟨1902267057569197753747811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5072712153517860676660829 1902267057569197753747811)
              ·
                refine ⟨2853400586353796630621717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902267057569197753747811 2853400586353796630621717)
                ·
                  refine ⟨133753152485334217060393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2853400586353796630621717 133753152485334217060393)
                  ·
                    rfl

theorem cell23_2344350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2344350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344350 prefixEnd_2344350 := by exact prefixLift 2344350
  have htrace : WordTrace (prefixWord ++ tailWord_2344350) baseStart_2344350 baseEnd_2344350 := by
    simpa [prefixWord, tailWord_2344350, baseEnd_2344350] using wordTrace_append hprefix tailTrace_2344350
  have hstable : (prefixWord ++ tailWord_2344350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344350).length < 2 ^ (prefixWord ++ tailWord_2344350).sum := by decide
  have hdescent : baseEnd_2344350 < baseStart_2344350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344369 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2344369 : Nat := 118140960795 + 2344369 * 2 ^ 59
def prefixEnd_2344369 : Nat := 4983230072969 + 3 ^ 40 * 2344369 * 2
def baseEnd_2344369 : Nat := 1203788128500443379205949

theorem tailTrace_2344369 : CollatzResearch.WordTrace tailWord_2344369 prefixEnd_2344369 1203788128500443379205949 := by
  unfold tailWord_2344369
  simp only [CollatzResearch.WordTrace]
  refine ⟨85506162043758974193924161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57004108029172649462616107 85506162043758974193924161)
  ·
    refine ⟨64129621532819230645443121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85506162043758974193924161 64129621532819230645443121)
    ·
      refine ⟨48097216149614422984082341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64129621532819230645443121 48097216149614422984082341)
      ·
        refine ⟨9018228028052704309515439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48097216149614422984082341 9018228028052704309515439)
        ·
          refine ⟨13527342042079056464273159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9018228028052704309515439 13527342042079056464273159)
          ·
            refine ⟨20291013063118584696409739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13527342042079056464273159 20291013063118584696409739)
            ·
              refine ⟨30436519594677877044614609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20291013063118584696409739 30436519594677877044614609)
              ·
                refine ⟨22827389696008407783460957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30436519594677877044614609 22827389696008407783460957)
                ·
                  refine ⟨8560271136003152918797859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22827389696008407783460957 8560271136003152918797859)
                  ·
                    refine ⟨12840406704004729378196789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8560271136003152918797859 12840406704004729378196789)
                    ·
                      refine ⟨1203788128500443379205949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12840406704004729378196789 1203788128500443379205949)
                      ·
                        rfl

theorem cell23_2344369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2344369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344369 prefixEnd_2344369 := by exact prefixLift 2344369
  have htrace : WordTrace (prefixWord ++ tailWord_2344369) baseStart_2344369 baseEnd_2344369 := by
    simpa [prefixWord, tailWord_2344369, baseEnd_2344369] using wordTrace_append hprefix tailTrace_2344369
  have hstable : (prefixWord ++ tailWord_2344369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344369).length < 2 ^ (prefixWord ++ tailWord_2344369).sum := by decide
  have hdescent : baseEnd_2344369 < baseStart_2344369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344377 : List Nat := [1, 2, 1, 4, 4, 2, 1, 3, 1, 1, 3]
def baseStart_2344377 : Nat := 118140960795 + 2344377 * 2 ^ 59
def prefixEnd_2344377 : Nat := 4983230072969 + 3 ^ 40 * 2344377 * 2
def baseEnd_2344377 : Nat := 1203792236345679347905913

theorem tailTrace_2344377 : CollatzResearch.WordTrace tailWord_2344377 prefixEnd_2344377 1203792236345679347905913 := by
  unfold tailWord_2344377
  simp only [CollatzResearch.WordTrace]
  refine ⟨85506453827729991560215385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57004302551819994373476923 85506453827729991560215385)
  ·
    refine ⟨64129840370797493670161539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85506453827729991560215385 64129840370797493670161539)
    ·
      refine ⟨96194760556196240505242309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64129840370797493670161539 96194760556196240505242309)
      ·
        refine ⟨18036517604286795094732933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96194760556196240505242309 18036517604286795094732933)
        ·
          refine ⟨3381847050803774080262425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18036517604286795094732933 3381847050803774080262425)
          ·
            refine ⟨2536385288102830560196819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3381847050803774080262425 2536385288102830560196819)
            ·
              refine ⟨3804577932154245840295229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536385288102830560196819 3804577932154245840295229)
              ·
                refine ⟨1426716724557842190110711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3804577932154245840295229 1426716724557842190110711)
                ·
                  refine ⟨2140075086836763285166067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426716724557842190110711 2140075086836763285166067)
                  ·
                    refine ⟨3210112630255144927749101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2140075086836763285166067 3210112630255144927749101)
                    ·
                      refine ⟨1203792236345679347905913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3210112630255144927749101 1203792236345679347905913)
                      ·
                        rfl

theorem cell23_2344377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_2344377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344377 prefixEnd_2344377 := by exact prefixLift 2344377
  have htrace : WordTrace (prefixWord ++ tailWord_2344377) baseStart_2344377 baseEnd_2344377 := by
    simpa [prefixWord, tailWord_2344377, baseEnd_2344377] using wordTrace_append hprefix tailTrace_2344377
  have hstable : (prefixWord ++ tailWord_2344377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344377).length < 2 ^ (prefixWord ++ tailWord_2344377).sum := by decide
  have hdescent : baseEnd_2344377 < baseStart_2344377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344406 : List Nat := [5, 2, 1, 1, 1, 2, 1, 10]
def baseStart_2344406 : Nat := 118140960795 + 2344406 * 2 ^ 59
def prefixEnd_2344406 : Nat := 4983230072969 + 3 ^ 40 * 2344406 * 2
def baseEnd_2344406 : Nat := 44585449158691101275677

theorem tailTrace_2344406 : CollatzResearch.WordTrace tailWord_2344406 prefixEnd_2344406 44585449158691101275677 := by
  unfold tailWord_2344406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344219471539058094563817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57005007696416619675347381 5344219471539058094563817)
  ·
    refine ⟨4008164603654293570922863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5344219471539058094563817 4008164603654293570922863)
    ·
      refine ⟨6012246905481440356384295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4008164603654293570922863 6012246905481440356384295)
      ·
        refine ⟨9018370358222160534576443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6012246905481440356384295 9018370358222160534576443)
        ·
          refine ⟨13527555537333240801864665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9018370358222160534576443 13527555537333240801864665)
          ·
            refine ⟨10145666652999930601398499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13527555537333240801864665 10145666652999930601398499)
            ·
              refine ⟨15218499979499895902097749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10145666652999930601398499 15218499979499895902097749)
              ·
                refine ⟨44585449158691101275677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15218499979499895902097749 44585449158691101275677)
                ·
                  rfl

theorem cell23_2344406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_2344406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344406 prefixEnd_2344406 := by exact prefixLift 2344406
  have htrace : WordTrace (prefixWord ++ tailWord_2344406) baseStart_2344406 baseEnd_2344406 := by
    simpa [prefixWord, tailWord_2344406, baseEnd_2344406] using wordTrace_append hprefix tailTrace_2344406
  have hstable : (prefixWord ++ tailWord_2344406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344406).length < 2 ^ (prefixWord ++ tailWord_2344406).sum := by decide
  have hdescent : baseEnd_2344406 < baseStart_2344406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344410 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_2344410 : Nat := 118140960795 + 2344410 * 2 ^ 59
def prefixEnd_2344410 : Nat := 4983230072969 + 3 ^ 40 * 2344410 * 2
def baseEnd_2344410 : Nat := 401269727069092572931087

theorem tailTrace_2344410 : CollatzResearch.WordTrace tailWord_2344410 prefixEnd_2344410 401269727069092572931087 := by
  unfold tailWord_2344410
  simp only [CollatzResearch.WordTrace]
  refine ⟨21376914359152609549041671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57005104957740292130777789 21376914359152609549041671)
  ·
    refine ⟨32065371538728914323562507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21376914359152609549041671 32065371538728914323562507)
    ·
      refine ⟨48098057308093371485343761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32065371538728914323562507 48098057308093371485343761)
      ·
        refine ⟨36073542981070028614007821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48098057308093371485343761 36073542981070028614007821)
        ·
          refine ⟨13527578617901260730252933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36073542981070028614007821 13527578617901260730252933)
          ·
            refine ⟨2536420990856486386922425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13527578617901260730252933 2536420990856486386922425)
            ·
              refine ⟨1902315743142364790191819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2536420990856486386922425 1902315743142364790191819)
              ·
                refine ⟨2853473614713547185287729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902315743142364790191819 2853473614713547185287729)
                ·
                  refine ⟨2140105211035160388965797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2853473614713547185287729 2140105211035160388965797)
                  ·
                    refine ⟨401269727069092572931087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140105211035160388965797 401269727069092572931087)
                    ·
                      rfl

theorem cell23_2344410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_2344410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344410 prefixEnd_2344410 := by exact prefixLift 2344410
  have htrace : WordTrace (prefixWord ++ tailWord_2344410) baseStart_2344410 baseEnd_2344410 := by
    simpa [prefixWord, tailWord_2344410, baseEnd_2344410] using wordTrace_append hprefix tailTrace_2344410
  have hstable : (prefixWord ++ tailWord_2344410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344410).length < 2 ^ (prefixWord ++ tailWord_2344410).sum := by decide
  have hdescent : baseEnd_2344410 < baseStart_2344410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344416 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 6, 1, 3]
def baseStart_2344416 : Nat := 118140960795 + 2344416 * 2 ^ 59
def prefixEnd_2344416 : Nat := 4983230072969 + 3 ^ 40 * 2344416 * 2
def baseEnd_2344416 : Nat := 1203812262091204695318233

theorem tailTrace_2344416 : CollatzResearch.WordTrace tailWord_2344416 prefixEnd_2344416 1203812262091204695318233 := by
  unfold tailWord_2344416
  simp only [CollatzResearch.WordTrace]
  refine ⟨42753938137294350610442551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57005250849725800813923401 42753938137294350610442551)
  ·
    refine ⟨64130907205941525915663827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42753938137294350610442551 64130907205941525915663827)
    ·
      refine ⟨96196360808912288873495741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64130907205941525915663827 96196360808912288873495741)
      ·
        refine ⟨36073635303342108327560903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96196360808912288873495741 36073635303342108327560903)
        ·
          refine ⟨54110452955013162491341355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36073635303342108327560903 54110452955013162491341355)
          ·
            refine ⟨81165679432519743737012033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54110452955013162491341355 81165679432519743737012033)
            ·
              refine ⟨60874259574389807802759025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81165679432519743737012033 60874259574389807802759025)
              ·
                refine ⟨45655694680792355852069269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60874259574389807802759025 45655694680792355852069269)
                ·
                  refine ⟨2140110688162141680565747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45655694680792355852069269 2140110688162141680565747)
                  ·
                    refine ⟨3210166032243212520848621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2140110688162141680565747 3210166032243212520848621)
                    ·
                      refine ⟨1203812262091204695318233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3210166032243212520848621 1203812262091204695318233)
                      ·
                        rfl

theorem cell23_2344416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_2344416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344416 prefixEnd_2344416 := by exact prefixLift 2344416
  have htrace : WordTrace (prefixWord ++ tailWord_2344416) baseStart_2344416 baseEnd_2344416 := by
    simpa [prefixWord, tailWord_2344416, baseEnd_2344416] using wordTrace_append hprefix tailTrace_2344416
  have hstable : (prefixWord ++ tailWord_2344416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344416).length < 2 ^ (prefixWord ++ tailWord_2344416).sum := by decide
  have hdescent : baseEnd_2344416 < baseStart_2344416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344437 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2344437 : Nat := 118140960795 + 2344437 * 2 ^ 59
def prefixEnd_2344437 : Nat := 4983230072969 + 3 ^ 40 * 2344437 * 2
def baseEnd_2344437 : Nat := 1203823045184949113155637

theorem tailTrace_2344437 : CollatzResearch.WordTrace tailWord_2344437 prefixEnd_2344437 1203823045184949113155637 := by
  unfold tailWord_2344437
  simp only [CollatzResearch.WordTrace]
  refine ⟨85508642207512621807399565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57005761471675081204933043 85508642207512621807399565)
  ·
    refine ⟨32065740827817233177774837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85508642207512621807399565 32065740827817233177774837)
    ·
      refine ⟨3006163202607865610416391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32065740827817233177774837 3006163202607865610416391)
      ·
        refine ⟨4509244803911798415624587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3006163202607865610416391 4509244803911798415624587)
        ·
          refine ⟨6763867205867697623436881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4509244803911798415624587 6763867205867697623436881)
          ·
            refine ⟨5072900404400773217577661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6763867205867697623436881 5072900404400773217577661)
            ·
              refine ⟨1902337651650289956591623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5072900404400773217577661 1902337651650289956591623)
              ·
                refine ⟨2853506477475434934887435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902337651650289956591623 2853506477475434934887435)
                ·
                  refine ⟨4280259716213152402331153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853506477475434934887435 4280259716213152402331153)
                  ·
                    refine ⟨3210194787159864301748365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4280259716213152402331153 3210194787159864301748365)
                    ·
                      refine ⟨1203823045184949113155637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3210194787159864301748365 1203823045184949113155637)
                      ·
                        rfl

theorem cell23_2344437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2344437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344437 prefixEnd_2344437 := by exact prefixLift 2344437
  have htrace : WordTrace (prefixWord ++ tailWord_2344437) baseStart_2344437 baseEnd_2344437 := by
    simpa [prefixWord, tailWord_2344437, baseEnd_2344437] using wordTrace_append hprefix tailTrace_2344437
  have hstable : (prefixWord ++ tailWord_2344437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344437).length < 2 ^ (prefixWord ++ tailWord_2344437).sum := by decide
  have hdescent : baseEnd_2344437 < baseStart_2344437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344476 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2344476 : Nat := 118140960795 + 2344476 * 2 ^ 59
def prefixEnd_2344476 : Nat := 4983230072969 + 3 ^ 40 * 2344476 * 2
def baseEnd_2344476 : Nat := 1203843070930474460567957

theorem tailTrace_2344476 : CollatzResearch.WordTrace tailWord_2344476 prefixEnd_2344476 1203843070930474460567957 := by
  unfold tailWord_2344476
  simp only [CollatzResearch.WordTrace]
  refine ⟨42755032327185665734034641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57006709769580887645379521 42755032327185665734034641)
  ·
    refine ⟨32066274245389249300525981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42755032327185665734034641 32066274245389249300525981)
    ·
      refine ⟨12024852842020968487697243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32066274245389249300525981 12024852842020968487697243)
      ·
        refine ⟨18037279263031452731545865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12024852842020968487697243 18037279263031452731545865)
        ·
          refine ⟨13527959447273589548659399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18037279263031452731545865 13527959447273589548659399)
          ·
            refine ⟨20291939170910384322989099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13527959447273589548659399 20291939170910384322989099)
            ·
              refine ⟨30437908756365576484483649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20291939170910384322989099 30437908756365576484483649)
              ·
                refine ⟨22828431567274182363362737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30437908756365576484483649 22828431567274182363362737)
                ·
                  refine ⟨17121323675455636772522053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22828431567274182363362737 17121323675455636772522053)
                  ·
                    refine ⟨3210248189147931894847885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17121323675455636772522053 3210248189147931894847885)
                    ·
                      refine ⟨1203843070930474460567957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3210248189147931894847885 1203843070930474460567957)
                      ·
                        rfl

theorem cell23_2344476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2344476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344476 prefixEnd_2344476 := by exact prefixLift 2344476
  have htrace : WordTrace (prefixWord ++ tailWord_2344476) baseStart_2344476 baseEnd_2344476 := by
    simpa [prefixWord, tailWord_2344476, baseEnd_2344476] using wordTrace_append hprefix tailTrace_2344476
  have hstable : (prefixWord ++ tailWord_2344476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344476).length < 2 ^ (prefixWord ++ tailWord_2344476).sum := by decide
  have hdescent : baseEnd_2344476 < baseStart_2344476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344479 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 9]
def baseStart_2344479 : Nat := 118140960795 + 2344479 * 2 ^ 59
def prefixEnd_2344479 : Nat := 4983230072969 + 3 ^ 40 * 2344479 * 2
def baseEnd_2344479 : Nat := 133760512374715327647827

theorem tailTrace_2344479 : CollatzResearch.WordTrace tailWord_2344479 prefixEnd_2344479 133760512374715327647827 := by
  unfold tailWord_2344479
  simp only [CollatzResearch.WordTrace]
  refine ⟨85510174073360462980428491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57006782715573641986952327 85510174073360462980428491)
  ·
    refine ⟨128265261110040694470642737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85510174073360462980428491 128265261110040694470642737)
    ·
      refine ⟨96198945832530520852982053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128265261110040694470642737 96198945832530520852982053)
      ·
        refine ⟨18037302343599472659934135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96198945832530520852982053 18037302343599472659934135)
        ·
          refine ⟨27055953515399208989901203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18037302343599472659934135 27055953515399208989901203)
          ·
            refine ⟨40583930273098813484851805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27055953515399208989901203 40583930273098813484851805)
            ·
              refine ⟨15218973852412055056819427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40583930273098813484851805 15218973852412055056819427)
              ·
                refine ⟨22828460778618082585229141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15218973852412055056819427 22828460778618082585229141)
                ·
                  refine ⟨133760512374715327647827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22828460778618082585229141 133760512374715327647827)
                  ·
                    rfl

theorem cell23_2344479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 9].length) (baseStart_2344479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344479 prefixEnd_2344479 := by exact prefixLift 2344479
  have htrace : WordTrace (prefixWord ++ tailWord_2344479) baseStart_2344479 baseEnd_2344479 := by
    simpa [prefixWord, tailWord_2344479, baseEnd_2344479] using wordTrace_append hprefix tailTrace_2344479
  have hstable : (prefixWord ++ tailWord_2344479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344479).length < 2 ^ (prefixWord ++ tailWord_2344479).sum := by decide
  have hdescent : baseEnd_2344479 < baseStart_2344479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344490 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_2344490 : Nat := 118140960795 + 2344490 * 2 ^ 59
def prefixEnd_2344490 : Nat := 4983230072969 + 3 ^ 40 * 2344490 * 2
def baseEnd_2344490 : Nat := 1203850259659637405792893

theorem tailTrace_2344490 : CollatzResearch.WordTrace tailWord_2344490 prefixEnd_2344490 1203850259659637405792893 := by
  unfold tailWord_2344490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21377643819080152964769731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57007050184213741239385949 21377643819080152964769731)
  ·
    refine ⟨32066465728620229447154597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21377643819080152964769731 32066465728620229447154597)
    ·
      refine ⟨6012462324116293021341487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32066465728620229447154597 6012462324116293021341487)
      ·
        refine ⟨9018693486174439532012231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6012462324116293021341487 9018693486174439532012231)
        ·
          refine ⟨13528040229261659298018347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9018693486174439532012231 13528040229261659298018347)
          ·
            refine ⟨20292060343892488947027521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13528040229261659298018347 20292060343892488947027521)
            ·
              refine ⟨15219045257919366710270641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20292060343892488947027521 15219045257919366710270641)
              ·
                refine ⟨11414283943439525032702981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15219045257919366710270641 11414283943439525032702981)
                ·
                  refine ⟨2140178239394910943631809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11414283943439525032702981 2140178239394910943631809)
                  ·
                    refine ⟨1605133679546183207723857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140178239394910943631809 1605133679546183207723857)
                    ·
                      refine ⟨1203850259659637405792893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605133679546183207723857 1203850259659637405792893)
                      ·
                        rfl

theorem cell23_2344490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_2344490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344490 prefixEnd_2344490 := by exact prefixLift 2344490
  have htrace : WordTrace (prefixWord ++ tailWord_2344490) baseStart_2344490 baseEnd_2344490 := by
    simpa [prefixWord, tailWord_2344490, baseEnd_2344490] using wordTrace_append hprefix tailTrace_2344490
  have hstable : (prefixWord ++ tailWord_2344490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344490).length < 2 ^ (prefixWord ++ tailWord_2344490).sum := by decide
  have hdescent : baseEnd_2344490 < baseStart_2344490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344494 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_2344494 : Nat := 118140960795 + 2344494 * 2 ^ 59
def prefixEnd_2344494 : Nat := 4983230072969 + 3 ^ 40 * 2344494 * 2
def baseEnd_2344494 : Nat := 1203852313582255390142875

theorem tailTrace_2344494 : CollatzResearch.WordTrace tailWord_2344494 prefixEnd_2344494 1203852313582255390142875 := by
  unfold tailWord_2344494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10688840146038265067778067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57007147445537413694816357 10688840146038265067778067)
  ·
    refine ⟨16033260219057397601667101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10688840146038265067778067 16033260219057397601667101)
    ·
      refine ⟨6012472582146524100625163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16033260219057397601667101 6012472582146524100625163)
      ·
        refine ⟨9018708873219786150937745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6012472582146524100625163 9018708873219786150937745)
        ·
          refine ⟨6764031654914839613203309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9018708873219786150937745 6764031654914839613203309)
          ·
            refine ⟨2536511870593064854951241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6764031654914839613203309 2536511870593064854951241)
            ·
              refine ⟨1902383902944798641213431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2536511870593064854951241 1902383902944798641213431)
              ·
                refine ⟨2853575854417197961820147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902383902944798641213431 2853575854417197961820147)
                ·
                  refine ⟨4280363781625796942730221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853575854417197961820147 4280363781625796942730221)
                  ·
                    refine ⟨1605136418109673853523833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4280363781625796942730221 1605136418109673853523833)
                    ·
                      refine ⟨1203852313582255390142875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605136418109673853523833 1203852313582255390142875)
                      ·
                        rfl

theorem cell23_2344494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_2344494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344494 prefixEnd_2344494 := by exact prefixLift 2344494
  have htrace : WordTrace (prefixWord ++ tailWord_2344494) baseStart_2344494 baseEnd_2344494 := by
    simpa [prefixWord, tailWord_2344494, baseEnd_2344494] using wordTrace_append hprefix tailTrace_2344494
  have hstable : (prefixWord ++ tailWord_2344494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344494).length < 2 ^ (prefixWord ++ tailWord_2344494).sum := by decide
  have hdescent : baseEnd_2344494 < baseStart_2344494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344506 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_2344506 : Nat := 118140960795 + 2344506 * 2 ^ 59
def prefixEnd_2344506 : Nat := 4983230072969 + 3 ^ 40 * 2344506 * 2
def baseEnd_2344506 : Nat := 1203858475350109343192819

theorem tailTrace_2344506 : CollatzResearch.WordTrace tailWord_2344506 prefixEnd_2344506 1203858475350109343192819 := by
  unfold tailWord_2344506
  simp only [CollatzResearch.WordTrace]
  refine ⟨21377789711065661647915343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57007439229508431061107581 21377789711065661647915343)
  ·
    refine ⟨32066684566598492471873015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21377789711065661647915343 32066684566598492471873015)
    ·
      refine ⟨48100026849897738707809523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32066684566598492471873015 48100026849897738707809523)
      ·
        refine ⟨72150040274846608061714285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48100026849897738707809523 72150040274846608061714285)
        ·
          refine ⟨27056265103067478023142857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72150040274846608061714285 27056265103067478023142857)
          ·
            refine ⟨20292198827300608517357143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27056265103067478023142857 20292198827300608517357143)
            ·
              refine ⟨30438298240950912776035715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20292198827300608517357143 30438298240950912776035715)
              ·
                refine ⟨45657447361426369164053573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30438298240950912776035715 45657447361426369164053573)
                ·
                  refine ⟨8560771380267444218260045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45657447361426369164053573 8560771380267444218260045)
                  ·
                    refine ⟨3210289267600291581847517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8560771380267444218260045 3210289267600291581847517)
                    ·
                      refine ⟨1203858475350109343192819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3210289267600291581847517 1203858475350109343192819)
                      ·
                        rfl

theorem cell23_2344506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_2344506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344506 prefixEnd_2344506 := by exact prefixLift 2344506
  have htrace : WordTrace (prefixWord ++ tailWord_2344506) baseStart_2344506 baseEnd_2344506 := by
    simpa [prefixWord, tailWord_2344506, baseEnd_2344506] using wordTrace_append hprefix tailTrace_2344506
  have hstable : (prefixWord ++ tailWord_2344506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344506).length < 2 ^ (prefixWord ++ tailWord_2344506).sum := by decide
  have hdescent : baseEnd_2344506 < baseStart_2344506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344513 : List Nat := [1, 2, 5, 1, 1, 1, 1, 6, 5]
def baseStart_2344513 : Nat := 118140960795 + 2344513 * 2 ^ 59
def prefixEnd_2344513 : Nat := 4983230072969 + 3 ^ 40 * 2344513 * 2
def baseEnd_2344513 : Nat := 133762452190521201756143

theorem tailTrace_2344513 : CollatzResearch.WordTrace tailWord_2344513 prefixEnd_2344513 133762452190521201756143 := by
  unfold tailWord_2344513
  simp only [CollatzResearch.WordTrace]
  refine ⟨85511414155237286787166193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57007609436824857858110795 85511414155237286787166193)
  ·
    refine ⟨64133560616427965090374645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85511414155237286787166193 64133560616427965090374645)
    ·
      refine ⟨6012521307790121727222623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64133560616427965090374645 6012521307790121727222623)
      ·
        refine ⟨9018781961685182590833935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6012521307790121727222623 9018781961685182590833935)
        ·
          refine ⟨13528172942527773886250903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9018781961685182590833935 13528172942527773886250903)
          ·
            refine ⟨20292259413791660829376355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13528172942527773886250903 20292259413791660829376355)
            ·
              refine ⟨30438389120687491244064533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20292259413791660829376355 30438389120687491244064533)
              ·
                refine ⟨1426799490032226152065525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30438389120687491244064533 1426799490032226152065525)
                ·
                  refine ⟨133762452190521201756143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426799490032226152065525 133762452190521201756143)
                  ·
                    rfl

theorem cell23_2344513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 5].length) (baseStart_2344513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344513 prefixEnd_2344513 := by exact prefixLift 2344513
  have htrace : WordTrace (prefixWord ++ tailWord_2344513) baseStart_2344513 baseEnd_2344513 := by
    simpa [prefixWord, tailWord_2344513, baseEnd_2344513] using wordTrace_append hprefix tailTrace_2344513
  have hstable : (prefixWord ++ tailWord_2344513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344513).length < 2 ^ (prefixWord ++ tailWord_2344513).sum := by decide
  have hdescent : baseEnd_2344513 < baseStart_2344513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344600 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2344600 : Nat := 118140960795 + 2344600 * 2 ^ 59
def prefixEnd_2344600 : Nat := 4983230072969 + 3 ^ 40 * 2344600 * 2
def baseEnd_2344600 : Nat := 1203906742531631975417387

theorem tailTrace_2344600 : CollatzResearch.WordTrace tailWord_2344600 prefixEnd_2344600 1203906742531631975417387 := by
  unfold tailWord_2344600
  simp only [CollatzResearch.WordTrace]
  refine ⟨42757293652961050322791627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57009724870614733763722169 42757293652961050322791627)
  ·
    refine ⟨64135940479441575484187441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42757293652961050322791627 64135940479441575484187441)
    ·
      refine ⟨48101955359581181613140581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64135940479441575484187441 48101955359581181613140581)
      ·
        refine ⟨9019116629921471552463859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48101955359581181613140581 9019116629921471552463859)
        ·
          refine ⟨13528674944882207328695789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9019116629921471552463859 13528674944882207328695789)
          ·
            refine ⟨5073253104330827748260921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13528674944882207328695789 5073253104330827748260921)
            ·
              refine ⟨3804939828248120811195691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073253104330827748260921 3804939828248120811195691)
              ·
                refine ⟨5707409742372181216793537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3804939828248120811195691 5707409742372181216793537)
                ·
                  refine ⟨4280557306779135912595153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5707409742372181216793537 4280557306779135912595153)
                  ·
                    refine ⟨3210417980084351934446365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4280557306779135912595153 3210417980084351934446365)
                    ·
                      refine ⟨1203906742531631975417387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3210417980084351934446365 1203906742531631975417387)
                      ·
                        rfl

theorem cell23_2344600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2344600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344600 prefixEnd_2344600 := by exact prefixLift 2344600
  have htrace : WordTrace (prefixWord ++ tailWord_2344600) baseStart_2344600 baseEnd_2344600 := by
    simpa [prefixWord, tailWord_2344600, baseEnd_2344600] using wordTrace_append hprefix tailTrace_2344600
  have hstable : (prefixWord ++ tailWord_2344600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344600).length < 2 ^ (prefixWord ++ tailWord_2344600).sum := by decide
  have hdescent : baseEnd_2344600 < baseStart_2344600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344656 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_2344656 : Nat := 118140960795 + 2344656 * 2 ^ 59
def prefixEnd_2344656 : Nat := 4983230072969 + 3 ^ 40 * 2344656 * 2
def baseEnd_2344656 : Nat := 1203935497448283756317129

theorem tailTrace_2344656 : CollatzResearch.WordTrace tailWord_2344656 prefixEnd_2344656 1203935497448283756317129 := by
  unfold tailWord_2344656
  simp only [CollatzResearch.WordTrace]
  refine ⟨42758314896859611104810911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57011086529146148139747881 42758314896859611104810911)
  ·
    refine ⟨64137472345289416657216367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42758314896859611104810911 64137472345289416657216367)
    ·
      refine ⟨96206208517934124985824551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64137472345289416657216367 96206208517934124985824551)
      ·
        refine ⟨144309312776901187478736827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96206208517934124985824551 144309312776901187478736827)
        ·
          refine ⟨216463969165351781218105241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144309312776901187478736827 216463969165351781218105241)
          ·
            refine ⟨162347976874013835913578931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216463969165351781218105241 162347976874013835913578931)
            ·
              refine ⟨243521965311020753870368397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162347976874013835913578931 243521965311020753870368397)
              ·
                refine ⟨91320736991632782701388149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243521965311020753870368397 91320736991632782701388149)
                ·
                  refine ⟨8561319092965573378255139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91320736991632782701388149 8561319092965573378255139)
                  ·
                    refine ⟨12841978639448360067382709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8561319092965573378255139 12841978639448360067382709)
                    ·
                      refine ⟨1203935497448283756317129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12841978639448360067382709 1203935497448283756317129)
                      ·
                        rfl

theorem cell23_2344656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_2344656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344656 prefixEnd_2344656 := by exact prefixLift 2344656
  have htrace : WordTrace (prefixWord ++ tailWord_2344656) baseStart_2344656 baseEnd_2344656 := by
    simpa [prefixWord, tailWord_2344656, baseEnd_2344656] using wordTrace_append hprefix tailTrace_2344656
  have hstable : (prefixWord ++ tailWord_2344656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344656).length < 2 ^ (prefixWord ++ tailWord_2344656).sum := by decide
  have hdescent : baseEnd_2344656 < baseStart_2344656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344657 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 2, 3, 2]
def baseStart_2344657 : Nat := 118140960795 + 2344657 * 2 ^ 59
def prefixEnd_2344657 : Nat := 4983230072969 + 3 ^ 40 * 2344657 * 2
def baseEnd_2344657 : Nat := 1203936010928938252404625

theorem tailTrace_2344657 : CollatzResearch.WordTrace tailWord_2344657 prefixEnd_2344657 1203936010928938252404625 := by
  unfold tailWord_2344657
  simp only [CollatzResearch.WordTrace]
  refine ⟨85516666266715599380408225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57011110844477066253605483 85516666266715599380408225)
  ·
    refine ⟨64137499700036699535306169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85516666266715599380408225 64137499700036699535306169)
    ·
      refine ⟨48103124775027524651479627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64137499700036699535306169 48103124775027524651479627)
      ·
        refine ⟨72154687162541286977219441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48103124775027524651479627 72154687162541286977219441)
        ·
          refine ⟨54116015371905965232914581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72154687162541286977219441 54116015371905965232914581)
          ·
            refine ⟨2536688220558092120292871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54116015371905965232914581 2536688220558092120292871)
            ·
              refine ⟨3805032330837138180439307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536688220558092120292871 3805032330837138180439307)
              ·
                refine ⟨5707548496255707270658961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805032330837138180439307 5707548496255707270658961)
                ·
                  refine ⟨4280661372191780452994221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5707548496255707270658961 4280661372191780452994221)
                  ·
                    refine ⟨1605248014571917669872833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4280661372191780452994221 1605248014571917669872833)
                    ·
                      refine ⟨1203936010928938252404625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605248014571917669872833 1203936010928938252404625)
                      ·
                        rfl

theorem cell23_2344657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_2344657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344657 prefixEnd_2344657 := by exact prefixLift 2344657
  have htrace : WordTrace (prefixWord ++ tailWord_2344657) baseStart_2344657 baseEnd_2344657 := by
    simpa [prefixWord, tailWord_2344657, baseEnd_2344657] using wordTrace_append hprefix tailTrace_2344657
  have hstable : (prefixWord ++ tailWord_2344657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344657).length < 2 ^ (prefixWord ++ tailWord_2344657).sum := by decide
  have hdescent : baseEnd_2344657 < baseStart_2344657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344663 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 4, 4]
def baseStart_2344663 : Nat := 118140960795 + 2344663 * 2 ^ 59
def prefixEnd_2344663 : Nat := 4983230072969 + 3 ^ 40 * 2344663 * 2
def baseEnd_2344663 : Nat := 401313030604288409643199

theorem tailTrace_2344663 : CollatzResearch.WordTrace tailWord_2344663 prefixEnd_2344663 401313030604288409643199 := by
  unfold tailWord_2344663
  simp only [CollatzResearch.WordTrace]
  refine ⟨85516885104693862405126643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57011256736462574936751095 85516885104693862405126643)
  ·
    refine ⟨128275327657040793607689965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85516885104693862405126643 128275327657040793607689965)
    ·
      refine ⟨48103247871390297602883737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128275327657040793607689965 48103247871390297602883737)
      ·
        refine ⟨36077435903542723202162803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48103247871390297602883737 36077435903542723202162803)
        ·
          refine ⟨54116153855314084803244205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36077435903542723202162803 54116153855314084803244205)
          ·
            refine ⟨20293557695742781801216577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54116153855314084803244205 20293557695742781801216577)
            ·
              refine ⟨15220168271807086350912433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20293557695742781801216577 15220168271807086350912433)
              ·
                refine ⟨11415126203855314763184325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15220168271807086350912433 11415126203855314763184325)
                ·
                  refine ⟨2140336163222871518097061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11415126203855314763184325 2140336163222871518097061)
                  ·
                    refine ⟨401313030604288409643199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140336163222871518097061 401313030604288409643199)
                    ·
                      rfl

theorem cell23_2344663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_2344663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344663 prefixEnd_2344663 := by exact prefixLift 2344663
  have htrace : WordTrace (prefixWord ++ tailWord_2344663) baseStart_2344663 baseEnd_2344663 := by
    simpa [prefixWord, tailWord_2344663, baseEnd_2344663] using wordTrace_append hprefix tailTrace_2344663
  have hstable : (prefixWord ++ tailWord_2344663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344663).length < 2 ^ (prefixWord ++ tailWord_2344663).sum := by decide
  have hdescent : baseEnd_2344663 < baseStart_2344663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344676 : List Nat := [2, 3, 1, 1, 1, 3, 12]
def baseStart_2344676 : Nat := 118140960795 + 2344676 * 2 ^ 59
def prefixEnd_2344676 : Nat := 4983230072969 + 3 ^ 40 * 2344676 * 2
def baseEnd_2344676 : Nat := 14863527988412020716877

theorem tailTrace_2344676 : CollatzResearch.WordTrace tailWord_2344676 prefixEnd_2344676 14863527988412020716877 := by
  unfold tailWord_2344676
  simp only [CollatzResearch.WordTrace]
  refine ⟨42758679626823382812674941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57011572835764510416899921 42758679626823382812674941)
  ·
    refine ⟨16034504860058768554753103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42758679626823382812674941 16034504860058768554753103)
    ·
      refine ⟨24051757290088152832129655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16034504860058768554753103 24051757290088152832129655)
      ·
        refine ⟨36077635935132229248194483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24051757290088152832129655 36077635935132229248194483)
        ·
          refine ⟨54116453902698343872291725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36077635935132229248194483 54116453902698343872291725)
          ·
            refine ⟨20293670213511878952109397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54116453902698343872291725 20293670213511878952109397)
            ·
              refine ⟨14863527988412020716877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 20293670213511878952109397 14863527988412020716877)
              ·
                rfl

theorem cell23_2344676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 12].length) (baseStart_2344676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344676 prefixEnd_2344676 := by exact prefixLift 2344676
  have htrace : WordTrace (prefixWord ++ tailWord_2344676) baseStart_2344676 baseEnd_2344676 := by
    simpa [prefixWord, tailWord_2344676, baseEnd_2344676] using wordTrace_append hprefix tailTrace_2344676
  have hstable : (prefixWord ++ tailWord_2344676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344676).length < 2 ^ (prefixWord ++ tailWord_2344676).sum := by decide
  have hdescent : baseEnd_2344676 < baseStart_2344676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344680 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 4, 4]
def baseStart_2344680 : Nat := 118140960795 + 2344680 * 2 ^ 59
def prefixEnd_2344680 : Nat := 4983230072969 + 3 ^ 40 * 2344680 * 2
def baseEnd_2344680 : Nat := 401315940327997220805673

theorem tailTrace_2344680 : CollatzResearch.WordTrace tailWord_2344680 prefixEnd_2344680 401315940327997220805673 := by
  unfold tailWord_2344680
  simp only [CollatzResearch.WordTrace]
  refine ⟨42758752572816137154247747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57011670097088182872330329 42758752572816137154247747)
  ·
    refine ⟨64138128859224205731371621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42758752572816137154247747 64138128859224205731371621)
    ·
      refine ⟨12025899161104538574632179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64138128859224205731371621 12025899161104538574632179)
      ·
        refine ⟨18038848741656807861948269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12025899161104538574632179 18038848741656807861948269)
        ·
          refine ⟨6764568278121302948230601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18038848741656807861948269 6764568278121302948230601)
          ·
            refine ⟨5073426208590977211172951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6764568278121302948230601 5073426208590977211172951)
            ·
              refine ⟨7610139312886465816759427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5073426208590977211172951 7610139312886465816759427)
              ·
                refine ⟨11415208969329698725139141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7610139312886465816759427 11415208969329698725139141)
                ·
                  refine ⟨2140351681749318510963589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11415208969329698725139141 2140351681749318510963589)
                  ·
                    refine ⟨401315940327997220805673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2140351681749318510963589 401315940327997220805673)
                    ·
                      rfl

theorem cell23_2344680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_2344680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344680 prefixEnd_2344680 := by exact prefixLift 2344680
  have htrace : WordTrace (prefixWord ++ tailWord_2344680) baseStart_2344680 baseEnd_2344680 := by
    simpa [prefixWord, tailWord_2344680, baseEnd_2344680] using wordTrace_append hprefix tailTrace_2344680
  have hstable : (prefixWord ++ tailWord_2344680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344680).length < 2 ^ (prefixWord ++ tailWord_2344680).sum := by decide
  have hdescent : baseEnd_2344680 < baseStart_2344680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344687 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 3, 2, 2]
def baseStart_2344687 : Nat := 118140960795 + 2344687 * 2 ^ 59
def prefixEnd_2344687 : Nat := 4983230072969 + 3 ^ 40 * 2344687 * 2
def baseEnd_2344687 : Nat := 1203951415348573135029487

theorem tailTrace_2344687 : CollatzResearch.WordTrace tailWord_2344687 prefixEnd_2344687 1203951415348573135029487 := by
  unfold tailWord_2344687
  simp only [CollatzResearch.WordTrace]
  refine ⟨85517760456606914504000315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57011840304404609669333543 85517760456606914504000315)
  ·
    refine ⟨128276640684910371756000473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85517760456606914504000315 128276640684910371756000473)
    ·
      refine ⟨96207480513682778817000355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128276640684910371756000473 96207480513682778817000355)
      ·
        refine ⟨144311220770524168225500533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96207480513682778817000355 144311220770524168225500533)
        ·
          refine ⟨13529176947236640771140675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144311220770524168225500533 13529176947236640771140675)
          ·
            refine ⟨20293765420854961156711013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13529176947236640771140675 20293765420854961156711013)
            ·
              refine ⟨3805081016410305216883315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20293765420854961156711013 3805081016410305216883315)
              ·
                refine ⟨5707621524615457825324973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805081016410305216883315 5707621524615457825324973)
                ·
                  refine ⟨2140358071730796684496865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5707621524615457825324973 2140358071730796684496865)
                  ·
                    refine ⟨1605268553798097513372649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140358071730796684496865 1605268553798097513372649)
                    ·
                      refine ⟨1203951415348573135029487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605268553798097513372649 1203951415348573135029487)
                      ·
                        rfl

theorem cell23_2344687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 2, 2].length) (baseStart_2344687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344687 prefixEnd_2344687 := by exact prefixLift 2344687
  have htrace : WordTrace (prefixWord ++ tailWord_2344687) baseStart_2344687 baseEnd_2344687 := by
    simpa [prefixWord, tailWord_2344687, baseEnd_2344687] using wordTrace_append hprefix tailTrace_2344687
  have hstable : (prefixWord ++ tailWord_2344687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344687).length < 2 ^ (prefixWord ++ tailWord_2344687).sum := by decide
  have hdescent : baseEnd_2344687 < baseStart_2344687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344696 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2344696 : Nat := 118140960795 + 2344696 * 2 ^ 59
def prefixEnd_2344696 : Nat := 4983230072969 + 3 ^ 40 * 2344696 * 2
def baseEnd_2344696 : Nat := 1203956036674463599816945

theorem tailTrace_2344696 : CollatzResearch.WordTrace tailWord_2344696 prefixEnd_2344696 1203956036674463599816945 := by
  unfold tailWord_2344696
  simp only [CollatzResearch.WordTrace]
  refine ⟨42759044356787154520538971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57012059142382872694051961 42759044356787154520538971)
  ·
    refine ⟨64138566535180731780808457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42759044356787154520538971 64138566535180731780808457)
    ·
      refine ⟨48103924901385548835606343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64138566535180731780808457 48103924901385548835606343)
      ·
        refine ⟨72155887352078323253409515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48103924901385548835606343 72155887352078323253409515)
        ·
          refine ⟨108233831028117484880114273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72155887352078323253409515 108233831028117484880114273)
          ·
            refine ⟨81175373271088113660085705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108233831028117484880114273 81175373271088113660085705)
            ·
              refine ⟨60881529953316085245064279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81175373271088113660085705 60881529953316085245064279)
              ·
                refine ⟨91322294929974127867596419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60881529953316085245064279 91322294929974127867596419)
                ·
                  refine ⟨136983442394961191801394629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91322294929974127867596419 136983442394961191801394629)
                  ·
                    refine ⟨25684395449055223462761493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136983442394961191801394629 25684395449055223462761493)
                    ·
                      refine ⟨1203956036674463599816945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25684395449055223462761493 1203956036674463599816945)
                      ·
                        rfl

theorem cell23_2344696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2344696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344696 prefixEnd_2344696 := by exact prefixLift 2344696
  have htrace : WordTrace (prefixWord ++ tailWord_2344696) baseStart_2344696 baseEnd_2344696 := by
    simpa [prefixWord, tailWord_2344696, baseEnd_2344696] using wordTrace_append hprefix tailTrace_2344696
  have hstable : (prefixWord ++ tailWord_2344696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344696).length < 2 ^ (prefixWord ++ tailWord_2344696).sum := by decide
  have hdescent : baseEnd_2344696 < baseStart_2344696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344754 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_2344754 : Nat := 118140960795 + 2344754 * 2 ^ 59
def prefixEnd_2344754 : Nat := 4983230072969 + 3 ^ 40 * 2344754 * 2
def baseEnd_2344754 : Nat := 1203985818552424372891679

theorem tailTrace_2344754 : CollatzResearch.WordTrace tailWord_2344754 prefixEnd_2344754 1203985818552424372891679 := by
  unfold tailWord_2344754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21380051036841046236672329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57013469431576123297792877 21380051036841046236672329)
  ·
    refine ⟨16035038277630784677504247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21380051036841046236672329 16035038277630784677504247)
    ·
      refine ⟨24052557416446177016256371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16035038277630784677504247 24052557416446177016256371)
      ·
        refine ⟨36078836124669265524384557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24052557416446177016256371 36078836124669265524384557)
        ·
          refine ⟨13529563546750974571644209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36078836124669265524384557 13529563546750974571644209)
          ·
            refine ⟨10147172660063230928733157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13529563546750974571644209 10147172660063230928733157)
            ·
              refine ⟨1902594873761855799137467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10147172660063230928733157 1902594873761855799137467)
              ·
                refine ⟨2853892310642783698706201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902594873761855799137467 2853892310642783698706201)
                ·
                  refine ⟨2140419232982087774029651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2853892310642783698706201 2140419232982087774029651)
                  ·
                    refine ⟨3210628849473131661044477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2140419232982087774029651 3210628849473131661044477)
                    ·
                      refine ⟨1203985818552424372891679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3210628849473131661044477 1203985818552424372891679)
                      ·
                        rfl

theorem cell23_2344754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_2344754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344754 prefixEnd_2344754 := by exact prefixLift 2344754
  have htrace : WordTrace (prefixWord ++ tailWord_2344754) baseStart_2344754 baseEnd_2344754 := by
    simpa [prefixWord, tailWord_2344754, baseEnd_2344754] using wordTrace_append hprefix tailTrace_2344754
  have hstable : (prefixWord ++ tailWord_2344754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344754).length < 2 ^ (prefixWord ++ tailWord_2344754).sum := by decide
  have hdescent : baseEnd_2344754 < baseStart_2344754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344794 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2]
def baseStart_2344794 : Nat := 118140960795 + 2344794 * 2 ^ 59
def prefixEnd_2344794 : Nat := 4983230072969 + 3 ^ 40 * 2344794 * 2
def baseEnd_2344794 : Nat := 1204006357778604216391495

theorem tailTrace_2344794 : CollatzResearch.WordTrace tailWord_2344794 prefixEnd_2344794 1204006357778604216391495 := by
  unfold tailWord_2344794
  simp only [CollatzResearch.WordTrace]
  refine ⟨21380415766804817944536359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57014442044812847852096957 21380415766804817944536359)
  ·
    refine ⟨32070623650207226916804539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21380415766804817944536359 32070623650207226916804539)
    ·
      refine ⟨48105935475310840375206809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32070623650207226916804539 48105935475310840375206809)
      ·
        refine ⟨36079451606483130281405107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48105935475310840375206809 36079451606483130281405107)
        ·
          refine ⟨54119177409724695422107661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36079451606483130281405107 54119177409724695422107661)
          ·
            refine ⟨20294691528646760783290373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54119177409724695422107661 20294691528646760783290373)
            ·
              refine ⟨3805254661621267646866945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20294691528646760783290373 3805254661621267646866945)
              ·
                refine ⟨2853940996215950735150209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805254661621267646866945 2853940996215950735150209)
                ·
                  refine ⟨2140455747161963051362657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2853940996215950735150209 2140455747161963051362657)
                  ·
                    refine ⟨1605341810371472288521993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140455747161963051362657 1605341810371472288521993)
                    ·
                      refine ⟨1204006357778604216391495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605341810371472288521993 1204006357778604216391495)
                      ·
                        rfl

theorem cell23_2344794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_2344794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344794 prefixEnd_2344794 := by exact prefixLift 2344794
  have htrace : WordTrace (prefixWord ++ tailWord_2344794) baseStart_2344794 baseEnd_2344794 := by
    simpa [prefixWord, tailWord_2344794, baseEnd_2344794] using wordTrace_append hprefix tailTrace_2344794
  have hstable : (prefixWord ++ tailWord_2344794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344794).length < 2 ^ (prefixWord ++ tailWord_2344794).sum := by decide
  have hdescent : baseEnd_2344794 < baseStart_2344794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344920 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 3, 5]
def baseStart_2344920 : Nat := 118140960795 + 2344920 * 2 ^ 59
def prefixEnd_2344920 : Nat := 4983230072969 + 3 ^ 40 * 2344920 * 2
def baseEnd_2344920 : Nat := 401357018780356907805305

theorem tailTrace_2344920 : CollatzResearch.WordTrace tailWord_2344920 prefixEnd_2344920 401357018780356907805305 := by
  unfold tailWord_2344920
  simp only [CollatzResearch.WordTrace]
  refine ⟨42763129332381397648616107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57017505776508530198154809 42763129332381397648616107)
  ·
    refine ⟨64144693998572096472924161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42763129332381397648616107 64144693998572096472924161)
    ·
      refine ⟨48108520498929072354693121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64144693998572096472924161 48108520498929072354693121)
      ·
        refine ⟨36081390374196804266019841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48108520498929072354693121 36081390374196804266019841)
        ·
          refine ⟨27061042780647603199514881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36081390374196804266019841 27061042780647603199514881)
          ·
            refine ⟨20295782085485702399636161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27061042780647603199514881 20295782085485702399636161)
            ·
              refine ⟨15221836564114276799727121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20295782085485702399636161 15221836564114276799727121)
              ·
                refine ⟨11416377423085707599795341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15221836564114276799727121 11416377423085707599795341)
                ·
                  refine ⟨4281141533657140349923253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11416377423085707599795341 4281141533657140349923253)
                  ·
                    refine ⟨401357018780356907805305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4281141533657140349923253 401357018780356907805305)
                    ·
                      rfl

theorem cell23_2344920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_2344920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344920 prefixEnd_2344920 := by exact prefixLift 2344920
  have htrace : WordTrace (prefixWord ++ tailWord_2344920) baseStart_2344920 baseEnd_2344920 := by
    simpa [prefixWord, tailWord_2344920, baseEnd_2344920] using wordTrace_append hprefix tailTrace_2344920
  have hstable : (prefixWord ++ tailWord_2344920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344920).length < 2 ^ (prefixWord ++ tailWord_2344920).sum := by decide
  have hdescent : baseEnd_2344920 < baseStart_2344920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344957 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_2344957 : Nat := 118140960795 + 2344957 * 2 ^ 59
def prefixEnd_2344957 : Nat := 4983230072969 + 3 ^ 40 * 2344957 * 2
def baseEnd_2344957 : Nat := 1204090055125287078653245

theorem tailTrace_2344957 : CollatzResearch.WordTrace tailWord_2344957 prefixEnd_2344957 1204090055125287078653245 := by
  unfold tailWord_2344957
  simp only [CollatzResearch.WordTrace]
  refine ⟨85527608165628750616329125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57018405443752500410886083 85527608165628750616329125)
  ·
    refine ⟨16036426531055390740561711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85527608165628750616329125 16036426531055390740561711)
    ·
      refine ⟨24054639796583086110842567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16036426531055390740561711 24054639796583086110842567)
      ·
        refine ⟨36081959694874629166263851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24054639796583086110842567 36081959694874629166263851)
        ·
          refine ⟨54122939542311943749395777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36081959694874629166263851 54122939542311943749395777)
          ·
            refine ⟨40592204656733957812046833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54122939542311943749395777 40592204656733957812046833)
            ·
              refine ⟨30444153492550468359035125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40592204656733957812046833 30444153492550468359035125)
              ·
                refine ⟨2854139389926606408659543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30444153492550468359035125 2854139389926606408659543)
                ·
                  refine ⟨4281209084889909612989315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854139389926606408659543 4281209084889909612989315)
                  ·
                    refine ⟨6421813627334864419483973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4281209084889909612989315 6421813627334864419483973)
                    ·
                      refine ⟨1204090055125287078653245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6421813627334864419483973 1204090055125287078653245)
                      ·
                        rfl

theorem cell23_2344957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_2344957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344957 prefixEnd_2344957 := by exact prefixLift 2344957
  have htrace : WordTrace (prefixWord ++ tailWord_2344957) baseStart_2344957 baseEnd_2344957 := by
    simpa [prefixWord, tailWord_2344957, baseEnd_2344957] using wordTrace_append hprefix tailTrace_2344957
  have hstable : (prefixWord ++ tailWord_2344957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344957).length < 2 ^ (prefixWord ++ tailWord_2344957).sum := by decide
  have hdescent : baseEnd_2344957 < baseStart_2344957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344960 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_2344960 : Nat := 118140960795 + 2344960 * 2 ^ 59
def prefixEnd_2344960 : Nat := 4983230072969 + 3 ^ 40 * 2344960 * 2
def baseEnd_2344960 : Nat := 1204091595567250566915731

theorem tailTrace_2344960 : CollatzResearch.WordTrace tailWord_2344960 prefixEnd_2344960 1204091595567250566915731 := by
  unfold tailWord_2344960
  simp only [CollatzResearch.WordTrace]
  refine ⟨42763858792308941064344167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57018478389745254752458889 42763858792308941064344167)
  ·
    refine ⟨64145788188463411596516251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42763858792308941064344167 64145788188463411596516251)
    ·
      refine ⟨96218682282695117394774377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64145788188463411596516251 96218682282695117394774377)
      ·
        refine ⟨72164011712021338046080783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96218682282695117394774377 72164011712021338046080783)
        ·
          refine ⟨108246017568032007069121175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72164011712021338046080783 108246017568032007069121175)
          ·
            refine ⟨162369026352048010603681763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108246017568032007069121175 162369026352048010603681763)
            ·
              refine ⟨243553539528072015905522645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162369026352048010603681763 243553539528072015905522645)
              ·
                refine ⟨5708286082689187872785687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 243553539528072015905522645 5708286082689187872785687)
                ·
                  refine ⟨8562429124033781809178531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5708286082689187872785687 8562429124033781809178531)
                  ·
                    refine ⟨12843643686050672713767797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8562429124033781809178531 12843643686050672713767797)
                    ·
                      refine ⟨1204091595567250566915731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12843643686050672713767797 1204091595567250566915731)
                      ·
                        rfl

theorem cell23_2344960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_2344960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344960 prefixEnd_2344960 := by exact prefixLift 2344960
  have htrace : WordTrace (prefixWord ++ tailWord_2344960) baseStart_2344960 baseEnd_2344960 := by
    simpa [prefixWord, tailWord_2344960, baseEnd_2344960] using wordTrace_append hprefix tailTrace_2344960
  have hstable : (prefixWord ++ tailWord_2344960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344960).length < 2 ^ (prefixWord ++ tailWord_2344960).sum := by decide
  have hdescent : baseEnd_2344960 < baseStart_2344960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344994 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_2344994 : Nat := 118140960795 + 2344994 * 2 ^ 59
def prefixEnd_2344994 : Nat := 4983230072969 + 3 ^ 40 * 2344994 * 2
def baseEnd_2344994 : Nat := 1204109053909503433890575

theorem tailTrace_2344994 : CollatzResearch.WordTrace tailWord_2344994 prefixEnd_2344994 1204109053909503433890575 := by
  unfold tailWord_2344994
  simp only [CollatzResearch.WordTrace]
  refine ⟨21382239416623676483856509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57019305110996470623617357 21382239416623676483856509)
  ·
    refine ⟨8018339781233878681446191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21382239416623676483856509 8018339781233878681446191)
    ·
      refine ⟨12027509671850818022169287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8018339781233878681446191 12027509671850818022169287)
      ·
        refine ⟨18041264507776227033253931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12027509671850818022169287 18041264507776227033253931)
        ·
          refine ⟨27061896761664340549880897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18041264507776227033253931 27061896761664340549880897)
          ·
            refine ⟨20296422571248255412410673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27061896761664340549880897 20296422571248255412410673)
            ·
              refine ⟨15222316928436191559308005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20296422571248255412410673 15222316928436191559308005)
              ·
                refine ⟨2854184424081785917370251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15222316928436191559308005 2854184424081785917370251)
                ·
                  refine ⟨4281276636122678876055377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854184424081785917370251 4281276636122678876055377)
                  ·
                    refine ⟨3210957477092009157041533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4281276636122678876055377 3210957477092009157041533)
                    ·
                      refine ⟨1204109053909503433890575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3210957477092009157041533 1204109053909503433890575)
                      ·
                        rfl

theorem cell23_2344994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_2344994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344994 prefixEnd_2344994 := by exact prefixLift 2344994
  have htrace : WordTrace (prefixWord ++ tailWord_2344994) baseStart_2344994 baseEnd_2344994 := by
    simpa [prefixWord, tailWord_2344994, baseEnd_2344994] using wordTrace_append hprefix tailTrace_2344994
  have hstable : (prefixWord ++ tailWord_2344994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344994).length < 2 ^ (prefixWord ++ tailWord_2344994).sum := by decide
  have hdescent : baseEnd_2344994 < baseStart_2344994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344997 : List Nat := [1, 3, 1, 2, 2, 4, 3, 7]
def baseStart_2344997 : Nat := 118140960795 + 2344997 * 2 ^ 59
def prefixEnd_2344997 : Nat := 4983230072969 + 3 ^ 40 * 2344997 * 2
def baseEnd_2344997 : Nat := 44596688679683960079743

theorem tailTrace_2344997 : CollatzResearch.WordTrace tailWord_2344997 prefixEnd_2344997 44596688679683960079743 := by
  unfold tailWord_2344997
  simp only [CollatzResearch.WordTrace]
  refine ⟨85529067085483837447785245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57019378056989224965190163 85529067085483837447785245)
  ·
    refine ⟨32073400157056439042919467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85529067085483837447785245 32073400157056439042919467)
    ·
      refine ⟨48110100235584658564379201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32073400157056439042919467 48110100235584658564379201)
      ·
        refine ⟨36082575176688493923284401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48110100235584658564379201 36082575176688493923284401)
        ·
          refine ⟨27061931382516370442463301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36082575176688493923284401 27061931382516370442463301)
          ·
            refine ⟨5074112134221819457961869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27061931382516370442463301 5074112134221819457961869)
            ·
              refine ⟨1902792050333182296735701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5074112134221819457961869 1902792050333182296735701)
              ·
                refine ⟨44596688679683960079743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1902792050333182296735701 44596688679683960079743)
                ·
                  rfl

theorem cell23_2344997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 7].length) (baseStart_2344997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2344997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2344997 prefixEnd_2344997 := by exact prefixLift 2344997
  have htrace : WordTrace (prefixWord ++ tailWord_2344997) baseStart_2344997 baseEnd_2344997 := by
    simpa [prefixWord, tailWord_2344997, baseEnd_2344997] using wordTrace_append hprefix tailTrace_2344997
  have hstable : (prefixWord ++ tailWord_2344997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344997).length < 2 ^ (prefixWord ++ tailWord_2344997).sum := by decide
  have hdescent : baseEnd_2344997 < baseStart_2344997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345008 : List Nat := [2, 1, 1, 1, 2, 6, 2, 3, 1, 2, 2]
def baseStart_2345008 : Nat := 118140960795 + 2345008 * 2 ^ 59
def prefixEnd_2345008 : Nat := 4983230072969 + 3 ^ 40 * 2345008 * 2
def baseEnd_2345008 : Nat := 1204116242638666379115511

theorem tailTrace_2345008 : CollatzResearch.WordTrace tailWord_2345008 prefixEnd_2345008 1204116242638666379115511 := by
  unfold tailWord_2345008
  simp only [CollatzResearch.WordTrace]
  refine ⟨42764734144221993163217839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57019645525629324217623785 42764734144221993163217839)
  ·
    refine ⟨64147101216332989744826759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42764734144221993163217839 64147101216332989744826759)
    ·
      refine ⟨96220651824499484617240139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64147101216332989744826759 96220651824499484617240139)
      ·
        refine ⟨144330977736749226925860209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96220651824499484617240139 144330977736749226925860209)
        ·
          refine ⟨108248233302561920194395157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144330977736749226925860209 108248233302561920194395157)
          ·
            refine ⟨5074135936057590009112273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108248233302561920194395157 5074135936057590009112273)
            ·
              refine ⟨3805601952043192506834205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5074135936057590009112273 3805601952043192506834205)
              ·
                refine ⟨1427100732016197190062827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3805601952043192506834205 1427100732016197190062827)
                ·
                  refine ⟨2140651098024295785094241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427100732016197190062827 2140651098024295785094241)
                  ·
                    refine ⟨1605488323518221838820681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140651098024295785094241 1605488323518221838820681)
                    ·
                      refine ⟨1204116242638666379115511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605488323518221838820681 1204116242638666379115511)
                      ·
                        rfl

theorem cell23_2345008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 2, 2].length) (baseStart_2345008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345008 prefixEnd_2345008 := by exact prefixLift 2345008
  have htrace : WordTrace (prefixWord ++ tailWord_2345008) baseStart_2345008 baseEnd_2345008 := by
    simpa [prefixWord, tailWord_2345008, baseEnd_2345008] using wordTrace_append hprefix tailTrace_2345008
  have hstable : (prefixWord ++ tailWord_2345008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345008).length < 2 ^ (prefixWord ++ tailWord_2345008).sum := by decide
  have hdescent : baseEnd_2345008 < baseStart_2345008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345024 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 4, 1, 3]
def baseStart_2345024 : Nat := 118140960795 + 2345024 * 2 ^ 59
def prefixEnd_2345024 : Nat := 4983230072969 + 3 ^ 40 * 2345024 * 2
def baseEnd_2345024 : Nat := 1204124458329138316515437

theorem tailTrace_2345024 : CollatzResearch.WordTrace tailWord_2345024 prefixEnd_2345024 1204124458329138316515437 := by
  unfold tailWord_2345024
  simp only [CollatzResearch.WordTrace]
  refine ⟨42765025928193010529509063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57020034570924014039345417 42765025928193010529509063)
  ·
    refine ⟨64147538892289515794263595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42765025928193010529509063 64147538892289515794263595)
    ·
      refine ⟨96221308338434273691395393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64147538892289515794263595 96221308338434273691395393)
      ·
        refine ⟨72165981253825705268546545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96221308338434273691395393 72165981253825705268546545)
        ·
          refine ⟨54124485940369278951409909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72165981253825705268546545 54124485940369278951409909)
          ·
            refine ⟨5074170556909619901694679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54124485940369278951409909 5074170556909619901694679)
            ·
              refine ⟨7611255835364429852542019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074170556909619901694679 7611255835364429852542019)
              ·
                refine ⟨11416883753046644778813029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7611255835364429852542019 11416883753046644778813029)
                ·
                  refine ⟨2140665703696245896027443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11416883753046644778813029 2140665703696245896027443)
                  ·
                    refine ⟨3210998555544368844041165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2140665703696245896027443 3210998555544368844041165)
                    ·
                      refine ⟨1204124458329138316515437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3210998555544368844041165 1204124458329138316515437)
                      ·
                        rfl

theorem cell23_2345024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_2345024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345024 prefixEnd_2345024 := by exact prefixLift 2345024
  have htrace : WordTrace (prefixWord ++ tailWord_2345024) baseStart_2345024 baseEnd_2345024 := by
    simpa [prefixWord, tailWord_2345024, baseEnd_2345024] using wordTrace_append hprefix tailTrace_2345024
  have hstable : (prefixWord ++ tailWord_2345024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345024).length < 2 ^ (prefixWord ++ tailWord_2345024).sum := by decide
  have hdescent : baseEnd_2345024 < baseStart_2345024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345080 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2345080 : Nat := 118140960795 + 2345080 * 2 ^ 59
def prefixEnd_2345080 : Nat := 4983230072969 + 3 ^ 40 * 2345080 * 2
def baseEnd_2345080 : Nat := 1204153213245790097415179

theorem tailTrace_2345080 : CollatzResearch.WordTrace tailWord_2345080 prefixEnd_2345080 1204153213245790097415179 := by
  unfold tailWord_2345080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42766047172091571311528347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57021396229455428415371129 42766047172091571311528347)
  ·
    refine ⟨64149070758137356967292521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42766047172091571311528347 64149070758137356967292521)
    ·
      refine ⟨48111803068603017725469391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64149070758137356967292521 48111803068603017725469391)
      ·
        refine ⟨72167704602904526588204087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48111803068603017725469391 72167704602904526588204087)
        ·
          refine ⟨108251556904356789882306131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72167704602904526588204087 108251556904356789882306131)
          ·
            refine ⟨162377335356535184823459197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108251556904356789882306131 162377335356535184823459197)
            ·
              refine ⟨60891500758700694308797199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162377335356535184823459197 60891500758700694308797199)
              ·
                refine ⟨91337251138051041463195799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60891500758700694308797199 91337251138051041463195799)
                ·
                  refine ⟨137005876707076562194793699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91337251138051041463195799 137005876707076562194793699)
                  ·
                    refine ⟨205508815060614843292190549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137005876707076562194793699 205508815060614843292190549)
                    ·
                      refine ⟨1204153213245790097415179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 205508815060614843292190549 1204153213245790097415179)
                      ·
                        rfl

theorem cell23_2345080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2345080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345080 prefixEnd_2345080 := by exact prefixLift 2345080
  have htrace : WordTrace (prefixWord ++ tailWord_2345080) baseStart_2345080 baseEnd_2345080 := by
    simpa [prefixWord, tailWord_2345080, baseEnd_2345080] using wordTrace_append hprefix tailTrace_2345080
  have hstable : (prefixWord ++ tailWord_2345080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345080).length < 2 ^ (prefixWord ++ tailWord_2345080).sum := by decide
  have hdescent : baseEnd_2345080 < baseStart_2345080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345081 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 4, 2, 2]
def baseStart_2345081 : Nat := 118140960795 + 2345081 * 2 ^ 59
def prefixEnd_2345081 : Nat := 4983230072969 + 3 ^ 40 * 2345081 * 2
def baseEnd_2345081 : Nat := 1204153726726444593502675

theorem tailTrace_2345081 : CollatzResearch.WordTrace tailWord_2345081 prefixEnd_2345081 1204153726726444593502675 := by
  unfold tailWord_2345081
  simp only [CollatzResearch.WordTrace]
  refine ⟨85532130817179519793843097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57021420544786346529228731 85532130817179519793843097)
  ·
    refine ⟨64149098112884639845382323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85532130817179519793843097 64149098112884639845382323)
    ·
      refine ⟨96223647169326959768073485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64149098112884639845382323 96223647169326959768073485)
      ·
        refine ⟨36083867688497609913027557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96223647169326959768073485 36083867688497609913027557)
        ·
          refine ⟨6765725191593301858692667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36083867688497609913027557 6765725191593301858692667)
          ·
            refine ⟨10148587787389952788039001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765725191593301858692667 10148587787389952788039001)
            ·
              refine ⟨7611440840542464591029251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10148587787389952788039001 7611440840542464591029251)
              ·
                refine ⟨11417161260813696886543877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7611440840542464591029251 11417161260813696886543877)
                ·
                  refine ⟨2140717736402568166226977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11417161260813696886543877 2140717736402568166226977)
                  ·
                    refine ⟨1605538302301926124670233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140717736402568166226977 1605538302301926124670233)
                    ·
                      refine ⟨1204153726726444593502675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605538302301926124670233 1204153726726444593502675)
                      ·
                        rfl

theorem cell23_2345081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_2345081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345081 prefixEnd_2345081 := by exact prefixLift 2345081
  have htrace : WordTrace (prefixWord ++ tailWord_2345081) baseStart_2345081 baseEnd_2345081 := by
    simpa [prefixWord, tailWord_2345081, baseEnd_2345081] using wordTrace_append hprefix tailTrace_2345081
  have hstable : (prefixWord ++ tailWord_2345081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345081).length < 2 ^ (prefixWord ++ tailWord_2345081).sum := by decide
  have hdescent : baseEnd_2345081 < baseStart_2345081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345097 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 3]
def baseStart_2345097 : Nat := 118140960795 + 2345097 * 2 ^ 59
def prefixEnd_2345097 : Nat := 4983230072969 + 3 ^ 40 * 2345097 * 2
def baseEnd_2345097 : Nat := 1204161942416916530902601

theorem tailTrace_2345097 : CollatzResearch.WordTrace tailWord_2345097 prefixEnd_2345097 1204161942416916530902601 := by
  unfold tailWord_2345097
  simp only [CollatzResearch.WordTrace]
  refine ⟨85532714385121554526425545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57021809590081036350950363 85532714385121554526425545)
  ·
    refine ⟨64149535788841165894819159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85532714385121554526425545 64149535788841165894819159)
    ·
      refine ⟨96224303683261748842228739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64149535788841165894819159 96224303683261748842228739)
      ·
        refine ⟨144336455524892623263343109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96224303683261748842228739 144336455524892623263343109)
        ·
          refine ⟨27063085410917366861876833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144336455524892623263343109 27063085410917366861876833)
          ·
            refine ⟨20297314058188025146407625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27063085410917366861876833 20297314058188025146407625)
            ·
              refine ⟨15222985543641018859805719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20297314058188025146407625 15222985543641018859805719)
              ·
                refine ⟨22834478315461528289708579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15222985543641018859805719 22834478315461528289708579)
                ·
                  refine ⟨34251717473192292434562869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22834478315461528289708579 34251717473192292434562869)
                  ·
                    refine ⟨3211098513111777415740269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34251717473192292434562869 3211098513111777415740269)
                    ·
                      refine ⟨1204161942416916530902601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3211098513111777415740269 1204161942416916530902601)
                      ·
                        rfl

theorem cell23_2345097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_2345097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345097 prefixEnd_2345097 := by exact prefixLift 2345097
  have htrace : WordTrace (prefixWord ++ tailWord_2345097) baseStart_2345097 baseEnd_2345097 := by
    simpa [prefixWord, tailWord_2345097, baseEnd_2345097] using wordTrace_append hprefix tailTrace_2345097
  have hstable : (prefixWord ++ tailWord_2345097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345097).length < 2 ^ (prefixWord ++ tailWord_2345097).sum := by decide
  have hdescent : baseEnd_2345097 < baseStart_2345097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345098 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_2345098 : Nat := 118140960795 + 2345098 * 2 ^ 59
def prefixEnd_2345098 : Nat := 4983230072969 + 3 ^ 40 * 2345098 * 2
def baseEnd_2345098 : Nat := 1204162455897571026990097

theorem tailTrace_2345098 : CollatzResearch.WordTrace tailWord_2345098 prefixEnd_2345098 1204162455897571026990097 := by
  unfold tailWord_2345098
  simp only [CollatzResearch.WordTrace]
  refine ⟨21383187714529482924302987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57021833905411954464807965 21383187714529482924302987)
  ·
    refine ⟨32074781571794224386454481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21383187714529482924302987 32074781571794224386454481)
    ·
      refine ⟨24056086178845668289840861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32074781571794224386454481 24056086178845668289840861)
      ·
        refine ⟨9021032317067125608690323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24056086178845668289840861 9021032317067125608690323)
        ·
          refine ⟨13531548475600688413035485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9021032317067125608690323 13531548475600688413035485)
          ·
            refine ⟨5074330678350258154888307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13531548475600688413035485 5074330678350258154888307)
            ·
              refine ⟨7611496017525387232332461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074330678350258154888307 7611496017525387232332461)
              ·
                refine ⟨2854311006572020212124673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7611496017525387232332461 2854311006572020212124673)
                ·
                  refine ⟨2140733254929015159093505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2854311006572020212124673 2140733254929015159093505)
                  ·
                    refine ⟨1605549941196761369320129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140733254929015159093505 1605549941196761369320129)
                    ·
                      refine ⟨1204162455897571026990097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605549941196761369320129 1204162455897571026990097)
                      ·
                        rfl

theorem cell23_2345098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_2345098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345098 prefixEnd_2345098 := by exact prefixLift 2345098
  have htrace : WordTrace (prefixWord ++ tailWord_2345098) baseStart_2345098 baseEnd_2345098 := by
    simpa [prefixWord, tailWord_2345098, baseEnd_2345098] using wordTrace_append hprefix tailTrace_2345098
  have hstable : (prefixWord ++ tailWord_2345098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345098).length < 2 ^ (prefixWord ++ tailWord_2345098).sum := by decide
  have hdescent : baseEnd_2345098 < baseStart_2345098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345214 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2345214 : Nat := 118140960795 + 2345214 * 2 ^ 59
def prefixEnd_2345214 : Nat := 4983230072969 + 3 ^ 40 * 2345214 * 2
def baseEnd_2345214 : Nat := 1204222019653492573139563

theorem tailTrace_2345214 : CollatzResearch.WordTrace tailWord_2345214 prefixEnd_2345214 1204222019653492573139563 := by
  unfold tailWord_2345214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10692122715712210438554337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57024654483798455672289797 10692122715712210438554337)
  ·
    refine ⟨8019092036784157828915753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10692122715712210438554337 8019092036784157828915753)
    ·
      refine ⟨6014319027588118371686815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8019092036784157828915753 6014319027588118371686815)
      ·
        refine ⟨9021478541382177557530223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6014319027588118371686815 9021478541382177557530223)
        ·
          refine ⟨13532217812073266336295335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9021478541382177557530223 13532217812073266336295335)
          ·
            refine ⟨20298326718109899504443003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13532217812073266336295335 20298326718109899504443003)
            ·
              refine ⟨30447490077164849256664505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20298326718109899504443003 30447490077164849256664505)
              ·
                refine ⟨22835617557873636942498379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30447490077164849256664505 22835617557873636942498379)
                ·
                  refine ⟨34253426336810455413747569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22835617557873636942498379 34253426336810455413747569)
                  ·
                    refine ⟨25690069752607841560310677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34253426336810455413747569 25690069752607841560310677)
                    ·
                      refine ⟨1204222019653492573139563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25690069752607841560310677 1204222019653492573139563)
                      ·
                        rfl

theorem cell23_2345214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2345214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345214 prefixEnd_2345214 := by exact prefixLift 2345214
  have htrace : WordTrace (prefixWord ++ tailWord_2345214) baseStart_2345214 baseEnd_2345214 := by
    simpa [prefixWord, tailWord_2345214, baseEnd_2345214] using wordTrace_append hprefix tailTrace_2345214
  have hstable : (prefixWord ++ tailWord_2345214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345214).length < 2 ^ (prefixWord ++ tailWord_2345214).sum := by decide
  have hdescent : baseEnd_2345214 < baseStart_2345214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345244 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2345244 : Nat := 118140960795 + 2345244 * 2 ^ 59
def prefixEnd_2345244 : Nat := 4983230072969 + 3 ^ 40 * 2345244 * 2
def baseEnd_2345244 : Nat := 1204237424073127455764425

theorem tailTrace_2345244 : CollatzResearch.WordTrace tailWord_2345244 prefixEnd_2345244 1204237424073127455764425 := by
  unfold tailWord_2345244
  simp only [CollatzResearch.WordTrace]
  refine ⟨42769037957794499316013393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57025383943725999088017857 42769037957794499316013393)
  ·
    refine ⟨32076778468345874487010045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42769037957794499316013393 32076778468345874487010045)
    ·
      refine ⟨12028791925629702932628767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32076778468345874487010045 12028791925629702932628767)
      ·
        refine ⟨18043187888444554398943151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12028791925629702932628767 18043187888444554398943151)
        ·
          refine ⟨27064781832666831598414727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18043187888444554398943151 27064781832666831598414727)
          ·
            refine ⟨40597172749000247397622091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27064781832666831598414727 40597172749000247397622091)
            ·
              refine ⟨60895759123500371096433137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40597172749000247397622091 60895759123500371096433137)
              ·
                refine ⟨45671819342625278322324853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60895759123500371096433137 45671819342625278322324853)
                ·
                  refine ⟨4281733063371119842717955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45671819342625278322324853 4281733063371119842717955)
                  ·
                    refine ⟨6422599595056679764076933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4281733063371119842717955 6422599595056679764076933)
                    ·
                      refine ⟨1204237424073127455764425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6422599595056679764076933 1204237424073127455764425)
                      ·
                        rfl

theorem cell23_2345244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2345244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345244 prefixEnd_2345244 := by exact prefixLift 2345244
  have htrace : WordTrace (prefixWord ++ tailWord_2345244) baseStart_2345244 baseEnd_2345244 := by
    simpa [prefixWord, tailWord_2345244, baseEnd_2345244] using wordTrace_append hprefix tailTrace_2345244
  have hstable : (prefixWord ++ tailWord_2345244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345244).length < 2 ^ (prefixWord ++ tailWord_2345244).sum := by decide
  have hdescent : baseEnd_2345244 < baseStart_2345244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345248 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2345248 : Nat := 118140960795 + 2345248 * 2 ^ 59
def prefixEnd_2345248 : Nat := 4983230072969 + 3 ^ 40 * 2345248 * 2
def baseEnd_2345248 : Nat := 1204239477995745440114407

theorem tailTrace_2345248 : CollatzResearch.WordTrace tailWord_2345248 prefixEnd_2345248 1204239477995745440114407 := by
  unfold tailWord_2345248
  simp only [CollatzResearch.WordTrace]
  refine ⟨42769110903787253657586199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57025481205049671543448265 42769110903787253657586199)
  ·
    refine ⟨64153666355680880486379299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42769110903787253657586199 64153666355680880486379299)
    ·
      refine ⟨96230499533521320729568949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64153666355680880486379299 96230499533521320729568949)
      ·
        refine ⟨9021609331267623818397089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96230499533521320729568949 9021609331267623818397089)
        ·
          refine ⟨6766206998450717863797817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9021609331267623818397089 6766206998450717863797817)
          ·
            refine ⟨5074655248838038397848363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6766206998450717863797817 5074655248838038397848363)
            ·
              refine ⟨7611982873257057596772545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074655248838038397848363 7611982873257057596772545)
              ·
                refine ⟨5708987154942793197579409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7611982873257057596772545 5708987154942793197579409)
                ·
                  refine ⟨4281740366207094898184557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5708987154942793197579409 4281740366207094898184557)
                  ·
                    refine ⟨1605652637327660586819209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4281740366207094898184557 1605652637327660586819209)
                    ·
                      refine ⟨1204239477995745440114407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605652637327660586819209 1204239477995745440114407)
                      ·
                        rfl

theorem cell23_2345248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2345248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345248 prefixEnd_2345248 := by exact prefixLift 2345248
  have htrace : WordTrace (prefixWord ++ tailWord_2345248) baseStart_2345248 baseEnd_2345248 := by
    simpa [prefixWord, tailWord_2345248, baseEnd_2345248] using wordTrace_append hprefix tailTrace_2345248
  have hstable : (prefixWord ++ tailWord_2345248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345248).length < 2 ^ (prefixWord ++ tailWord_2345248).sum := by decide
  have hdescent : baseEnd_2345248 < baseStart_2345248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345262 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_2345262 : Nat := 118140960795 + 2345262 * 2 ^ 59
def prefixEnd_2345262 : Nat := 4983230072969 + 3 ^ 40 * 2345262 * 2
def baseEnd_2345262 : Nat := 133805185191656487259927

theorem tailTrace_2345262 : CollatzResearch.WordTrace tailWord_2345262 prefixEnd_2345262 133805185191656487259927 := by
  unfold tailWord_2345262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10692341553690473463272755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57025821619682525137454693 10692341553690473463272755)
  ·
    refine ⟨16038512330535710194909133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10692341553690473463272755 16038512330535710194909133)
    ·
      refine ⟨6014442123950891323090925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16038512330535710194909133 6014442123950891323090925)
      ·
        refine ⟨2255415796481584246159097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6014442123950891323090925 2255415796481584246159097)
        ·
          refine ⟨1691561847361188184619323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2255415796481584246159097 1691561847361188184619323)
          ·
            refine ⟨2537342771041782276928985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691561847361188184619323 2537342771041782276928985)
            ·
              refine ⟨1903007078281336707696739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2537342771041782276928985 1903007078281336707696739)
              ·
                refine ⟨2854510617422005061545109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903007078281336707696739 2854510617422005061545109)
                ·
                  refine ⟨133805185191656487259927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2854510617422005061545109 133805185191656487259927)
                  ·
                    rfl

theorem cell23_2345262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_2345262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345262 prefixEnd_2345262 := by exact prefixLift 2345262
  have htrace : WordTrace (prefixWord ++ tailWord_2345262) baseStart_2345262 baseEnd_2345262 := by
    simpa [prefixWord, tailWord_2345262, baseEnd_2345262] using wordTrace_append hprefix tailTrace_2345262
  have hstable : (prefixWord ++ tailWord_2345262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345262).length < 2 ^ (prefixWord ++ tailWord_2345262).sum := by decide
  have hdescent : baseEnd_2345262 < baseStart_2345262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345274 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_2345274 : Nat := 118140960795 + 2345274 * 2 ^ 59
def prefixEnd_2345274 : Nat := 4983230072969 + 3 ^ 40 * 2345274 * 2
def baseEnd_2345274 : Nat := 1204252828492762338389287

theorem tailTrace_2345274 : CollatzResearch.WordTrace tailWord_2345274 prefixEnd_2345274 1204252828492762338389287 := by
  unfold tailWord_2345274
  simp only [CollatzResearch.WordTrace]
  refine ⟨21384792526370078438904719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57026113403653542503745917 21384792526370078438904719)
  ·
    refine ⟨32077188789555117658357079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21384792526370078438904719 32077188789555117658357079)
    ·
      refine ⟨48115783184332676487535619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32077188789555117658357079 48115783184332676487535619)
      ·
        refine ⟨72173674776499014731303429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48115783184332676487535619 72173674776499014731303429)
        ·
          refine ⟨13532564020593565262119393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72173674776499014731303429 13532564020593565262119393)
          ·
            refine ⟨10149423015445173946589545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13532564020593565262119393 10149423015445173946589545)
            ·
              refine ⟨7612067261583880459942159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10149423015445173946589545 7612067261583880459942159)
              ·
                refine ⟨11418100892375820689913239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7612067261583880459942159 11418100892375820689913239)
                ·
                  refine ⟨17127151338563731034869859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11418100892375820689913239 17127151338563731034869859)
                  ·
                    refine ⟨25690727007845596552304789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17127151338563731034869859 25690727007845596552304789)
                    ·
                      refine ⟨1204252828492762338389287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25690727007845596552304789 1204252828492762338389287)
                      ·
                        rfl

theorem cell23_2345274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_2345274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345274 prefixEnd_2345274 := by exact prefixLift 2345274
  have htrace : WordTrace (prefixWord ++ tailWord_2345274) baseStart_2345274 baseEnd_2345274 := by
    simpa [prefixWord, tailWord_2345274, baseEnd_2345274] using wordTrace_append hprefix tailTrace_2345274
  have hstable : (prefixWord ++ tailWord_2345274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345274).length < 2 ^ (prefixWord ++ tailWord_2345274).sum := by decide
  have hdescent : baseEnd_2345274 < baseStart_2345274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345278 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_2345278 : Nat := 118140960795 + 2345278 * 2 ^ 59
def prefixEnd_2345278 : Nat := 4983230072969 + 3 ^ 40 * 2345278 * 2
def baseEnd_2345278 : Nat := 1204254882415380322739269

theorem tailTrace_2345278 : CollatzResearch.WordTrace tailWord_2345278 prefixEnd_2345278 1204254882415380322739269 := by
  unfold tailWord_2345278
  simp only [CollatzResearch.WordTrace]
  refine ⟨10692414499683227804845561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57026210664977214959176325 10692414499683227804845561)
  ·
    refine ⟨8019310874762420853634171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10692414499683227804845561 8019310874762420853634171)
    ·
      refine ⟨12028966312143631280451257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8019310874762420853634171 12028966312143631280451257)
      ·
        refine ⟨9021724734107723460338443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12028966312143631280451257 9021724734107723460338443)
        ·
          refine ⟨13532587101161585190507665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9021724734107723460338443 13532587101161585190507665)
          ·
            refine ⟨10149440325871188892880749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13532587101161585190507665 10149440325871188892880749)
            ·
              refine ⟨3806040122201695834830281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10149440325871188892880749 3806040122201695834830281)
              ·
                refine ⟨2854530091651271876122711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3806040122201695834830281 2854530091651271876122711)
                ·
                  refine ⟨4281795137476907814184067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854530091651271876122711 4281795137476907814184067)
                  ·
                    refine ⟨6422692706215361721276101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4281795137476907814184067 6422692706215361721276101)
                    ·
                      refine ⟨1204254882415380322739269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6422692706215361721276101 1204254882415380322739269)
                      ·
                        rfl

theorem cell23_2345278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_2345278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345278 prefixEnd_2345278 := by exact prefixLift 2345278
  have htrace : WordTrace (prefixWord ++ tailWord_2345278) baseStart_2345278 baseEnd_2345278 := by
    simpa [prefixWord, tailWord_2345278, baseEnd_2345278] using wordTrace_append hprefix tailTrace_2345278
  have hstable : (prefixWord ++ tailWord_2345278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345278).length < 2 ^ (prefixWord ++ tailWord_2345278).sum := by decide
  have hdescent : baseEnd_2345278 < baseStart_2345278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345311 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 3]
def baseStart_2345311 : Nat := 118140960795 + 2345311 * 2 ^ 59
def prefixEnd_2345311 : Nat := 4983230072969 + 3 ^ 40 * 2345311 * 2
def baseEnd_2345311 : Nat := 1204271827276978693626617

theorem tailTrace_2345311 : CollatzResearch.WordTrace tailWord_2345311 prefixEnd_2345311 1204271827276978693626617 := by
  unfold tailWord_2345311
  simp only [CollatzResearch.WordTrace]
  refine ⟨85540519606346269074715787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57027013070897512716477191 85540519606346269074715787)
  ·
    refine ⟨128310779409519403612073681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85540519606346269074715787 128310779409519403612073681)
    ·
      refine ⟨96233084557139552709055261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128310779409519403612073681 96233084557139552709055261)
      ·
        refine ⟨36087406708927332265895723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96233084557139552709055261 36087406708927332265895723)
        ·
          refine ⟨54131110063390998398843585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36087406708927332265895723 54131110063390998398843585)
          ·
            refine ⟨40598332547543248799132689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54131110063390998398843585 40598332547543248799132689)
            ·
              refine ⟨30448749410657436599349517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40598332547543248799132689 30448749410657436599349517)
              ·
                refine ⟨11418281028996538724756069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30448749410657436599349517 11418281028996538724756069)
                ·
                  refine ⟨2140927692936851010891763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11418281028996538724756069 2140927692936851010891763)
                  ·
                    refine ⟨3211391539405276516337645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2140927692936851010891763 3211391539405276516337645)
                    ·
                      refine ⟨1204271827276978693626617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3211391539405276516337645 1204271827276978693626617)
                      ·
                        rfl

theorem cell23_2345311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_2345311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345311 prefixEnd_2345311 := by exact prefixLift 2345311
  have htrace : WordTrace (prefixWord ++ tailWord_2345311) baseStart_2345311 baseEnd_2345311 := by
    simpa [prefixWord, tailWord_2345311, baseEnd_2345311] using wordTrace_append hprefix tailTrace_2345311
  have hstable : (prefixWord ++ tailWord_2345311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345311).length < 2 ^ (prefixWord ++ tailWord_2345311).sum := by decide
  have hdescent : baseEnd_2345311 < baseStart_2345311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345312 : List Nat := [2, 1, 1, 3, 5, 1, 1, 4, 1, 2, 2]
def baseStart_2345312 : Nat := 118140960795 + 2345312 * 2 ^ 59
def prefixEnd_2345312 : Nat := 4983230072969 + 3 ^ 40 * 2345312 * 2
def baseEnd_2345312 : Nat := 1204272340757633189714113

theorem tailTrace_2345312 : CollatzResearch.WordTrace tailWord_2345312 prefixEnd_2345312 1204272340757633189714113 := by
  unfold tailWord_2345312
  simp only [CollatzResearch.WordTrace]
  refine ⟨42770278039671323122751095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57027037386228430830334793 42770278039671323122751095)
  ·
    refine ⟨64155417059506984684126643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42770278039671323122751095 64155417059506984684126643)
    ·
      refine ⟨96233125589260477026189965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64155417059506984684126643 96233125589260477026189965)
      ·
        refine ⟨36087422095972678884821237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96233125589260477026189965 36087422095972678884821237)
        ·
          refine ⟨3383195821497438645451991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36087422095972678884821237 3383195821497438645451991)
          ·
            refine ⟨5074793732246157968177987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383195821497438645451991 5074793732246157968177987)
            ·
              refine ⟨7612190598369236952266981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074793732246157968177987 7612190598369236952266981)
              ·
                refine ⟨1427285737194231928550059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7612190598369236952266981 1427285737194231928550059)
                ·
                  refine ⟨2140928605791347892825089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427285737194231928550059 2140928605791347892825089)
                  ·
                    refine ⟨1605696454343510919618817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140928605791347892825089 1605696454343510919618817)
                    ·
                      refine ⟨1204272340757633189714113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605696454343510919618817 1204272340757633189714113)
                      ·
                        rfl

theorem cell23_2345312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_2345312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345312 prefixEnd_2345312 := by exact prefixLift 2345312
  have htrace : WordTrace (prefixWord ++ tailWord_2345312) baseStart_2345312 baseEnd_2345312 := by
    simpa [prefixWord, tailWord_2345312, baseEnd_2345312] using wordTrace_append hprefix tailTrace_2345312
  have hstable : (prefixWord ++ tailWord_2345312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345312).length < 2 ^ (prefixWord ++ tailWord_2345312).sum := by decide
  have hdescent : baseEnd_2345312 < baseStart_2345312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345321 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 5, 3, 2]
def baseStart_2345321 : Nat := 118140960795 + 2345321 * 2 ^ 59
def prefixEnd_2345321 : Nat := 4983230072969 + 3 ^ 40 * 2345321 * 2
def baseEnd_2345321 : Nat := 1204276962083523654501571

theorem tailTrace_2345321 : CollatzResearch.WordTrace tailWord_2345321 prefixEnd_2345321 1204276962083523654501571 := by
  unfold tailWord_2345321
  simp only [CollatzResearch.WordTrace]
  refine ⟨85540884336310040782579817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57027256224206693855053211 85540884336310040782579817)
  ·
    refine ⟨64155663252232530586934863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85540884336310040782579817 64155663252232530586934863)
    ·
      refine ⟨96233494878348795880402295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64155663252232530586934863 96233494878348795880402295)
      ·
        refine ⟨144350242317523193820603443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96233494878348795880402295 144350242317523193820603443)
        ·
          refine ⟨216525363476284790730905165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144350242317523193820603443 216525363476284790730905165)
          ·
            refine ⟨81197011303606796524089437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216525363476284790730905165 81197011303606796524089437)
            ·
              refine ⟨30448879238852548696533539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81197011303606796524089437 30448879238852548696533539)
              ·
                refine ⟨45673318858278823044800309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30448879238852548696533539 45673318858278823044800309)
                ·
                  refine ⟨4281873642963639660450029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45673318858278823044800309 4281873642963639660450029)
                  ·
                    refine ⟨1605702616111364872668761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4281873642963639660450029 1605702616111364872668761)
                    ·
                      refine ⟨1204276962083523654501571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605702616111364872668761 1204276962083523654501571)
                      ·
                        rfl

theorem cell23_2345321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 3, 2].length) (baseStart_2345321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345321 prefixEnd_2345321 := by exact prefixLift 2345321
  have htrace : WordTrace (prefixWord ++ tailWord_2345321) baseStart_2345321 baseEnd_2345321 := by
    simpa [prefixWord, tailWord_2345321, baseEnd_2345321] using wordTrace_append hprefix tailTrace_2345321
  have hstable : (prefixWord ++ tailWord_2345321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345321).length < 2 ^ (prefixWord ++ tailWord_2345321).sum := by decide
  have hdescent : baseEnd_2345321 < baseStart_2345321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345328 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 2, 1, 3]
def baseStart_2345328 : Nat := 118140960795 + 2345328 * 2 ^ 59
def prefixEnd_2345328 : Nat := 4983230072969 + 3 ^ 40 * 2345328 * 2
def baseEnd_2345328 : Nat := 1204280556448105127114039

theorem tailTrace_2345328 : CollatzResearch.WordTrace tailWord_2345328 prefixEnd_2345328 1204280556448105127114039 := by
  unfold tailWord_2345328
  simp only [CollatzResearch.WordTrace]
  refine ⟨42770569823642340489042319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57027426431523120652056425 42770569823642340489042319)
  ·
    refine ⟨64155854735463510733563479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42770569823642340489042319 64155854735463510733563479)
    ·
      refine ⟨96233782103195266100345219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64155854735463510733563479 96233782103195266100345219)
      ·
        refine ⟨144350673154792899150517829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96233782103195266100345219 144350673154792899150517829)
        ·
          refine ⟨27065751216523668590722093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144350673154792899150517829 27065751216523668590722093)
          ·
            refine ⟨10149656706196375721520785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27065751216523668590722093 10149656706196375721520785)
            ·
              refine ⟨7612242529647281791140589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10149656706196375721520785 7612242529647281791140589)
              ·
                refine ⟨2854590948617730671677721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7612242529647281791140589 2854590948617730671677721)
                ·
                  refine ⟨2140943211463298003758291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2854590948617730671677721 2140943211463298003758291)
                  ·
                    refine ⟨3211414817194947005637437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2140943211463298003758291 3211414817194947005637437)
                    ·
                      refine ⟨1204280556448105127114039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3211414817194947005637437 1204280556448105127114039)
                      ·
                        rfl

theorem cell23_2345328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 1, 3].length) (baseStart_2345328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345328 prefixEnd_2345328 := by exact prefixLift 2345328
  have htrace : WordTrace (prefixWord ++ tailWord_2345328) baseStart_2345328 baseEnd_2345328 := by
    simpa [prefixWord, tailWord_2345328, baseEnd_2345328] using wordTrace_append hprefix tailTrace_2345328
  have hstable : (prefixWord ++ tailWord_2345328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345328).length < 2 ^ (prefixWord ++ tailWord_2345328).sum := by decide
  have hdescent : baseEnd_2345328 < baseStart_2345328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345346 : List Nat := [3, 4, 2, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_2345346 : Nat := 118140960795 + 2345346 * 2 ^ 59
def prefixEnd_2345346 : Nat := 4983230072969 + 3 ^ 40 * 2345346 * 2
def baseEnd_2345346 : Nat := 1204289799099886056688957

theorem tailTrace_2345346 : CollatzResearch.WordTrace tailWord_2345346 prefixEnd_2345346 1204289799099886056688957 := by
  unfold tailWord_2345346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21385449040304867513059973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57027864107479646701493261 21385449040304867513059973)
  ·
    refine ⟨4009771695057162658698745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21385449040304867513059973 4009771695057162658698745)
    ·
      refine ⟨3007328771292871994024059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4009771695057162658698745 3007328771292871994024059)
      ·
        refine ⟨4510993156939307991036089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007328771292871994024059 4510993156939307991036089)
        ·
          refine ⟨3383244867704480993277067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4510993156939307991036089 3383244867704480993277067)
          ·
            refine ⟨5074867301556721489915601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383244867704480993277067 5074867301556721489915601)
            ·
              refine ⟨3806150476167541117436701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5074867301556721489915601 3806150476167541117436701)
              ·
                refine ⟨1427306428562827919038763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3806150476167541117436701 1427306428562827919038763)
                ·
                  refine ⟨2140959642844241878558145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427306428562827919038763 2140959642844241878558145)
                  ·
                    refine ⟨1605719732133181408918609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140959642844241878558145 1605719732133181408918609)
                    ·
                      refine ⟨1204289799099886056688957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605719732133181408918609 1204289799099886056688957)
                      ·
                        rfl

theorem cell23_2345346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_2345346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345346 prefixEnd_2345346 := by exact prefixLift 2345346
  have htrace : WordTrace (prefixWord ++ tailWord_2345346) baseStart_2345346 baseEnd_2345346 := by
    simpa [prefixWord, tailWord_2345346, baseEnd_2345346] using wordTrace_append hprefix tailTrace_2345346
  have hstable : (prefixWord ++ tailWord_2345346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345346).length < 2 ^ (prefixWord ++ tailWord_2345346).sum := by decide
  have hdescent : baseEnd_2345346 < baseStart_2345346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345355 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 1, 3, 2]
def baseStart_2345355 : Nat := 118140960795 + 2345355 * 2 ^ 59
def prefixEnd_2345355 : Nat := 4983230072969 + 3 ^ 40 * 2345355 * 2
def baseEnd_2345355 : Nat := 1204294420425776521476415

theorem tailTrace_2345355 : CollatzResearch.WordTrace tailWord_2345355 prefixEnd_2345355 1204294420425776521476415 := by
  unfold tailWord_2345355
  simp only [CollatzResearch.WordTrace]
  refine ⟨85542124418186864589317519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57028082945457909726211679 85542124418186864589317519)
  ·
    refine ⟨128313186627280296883976279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85542124418186864589317519 128313186627280296883976279)
    ·
      refine ⟨192469779940920445325964419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128313186627280296883976279 192469779940920445325964419)
      ·
        refine ⟨288704669911380667988946629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192469779940920445325964419 288704669911380667988946629)
        ·
          refine ⟨54132125608383875247927493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288704669911380667988946629 54132125608383875247927493)
          ·
            refine ⟨10149773551571976608986405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54132125608383875247927493 10149773551571976608986405)
            ·
              refine ⟨1903082540919745614184951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10149773551571976608986405 1903082540919745614184951)
              ·
                refine ⟨2854623811379618421277427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903082540919745614184951 2854623811379618421277427)
                ·
                  refine ⟨4281935717069427631916141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854623811379618421277427 4281935717069427631916141)
                  ·
                    refine ⟨1605725893901035361968553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4281935717069427631916141 1605725893901035361968553)
                    ·
                      refine ⟨1204294420425776521476415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605725893901035361968553 1204294420425776521476415)
                      ·
                        rfl

theorem cell23_2345355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 3, 2].length) (baseStart_2345355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345355 prefixEnd_2345355 := by exact prefixLift 2345355
  have htrace : WordTrace (prefixWord ++ tailWord_2345355) baseStart_2345355 baseEnd_2345355 := by
    simpa [prefixWord, tailWord_2345355, baseEnd_2345355] using wordTrace_append hprefix tailTrace_2345355
  have hstable : (prefixWord ++ tailWord_2345355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345355).length < 2 ^ (prefixWord ++ tailWord_2345355).sum := by decide
  have hdescent : baseEnd_2345355 < baseStart_2345355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345411 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 1, 7, 2]
def baseStart_2345411 : Nat := 118140960795 + 2345411 * 2 ^ 59
def prefixEnd_2345411 : Nat := 4983230072969 + 3 ^ 40 * 2345411 * 2
def baseEnd_2345411 : Nat := 1204323175342428302376157

theorem tailTrace_2345411 : CollatzResearch.WordTrace tailWord_2345411 prefixEnd_2345411 1204323175342428302376157 := by
  unfold tailWord_2345411
  simp only [CollatzResearch.WordTrace]
  refine ⟨85544166905983986153356087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57029444603989324102237391 85544166905983986153356087)
  ·
    refine ⟨128316250358975979230034131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85544166905983986153356087 128316250358975979230034131)
    ·
      refine ⟨192474375538463968845051197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128316250358975979230034131 192474375538463968845051197)
      ·
        refine ⟨72177890826923988316894199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192474375538463968845051197 72177890826923988316894199)
        ·
          refine ⟨108266836240385982475341299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72177890826923988316894199 108266836240385982475341299)
          ·
            refine ⟨162400254360578973713011949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108266836240385982475341299 162400254360578973713011949)
            ·
              refine ⟨60900095385217115142379481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162400254360578973713011949 60900095385217115142379481)
              ·
                refine ⟨45675071538912836356784611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60900095385217115142379481 45675071538912836356784611)
                ·
                  refine ⟨68512607308369254535176917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45675071538912836356784611 68512607308369254535176917)
                  ·
                    refine ⟨1605764233789904403168209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 68512607308369254535176917 1605764233789904403168209)
                    ·
                      refine ⟨1204323175342428302376157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605764233789904403168209 1204323175342428302376157)
                      ·
                        rfl

theorem cell23_2345411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_2345411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345411 prefixEnd_2345411 := by exact prefixLift 2345411
  have htrace : WordTrace (prefixWord ++ tailWord_2345411) baseStart_2345411 baseEnd_2345411 := by
    simpa [prefixWord, tailWord_2345411, baseEnd_2345411] using wordTrace_append hprefix tailTrace_2345411
  have hstable : (prefixWord ++ tailWord_2345411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345411).length < 2 ^ (prefixWord ++ tailWord_2345411).sum := by decide
  have hdescent : baseEnd_2345411 < baseStart_2345411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345441 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_2345441 : Nat := 118140960795 + 2345441 * 2 ^ 59
def prefixEnd_2345441 : Nat := 4983230072969 + 3 ^ 40 * 2345441 * 2
def baseEnd_2345441 : Nat := 1204338579762063185001019

theorem tailTrace_2345441 : CollatzResearch.WordTrace tailWord_2345441 prefixEnd_2345441 1204338579762063185001019 := by
  unfold tailWord_2345441
  simp only [CollatzResearch.WordTrace]
  refine ⟨85545261095875301276948177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57030174063916867517965451 85545261095875301276948177)
  ·
    refine ⟨64158945821906475957711133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85545261095875301276948177 64158945821906475957711133)
    ·
      refine ⟨24059604683214928484141675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64158945821906475957711133 24059604683214928484141675)
      ·
        refine ⟨36089407024822392726212513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24059604683214928484141675 36089407024822392726212513)
        ·
          refine ⟨27067055268616794544659385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36089407024822392726212513 27067055268616794544659385)
          ·
            refine ⟨20300291451462595908494539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27067055268616794544659385 20300291451462595908494539)
            ·
              refine ⟨30450437177193893862741809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20300291451462595908494539 30450437177193893862741809)
              ·
                refine ⟨22837827882895420397056357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30450437177193893862741809 22837827882895420397056357)
                ·
                  refine ⟨4282092728042891324448067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22837827882895420397056357 4282092728042891324448067)
                  ·
                    refine ⟨6423139092064336986672101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4282092728042891324448067 6423139092064336986672101)
                    ·
                      refine ⟨1204338579762063185001019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6423139092064336986672101 1204338579762063185001019)
                      ·
                        rfl

theorem cell23_2345441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_2345441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345441 prefixEnd_2345441 := by exact prefixLift 2345441
  have htrace : WordTrace (prefixWord ++ tailWord_2345441) baseStart_2345441 baseEnd_2345441 := by
    simpa [prefixWord, tailWord_2345441, baseEnd_2345441] using wordTrace_append hprefix tailTrace_2345441
  have hstable : (prefixWord ++ tailWord_2345441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345441).length < 2 ^ (prefixWord ++ tailWord_2345441).sum := by decide
  have hdescent : baseEnd_2345441 < baseStart_2345441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345451 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 5, 4]
def baseStart_2345451 : Nat := 118140960795 + 2345451 * 2 ^ 59
def prefixEnd_2345451 : Nat := 4983230072969 + 3 ^ 40 * 2345451 * 2
def baseEnd_2345451 : Nat := 401447904856202715291991

theorem tailTrace_2345451 : CollatzResearch.WordTrace tailWord_2345451 prefixEnd_2345451 401447904856202715291991 := by
  unfold tailWord_2345451
  simp only [CollatzResearch.WordTrace]
  refine ⟨85545625825839072984812207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57030417217226048656541471 85545625825839072984812207)
  ·
    refine ⟨128318438738758609477218311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85545625825839072984812207 128318438738758609477218311)
    ·
      refine ⟨192477658108137914215827467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128318438738758609477218311 192477658108137914215827467)
      ·
        refine ⟨288716487162206871323741201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192477658108137914215827467 288716487162206871323741201)
        ·
          refine ⟨216537365371655153492805901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288716487162206871323741201 216537365371655153492805901)
          ·
            refine ⟨81201512014370682559802213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216537365371655153492805901 81201512014370682559802213)
            ·
              refine ⟨15225283502694502979962915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81201512014370682559802213 15225283502694502979962915)
              ·
                refine ⟨22837925254041754469944373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15225283502694502979962915 22837925254041754469944373)
                ·
                  refine ⟨2141055492566414481557285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22837925254041754469944373 2141055492566414481557285)
                  ·
                    refine ⟨401447904856202715291991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2141055492566414481557285 401447904856202715291991)
                    ·
                      rfl

theorem cell23_2345451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 4].length) (baseStart_2345451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345451 prefixEnd_2345451 := by exact prefixLift 2345451
  have htrace : WordTrace (prefixWord ++ tailWord_2345451) baseStart_2345451 baseEnd_2345451 := by
    simpa [prefixWord, tailWord_2345451, baseEnd_2345451] using wordTrace_append hprefix tailTrace_2345451
  have hstable : (prefixWord ++ tailWord_2345451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345451).length < 2 ^ (prefixWord ++ tailWord_2345451).sum := by decide
  have hdescent : baseEnd_2345451 < baseStart_2345451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345492 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2345492 : Nat := 118140960795 + 2345492 * 2 ^ 59
def prefixEnd_2345492 : Nat := 4983230072969 + 3 ^ 40 * 2345492 * 2
def baseEnd_2345492 : Nat := 1204364767275442485463285

theorem tailTrace_2345492 : CollatzResearch.WordTrace tailWord_2345492 prefixEnd_2345492 1204364767275442485463285 := by
  unfold tailWord_2345492
  simp only [CollatzResearch.WordTrace]
  refine ⟨42773560609345268493527365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57031414145793691324703153 42773560609345268493527365)
  ·
    refine ⟨8020042614252237842536381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42773560609345268493527365 8020042614252237842536381)
    ·
      refine ⟨3007515980344589190951143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8020042614252237842536381 3007515980344589190951143)
      ·
        refine ⟨4511273970516883786426715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007515980344589190951143 4511273970516883786426715)
        ·
          refine ⟨6766910955775325679640073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511273970516883786426715 6766910955775325679640073)
          ·
            refine ⟨5075183216831494259730055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6766910955775325679640073 5075183216831494259730055)
            ·
              refine ⟨7612774825247241389595083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5075183216831494259730055 7612774825247241389595083)
              ·
                refine ⟨11419162237870862084392625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7612774825247241389595083 11419162237870862084392625)
                ·
                  refine ⟨8564371678403146563294469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11419162237870862084392625 8564371678403146563294469)
                  ·
                    refine ⟨1605819689700589980617713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8564371678403146563294469 1605819689700589980617713)
                    ·
                      refine ⟨1204364767275442485463285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605819689700589980617713 1204364767275442485463285)
                      ·
                        rfl

theorem cell23_2345492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2345492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345492 prefixEnd_2345492 := by exact prefixLift 2345492
  have htrace : WordTrace (prefixWord ++ tailWord_2345492) baseStart_2345492 baseEnd_2345492 := by
    simpa [prefixWord, tailWord_2345492, baseEnd_2345492] using wordTrace_append hprefix tailTrace_2345492
  have hstable : (prefixWord ++ tailWord_2345492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345492).length < 2 ^ (prefixWord ++ tailWord_2345492).sum := by decide
  have hdescent : baseEnd_2345492 < baseStart_2345492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345512 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2345512 : Nat := 118140960795 + 2345512 * 2 ^ 59
def prefixEnd_2345512 : Nat := 4983230072969 + 3 ^ 40 * 2345512 * 2
def baseEnd_2345512 : Nat := 1204375036888532407213193

theorem tailTrace_2345512 : CollatzResearch.WordTrace tailWord_2345512 prefixEnd_2345512 1204375036888532407213193 := by
  unfold tailWord_2345512
  simp only [CollatzResearch.WordTrace]
  refine ⟨42773925339309040201391395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57031900452412053601855193 42773925339309040201391395)
  ·
    refine ⟨64160888008963560302087093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42773925339309040201391395 64160888008963560302087093)
    ·
      refine ⟨6015083250840333778320665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64160888008963560302087093 6015083250840333778320665)
      ·
        refine ⟨4511312438130250333740499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6015083250840333778320665 4511312438130250333740499)
        ·
          refine ⟨6766968657195375500610749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511312438130250333740499 6766968657195375500610749)
          ·
            refine ⟨2537613246448265812729031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6766968657195375500610749 2537613246448265812729031)
            ·
              refine ⟨3806419869672398719093547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537613246448265812729031 3806419869672398719093547)
              ·
                refine ⟨5709629804508598078640321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806419869672398719093547 5709629804508598078640321)
                ·
                  refine ⟨4282222353381448558980241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5709629804508598078640321 4282222353381448558980241)
                  ·
                    refine ⟨3211666765036086419235181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4282222353381448558980241 3211666765036086419235181)
                    ·
                      refine ⟨1204375036888532407213193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3211666765036086419235181 1204375036888532407213193)
                      ·
                        rfl

theorem cell23_2345512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2345512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345512 prefixEnd_2345512 := by exact prefixLift 2345512
  have htrace : WordTrace (prefixWord ++ tailWord_2345512) baseStart_2345512 baseEnd_2345512 := by
    simpa [prefixWord, tailWord_2345512, baseEnd_2345512] using wordTrace_append hprefix tailTrace_2345512
  have hstable : (prefixWord ++ tailWord_2345512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345512).length < 2 ^ (prefixWord ++ tailWord_2345512).sum := by decide
  have hdescent : baseEnd_2345512 < baseStart_2345512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345528 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 1, 5]
def baseStart_2345528 : Nat := 118140960795 + 2345528 * 2 ^ 59
def prefixEnd_2345528 : Nat := 4983230072969 + 3 ^ 40 * 2345528 * 2
def baseEnd_2345528 : Nat := 401461084193001448204373

theorem tailTrace_2345528 : CollatzResearch.WordTrace tailWord_2345528 prefixEnd_2345528 401461084193001448204373 := by
  unfold tailWord_2345528
  simp only [CollatzResearch.WordTrace]
  refine ⟨42774217123280057567682619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57032289497706743423576825 42774217123280057567682619)
  ·
    refine ⟨64161325684920086351523929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42774217123280057567682619 64161325684920086351523929)
    ·
      refine ⟨48120994263690064763642947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64161325684920086351523929 48120994263690064763642947)
      ·
        refine ⟨72181491395535097145464421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48120994263690064763642947 72181491395535097145464421)
        ·
          refine ⟨13534029636662830714774579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72181491395535097145464421 13534029636662830714774579)
          ·
            refine ⟨20301044454994246072161869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13534029636662830714774579 20301044454994246072161869)
            ·
              refine ⟨7612891670622842277060701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20301044454994246072161869 7612891670622842277060701)
              ·
                refine ⟨2854834376483565853897763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7612891670622842277060701 2854834376483565853897763)
                ·
                  refine ⟨4282251564725348780846645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854834376483565853897763 4282251564725348780846645)
                  ·
                    refine ⟨401461084193001448204373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4282251564725348780846645 401461084193001448204373)
                    ·
                      rfl

theorem cell23_2345528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_2345528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345528 prefixEnd_2345528 := by exact prefixLift 2345528
  have htrace : WordTrace (prefixWord ++ tailWord_2345528) baseStart_2345528 baseEnd_2345528 := by
    simpa [prefixWord, tailWord_2345528, baseEnd_2345528] using wordTrace_append hprefix tailTrace_2345528
  have hstable : (prefixWord ++ tailWord_2345528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345528).length < 2 ^ (prefixWord ++ tailWord_2345528).sum := by decide
  have hdescent : baseEnd_2345528 < baseStart_2345528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345551 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_2345551 : Nat := 118140960795 + 2345551 * 2 ^ 59
def prefixEnd_2345551 : Nat := 4983230072969 + 3 ^ 40 * 2345551 * 2
def baseEnd_2345551 : Nat := 1204395062634057754625513

theorem tailTrace_2345551 : CollatzResearch.WordTrace tailWord_2345551 prefixEnd_2345551 1204395062634057754625513 := by
  unfold tailWord_2345551
  simp only [CollatzResearch.WordTrace]
  refine ⟨85549273125476790063452507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57032848750317860042301671 85549273125476790063452507)
  ·
    refine ⟨128323909688215185095178761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85549273125476790063452507 128323909688215185095178761)
    ·
      refine ⟨96242932266161388821384071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128323909688215185095178761 96242932266161388821384071)
      ·
        refine ⟨144364398399242083232076107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96242932266161388821384071 144364398399242083232076107)
        ·
          refine ⟨216546597598863124848114161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144364398399242083232076107 216546597598863124848114161)
          ·
            refine ⟨162409948199147343636085621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216546597598863124848114161 162409948199147343636085621)
            ·
              refine ⟨15225932643670063465883027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162409948199147343636085621 15225932643670063465883027)
              ·
                refine ⟨22838898965505095198824541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15225932643670063465883027 22838898965505095198824541)
                ·
                  refine ⟨8564587112064410699559203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22838898965505095198824541 8564587112064410699559203)
                  ·
                    refine ⟨12846880668096616049338805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8564587112064410699559203 12846880668096616049338805)
                    ·
                      refine ⟨1204395062634057754625513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12846880668096616049338805 1204395062634057754625513)
                      ·
                        rfl

theorem cell23_2345551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_2345551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345551 prefixEnd_2345551 := by exact prefixLift 2345551
  have htrace : WordTrace (prefixWord ++ tailWord_2345551) baseStart_2345551 baseEnd_2345551 := by
    simpa [prefixWord, tailWord_2345551, baseEnd_2345551] using wordTrace_append hprefix tailTrace_2345551
  have hstable : (prefixWord ++ tailWord_2345551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345551).length < 2 ^ (prefixWord ++ tailWord_2345551).sum := by decide
  have hdescent : baseEnd_2345551 < baseStart_2345551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345568 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 3]
def baseStart_2345568 : Nat := 118140960795 + 2345568 * 2 ^ 59
def prefixEnd_2345568 : Nat := 4983230072969 + 3 ^ 40 * 2345568 * 2
def baseEnd_2345568 : Nat := 1204403791805184188112935

theorem tailTrace_2345568 : CollatzResearch.WordTrace tailWord_2345568 prefixEnd_2345568 1204403791805184188112935 := by
  unfold tailWord_2345568
  simp only [CollatzResearch.WordTrace]
  refine ⟨42774946583207600983410679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57033262110943467977880905 42774946583207600983410679)
  ·
    refine ⟨64162419874811401475116019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42774946583207600983410679 64162419874811401475116019)
    ·
      refine ⟨96243629812217102212674029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64162419874811401475116019 96243629812217102212674029)
      ·
        refine ⟨36091361179581413329752761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96243629812217102212674029 36091361179581413329752761)
        ·
          refine ⟨27068520884686059997314571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36091361179581413329752761 27068520884686059997314571)
          ·
            refine ⟨40602781327029089995971857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27068520884686059997314571 40602781327029089995971857)
            ·
              refine ⟨30452085995271817496978893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40602781327029089995971857 30452085995271817496978893)
              ·
                refine ⟨11419532248226931561367085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30452085995271817496978893 11419532248226931561367085)
                ·
                  refine ⟨4282324593085099335512657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11419532248226931561367085 4282324593085099335512657)
                  ·
                    refine ⟨3211743444813824501634493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4282324593085099335512657 3211743444813824501634493)
                    ·
                      refine ⟨1204403791805184188112935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3211743444813824501634493 1204403791805184188112935)
                      ·
                        rfl

theorem cell23_2345568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_2345568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345568 prefixEnd_2345568 := by exact prefixLift 2345568
  have htrace : WordTrace (prefixWord ++ tailWord_2345568) baseStart_2345568 baseEnd_2345568 := by
    simpa [prefixWord, tailWord_2345568, baseEnd_2345568] using wordTrace_append hprefix tailTrace_2345568
  have hstable : (prefixWord ++ tailWord_2345568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345568).length < 2 ^ (prefixWord ++ tailWord_2345568).sum := by decide
  have hdescent : baseEnd_2345568 < baseStart_2345568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345571 : List Nat := [1, 1, 1, 5, 1, 2, 3, 9]
def baseStart_2345571 : Nat := 118140960795 + 2345571 * 2 ^ 59
def prefixEnd_2345571 : Nat := 4983230072969 + 3 ^ 40 * 2345571 * 2
def baseEnd_2345571 : Nat := 44607604898042506532423

theorem tailTrace_2345571 : CollatzResearch.WordTrace tailWord_2345571 prefixEnd_2345571 44607604898042506532423 := by
  unfold tailWord_2345571
  simp only [CollatzResearch.WordTrace]
  refine ⟨85550002585404333479180567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57033335056936222319453711 85550002585404333479180567)
  ·
    refine ⟨128325003878106500218770851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85550002585404333479180567 128325003878106500218770851)
    ·
      refine ⟨192487505817159750328156277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128325003878106500218770851 192487505817159750328156277)
      ·
        refine ⟨18045703670358726593264651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192487505817159750328156277 18045703670358726593264651)
        ·
          refine ⟨27068555505538089889896977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18045703670358726593264651 27068555505538089889896977)
          ·
            refine ⟨20301416629153567417422733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27068555505538089889896977 20301416629153567417422733)
            ·
              refine ⟨7613031235932587781533525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20301416629153567417422733 7613031235932587781533525)
              ·
                refine ⟨44607604898042506532423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7613031235932587781533525 44607604898042506532423)
                ·
                  rfl

theorem cell23_2345571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 9].length) (baseStart_2345571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345571 prefixEnd_2345571 := by exact prefixLift 2345571
  have htrace : WordTrace (prefixWord ++ tailWord_2345571) baseStart_2345571 baseEnd_2345571 := by
    simpa [prefixWord, tailWord_2345571, baseEnd_2345571] using wordTrace_append hprefix tailTrace_2345571
  have hstable : (prefixWord ++ tailWord_2345571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345571).length < 2 ^ (prefixWord ++ tailWord_2345571).sum := by decide
  have hdescent : baseEnd_2345571 < baseStart_2345571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345576 : List Nat := [2, 1, 4, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2345576 : Nat := 118140960795 + 2345576 * 2 ^ 59
def prefixEnd_2345576 : Nat := 4983230072969 + 3 ^ 40 * 2345576 * 2
def baseEnd_2345576 : Nat := 1204407899650420156812899

theorem tailTrace_2345576 : CollatzResearch.WordTrace tailWord_2345576 prefixEnd_2345576 1204407899650420156812899 := by
  unfold tailWord_2345576
  simp only [CollatzResearch.WordTrace]
  refine ⟨42775092475193109666556291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57033456633590812888741721 42775092475193109666556291)
  ·
    refine ⟨64162638712789664499834437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42775092475193109666556291 64162638712789664499834437)
    ·
      refine ⟨12030494758648062093718957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64162638712789664499834437 12030494758648062093718957)
      ·
        refine ⟨4511435534493023285144609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12030494758648062093718957 4511435534493023285144609)
        ·
          refine ⟨3383576650869767463858457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4511435534493023285144609 3383576650869767463858457)
          ·
            refine ⟨2537682488152325597893843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3383576650869767463858457 2537682488152325597893843)
            ·
              refine ⟨3806523732228488396840765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537682488152325597893843 3806523732228488396840765)
              ·
                refine ⟨1427446399585683148815287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3806523732228488396840765 1427446399585683148815287)
                ·
                  refine ⟨2141169599378524723222931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427446399585683148815287 2141169599378524723222931)
                  ·
                    refine ⟨3211754399067787084834397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2141169599378524723222931 3211754399067787084834397)
                    ·
                      refine ⟨1204407899650420156812899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3211754399067787084834397 1204407899650420156812899)
                      ·
                        rfl

theorem cell23_2345576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2345576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345576 prefixEnd_2345576 := by exact prefixLift 2345576
  have htrace : WordTrace (prefixWord ++ tailWord_2345576) baseStart_2345576 baseEnd_2345576 := by
    simpa [prefixWord, tailWord_2345576, baseEnd_2345576] using wordTrace_append hprefix tailTrace_2345576
  have hstable : (prefixWord ++ tailWord_2345576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345576).length < 2 ^ (prefixWord ++ tailWord_2345576).sum := by decide
  have hdescent : baseEnd_2345576 < baseStart_2345576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345578 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2345578 : Nat := 118140960795 + 2345578 * 2 ^ 59
def prefixEnd_2345578 : Nat := 4983230072969 + 3 ^ 40 * 2345578 * 2
def baseEnd_2345578 : Nat := 1204408926611729148987889

theorem tailTrace_2345578 : CollatzResearch.WordTrace tailWord_2345578 prefixEnd_2345578 1204408926611729148987889 := by
  unfold tailWord_2345578
  simp only [CollatzResearch.WordTrace]
  refine ⟨21387564474094743418671347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57033505264252649116456925 21387564474094743418671347)
  ·
    refine ⟨32081346711142115128007021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21387564474094743418671347 32081346711142115128007021)
    ·
      refine ⟨12030505016678293173002633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32081346711142115128007021 12030505016678293173002633)
      ·
        refine ⟨9022878762508719879751975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12030505016678293173002633 9022878762508719879751975)
        ·
          refine ⟨13534318143763079819627963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9022878762508719879751975 13534318143763079819627963)
          ·
            refine ⟨20301477215644619729441945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13534318143763079819627963 20301477215644619729441945)
            ·
              refine ⟨15226107911733464797081459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20301477215644619729441945 15226107911733464797081459)
              ·
                refine ⟨22839161867600197195622189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15226107911733464797081459 22839161867600197195622189)
                ·
                  refine ⟨8564685700350073948358321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22839161867600197195622189 8564685700350073948358321)
                  ·
                    refine ⟨6423514275262555461268741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8564685700350073948358321 6423514275262555461268741)
                    ·
                      refine ⟨1204408926611729148987889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6423514275262555461268741 1204408926611729148987889)
                      ·
                        rfl

theorem cell23_2345578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2345578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345578 prefixEnd_2345578 := by exact prefixLift 2345578
  have htrace : WordTrace (prefixWord ++ tailWord_2345578) baseStart_2345578 baseEnd_2345578 := by
    simpa [prefixWord, tailWord_2345578, baseEnd_2345578] using wordTrace_append hprefix tailTrace_2345578
  have hstable : (prefixWord ++ tailWord_2345578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345578).length < 2 ^ (prefixWord ++ tailWord_2345578).sum := by decide
  have hdescent : baseEnd_2345578 < baseStart_2345578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345611 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 5]
def baseStart_2345611 : Nat := 118140960795 + 2345611 * 2 ^ 59
def prefixEnd_2345611 : Nat := 4983230072969 + 3 ^ 40 * 2345611 * 2
def baseEnd_2345611 : Nat := 1204425871473327519875237

theorem tailTrace_2345611 : CollatzResearch.WordTrace tailWord_2345611 prefixEnd_2345611 1204425871473327519875237 := by
  unfold tailWord_2345611
  simp only [CollatzResearch.WordTrace]
  refine ⟨85551461505259420310636687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57034307670172946873757791 85551461505259420310636687)
  ·
    refine ⟨128327192257889130465955031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85551461505259420310636687 128327192257889130465955031)
    ·
      refine ⟨192490788386833695698932547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128327192257889130465955031 192490788386833695698932547)
      ·
        refine ⟨288736182580250543548398821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192490788386833695698932547 288736182580250543548398821)
        ·
          refine ⟨54138034233796976915324779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288736182580250543548398821 54138034233796976915324779)
          ·
            refine ⟨81207051350695465372987169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54138034233796976915324779 81207051350695465372987169)
            ·
              refine ⟨60905288513021599029740377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81207051350695465372987169 60905288513021599029740377)
              ·
                refine ⟨45678966384766199272305283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60905288513021599029740377 45678966384766199272305283)
                ·
                  refine ⟨68518449577149298908457925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45678966384766199272305283 68518449577149298908457925)
                  ·
                    refine ⟨12847209295715493545335861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68518449577149298908457925 12847209295715493545335861)
                    ·
                      refine ⟨1204425871473327519875237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12847209295715493545335861 1204425871473327519875237)
                      ·
                        rfl

theorem cell23_2345611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_2345611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345611 prefixEnd_2345611 := by exact prefixLift 2345611
  have htrace : WordTrace (prefixWord ++ tailWord_2345611) baseStart_2345611 baseEnd_2345611 := by
    simpa [prefixWord, tailWord_2345611, baseEnd_2345611] using wordTrace_append hprefix tailTrace_2345611
  have hstable : (prefixWord ++ tailWord_2345611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345611).length < 2 ^ (prefixWord ++ tailWord_2345611).sum := by decide
  have hdescent : baseEnd_2345611 < baseStart_2345611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345615 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 3]
def baseStart_2345615 : Nat := 118140960795 + 2345615 * 2 ^ 59
def prefixEnd_2345615 : Nat := 4983230072969 + 3 ^ 40 * 2345615 * 2
def baseEnd_2345615 : Nat := 1204427925395945504225219

theorem tailTrace_2345615 : CollatzResearch.WordTrace tailWord_2345615 prefixEnd_2345615 1204427925395945504225219 := by
  unfold tailWord_2345615
  simp only [CollatzResearch.WordTrace]
  refine ⟨85551607397244928993782299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57034404931496619329188199 85551607397244928993782299)
  ·
    refine ⟨128327411095867393490673449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85551607397244928993782299 128327411095867393490673449)
    ·
      refine ⟨96245558321900545118005087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128327411095867393490673449 96245558321900545118005087)
      ·
        refine ⟨144368337482850817677007631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96245558321900545118005087 144368337482850817677007631)
        ·
          refine ⟨216552506224276226515511447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144368337482850817677007631 216552506224276226515511447)
          ·
            refine ⟨324828759336414339773267171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216552506224276226515511447 324828759336414339773267171)
            ·
              refine ⟨487243139004621509659900757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324828759336414339773267171 487243139004621509659900757)
              ·
                refine ⟨2854940267605204158163481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 487243139004621509659900757 2854940267605204158163481)
                ·
                  refine ⟨2141205200703903118622611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2854940267605204158163481 2141205200703903118622611)
                  ·
                    refine ⟨3211807801055854677933917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2141205200703903118622611 3211807801055854677933917)
                    ·
                      refine ⟨1204427925395945504225219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3211807801055854677933917 1204427925395945504225219)
                      ·
                        rfl

theorem cell23_2345615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 3].length) (baseStart_2345615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345615 prefixEnd_2345615 := by exact prefixLift 2345615
  have htrace : WordTrace (prefixWord ++ tailWord_2345615) baseStart_2345615 baseEnd_2345615 := by
    simpa [prefixWord, tailWord_2345615, baseEnd_2345615] using wordTrace_append hprefix tailTrace_2345615
  have hstable : (prefixWord ++ tailWord_2345615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345615).length < 2 ^ (prefixWord ++ tailWord_2345615).sum := by decide
  have hdescent : baseEnd_2345615 < baseStart_2345615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345621 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_2345621 : Nat := 118140960795 + 2345621 * 2 ^ 59
def prefixEnd_2345621 : Nat := 4983230072969 + 3 ^ 40 * 2345621 * 2
def baseEnd_2345621 : Nat := 1204431006279872480750191

theorem tailTrace_2345621 : CollatzResearch.WordTrace tailWord_2345621 prefixEnd_2345621 1204431006279872480750191 := by
  unfold tailWord_2345621
  simp only [CollatzResearch.WordTrace]
  refine ⟨85551826235223192018500717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57034550823482128012333811 85551826235223192018500717)
  ·
    refine ⟨32081934838208697006937769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85551826235223192018500717 32081934838208697006937769)
    ·
      refine ⟨24061451128656522755203327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32081934838208697006937769 24061451128656522755203327)
      ·
        refine ⟨36092176692984784132804991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24061451128656522755203327 36092176692984784132804991)
        ·
          refine ⟨54138265039477176199207487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36092176692984784132804991 54138265039477176199207487)
          ·
            refine ⟨81207397559215764298811231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54138265039477176199207487 81207397559215764298811231)
            ·
              refine ⟨121811096338823646448216847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81207397559215764298811231 121811096338823646448216847)
              ·
                refine ⟨182716644508235469672325271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121811096338823646448216847 182716644508235469672325271)
                ·
                  refine ⟨274074966762353204508487907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182716644508235469672325271 274074966762353204508487907)
                  ·
                    refine ⟨411112450143529806762731861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274074966762353204508487907 411112450143529806762731861)
                    ·
                      refine ⟨1204431006279872480750191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 411112450143529806762731861 1204431006279872480750191)
                      ·
                        rfl

theorem cell23_2345621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_2345621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345621 prefixEnd_2345621 := by exact prefixLift 2345621
  have htrace : WordTrace (prefixWord ++ tailWord_2345621) baseStart_2345621 baseEnd_2345621 := by
    simpa [prefixWord, tailWord_2345621, baseEnd_2345621] using wordTrace_append hprefix tailTrace_2345621
  have hstable : (prefixWord ++ tailWord_2345621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345621).length < 2 ^ (prefixWord ++ tailWord_2345621).sum := by decide
  have hdescent : baseEnd_2345621 < baseStart_2345621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345625 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 3, 3, 2]
def baseStart_2345625 : Nat := 118140960795 + 2345625 * 2 ^ 59
def prefixEnd_2345625 : Nat := 4983230072969 + 3 ^ 40 * 2345625 * 2
def baseEnd_2345625 : Nat := 1204433060202490465100173

theorem tailTrace_2345625 : CollatzResearch.WordTrace tailWord_2345625 prefixEnd_2345625 1204433060202490465100173 := by
  unfold tailWord_2345625
  simp only [CollatzResearch.WordTrace]
  refine ⟨85551972127208700701646329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57034648084805800467764219 85551972127208700701646329)
  ·
    refine ⟨64163979095406525526234747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85551972127208700701646329 64163979095406525526234747)
    ·
      refine ⟨96245968643109788289352121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64163979095406525526234747 96245968643109788289352121)
      ·
        refine ⟨72184476482332341217014091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96245968643109788289352121 72184476482332341217014091)
        ·
          refine ⟨108276714723498511825521137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72184476482332341217014091 108276714723498511825521137)
          ·
            refine ⟨81207536042623883869140853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108276714723498511825521137 81207536042623883869140853)
            ·
              refine ⟨7613206503995989112731955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81207536042623883869140853 7613206503995989112731955)
              ·
                refine ⟨11419809755993983669097933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7613206503995989112731955 11419809755993983669097933)
                ·
                  refine ⟨4282428658497743875911725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11419809755993983669097933 4282428658497743875911725)
                  ·
                    refine ⟨1605910746936653953466897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4282428658497743875911725 1605910746936653953466897)
                    ·
                      refine ⟨1204433060202490465100173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605910746936653953466897 1204433060202490465100173)
                      ·
                        rfl

theorem cell23_2345625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_2345625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345625 prefixEnd_2345625 := by exact prefixLift 2345625
  have htrace : WordTrace (prefixWord ++ tailWord_2345625) baseStart_2345625 baseEnd_2345625 := by
    simpa [prefixWord, tailWord_2345625, baseEnd_2345625] using wordTrace_append hprefix tailTrace_2345625
  have hstable : (prefixWord ++ tailWord_2345625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345625).length < 2 ^ (prefixWord ++ tailWord_2345625).sum := by decide
  have hdescent : baseEnd_2345625 < baseStart_2345625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345658 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_2345658 : Nat := 118140960795 + 2345658 * 2 ^ 59
def prefixEnd_2345658 : Nat := 4983230072969 + 3 ^ 40 * 2345658 * 2
def baseEnd_2345658 : Nat := 1204450005064088835987521

theorem tailTrace_2345658 : CollatzResearch.WordTrace tailWord_2345658 prefixEnd_2345658 1204450005064088835987521 := by
  unfold tailWord_2345658
  simp only [CollatzResearch.WordTrace]
  refine ⟨21388293934022286834399407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57035450490726098225065085 21388293934022286834399407)
  ·
    refine ⟨32082440901033430251599111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21388293934022286834399407 32082440901033430251599111)
    ·
      refine ⟨48123661351550145377398667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32082440901033430251599111 48123661351550145377398667)
      ·
        refine ⟨72185492027325218066098001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48123661351550145377398667 72185492027325218066098001)
        ·
          refine ⟨54139119020493913549573501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72185492027325218066098001 54139119020493913549573501)
          ·
            refine ⟨20302169632685217581090063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54139119020493913549573501 20302169632685217581090063)
            ·
              refine ⟨30453254449027826371635095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20302169632685217581090063 30453254449027826371635095)
              ·
                refine ⟨45679881673541739557452643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30453254449027826371635095 45679881673541739557452643)
                ·
                  refine ⟨68519822510312609336178965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45679881673541739557452643 68519822510312609336178965)
                  ·
                    refine ⟨3211866680170903562633389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68519822510312609336178965 3211866680170903562633389)
                    ·
                      refine ⟨1204450005064088835987521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3211866680170903562633389 1204450005064088835987521)
                      ·
                        rfl

theorem cell23_2345658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_2345658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345658 prefixEnd_2345658 := by exact prefixLift 2345658
  have htrace : WordTrace (prefixWord ++ tailWord_2345658) baseStart_2345658 baseEnd_2345658 := by
    simpa [prefixWord, tailWord_2345658, baseEnd_2345658] using wordTrace_append hprefix tailTrace_2345658
  have hstable : (prefixWord ++ tailWord_2345658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345658).length < 2 ^ (prefixWord ++ tailWord_2345658).sum := by decide
  have hdescent : baseEnd_2345658 < baseStart_2345658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345672 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_2345672 : Nat := 118140960795 + 2345672 * 2 ^ 59
def prefixEnd_2345672 : Nat := 4983230072969 + 3 ^ 40 * 2345672 * 2
def baseEnd_2345672 : Nat := 1204457193793251781212457

theorem tailTrace_2345672 : CollatzResearch.WordTrace tailWord_2345672 prefixEnd_2345672 1204457193793251781212457 := by
  unfold tailWord_2345672
  simp only [CollatzResearch.WordTrace]
  refine ⟨42776843179019213864303635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57035790905358951819071513 42776843179019213864303635)
  ·
    refine ⟨64165264768528820796455453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42776843179019213864303635 64165264768528820796455453)
    ·
      refine ⟨24061974288198307798670795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64165264768528820796455453 24061974288198307798670795)
      ·
        refine ⟨36092961432297461698006193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24061974288198307798670795 36092961432297461698006193)
        ·
          refine ⟨27069721074223096273504645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36092961432297461698006193 27069721074223096273504645)
          ·
            refine ⟨5075572701416830551282121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27069721074223096273504645 5075572701416830551282121)
            ·
              refine ⟨3806679526062622913461591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075572701416830551282121 3806679526062622913461591)
              ·
                refine ⟨5710019289093934370192387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806679526062622913461591 5710019289093934370192387)
                ·
                  refine ⟨8565028933640901555288581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710019289093934370192387 8565028933640901555288581)
                  ·
                    refine ⟨1605942925057669041616609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8565028933640901555288581 1605942925057669041616609)
                    ·
                      refine ⟨1204457193793251781212457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605942925057669041616609 1204457193793251781212457)
                      ·
                        rfl

theorem cell23_2345672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_2345672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345672 prefixEnd_2345672 := by exact prefixLift 2345672
  have htrace : WordTrace (prefixWord ++ tailWord_2345672) baseStart_2345672 baseEnd_2345672 := by
    simpa [prefixWord, tailWord_2345672, baseEnd_2345672] using wordTrace_append hprefix tailTrace_2345672
  have hstable : (prefixWord ++ tailWord_2345672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345672).length < 2 ^ (prefixWord ++ tailWord_2345672).sum := by decide
  have hdescent : baseEnd_2345672 < baseStart_2345672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345678 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_2345678 : Nat := 118140960795 + 2345678 * 2 ^ 59
def prefixEnd_2345678 : Nat := 4983230072969 + 3 ^ 40 * 2345678 * 2
def baseEnd_2345678 : Nat := 133828919408575417526381

theorem tailTrace_2345678 : CollatzResearch.WordTrace tailWord_2345678 prefixEnd_2345678 133828919408575417526381 := by
  unfold tailWord_2345678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10694238149502086344165711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57035936797344460502217125 10694238149502086344165711)
  ·
    refine ⟨16041357224253129516248567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10694238149502086344165711 16041357224253129516248567)
    ·
      refine ⟨24062035836379694274372851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16041357224253129516248567 24062035836379694274372851)
      ·
        refine ⟨36093053754569541411559277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24062035836379694274372851 36093053754569541411559277)
        ·
          refine ⟨13534895157963578029334729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36093053754569541411559277 13534895157963578029334729)
          ·
            refine ⟨10151171368472683522001047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13534895157963578029334729 10151171368472683522001047)
            ·
              refine ⟨15226757052709025283001571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10151171368472683522001047 15226757052709025283001571)
              ·
                refine ⟨22840135579063537924502357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15226757052709025283001571 22840135579063537924502357)
                ·
                  refine ⟨133828919408575417526381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22840135579063537924502357 133828919408575417526381)
                  ·
                    rfl

theorem cell23_2345678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_2345678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345678 prefixEnd_2345678 := by exact prefixLift 2345678
  have htrace : WordTrace (prefixWord ++ tailWord_2345678) baseStart_2345678 baseEnd_2345678 := by
    simpa [prefixWord, tailWord_2345678, baseEnd_2345678] using wordTrace_append hprefix tailTrace_2345678
  have hstable : (prefixWord ++ tailWord_2345678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345678).length < 2 ^ (prefixWord ++ tailWord_2345678).sum := by decide
  have hdescent : baseEnd_2345678 < baseStart_2345678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345695 : List Nat := [1, 1, 2, 3, 2, 3, 1, 5, 5]
def baseStart_2345695 : Nat := 118140960795 + 2345695 * 2 ^ 59
def prefixEnd_2345695 : Nat := 4983230072969 + 3 ^ 40 * 2345695 * 2
def baseEnd_2345695 : Nat := 133829889316478354580539

theorem tailTrace_2345695 : CollatzResearch.WordTrace tailWord_2345695 prefixEnd_2345695 133829889316478354580539 := by
  unfold tailWord_2345695
  simp only [CollatzResearch.WordTrace]
  refine ⟨85554525236955102656694539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57036350157970068437796359 85554525236955102656694539)
  ·
    refine ⟨128331787855432653985041809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85554525236955102656694539 128331787855432653985041809)
    ·
      refine ⟨96248840891574490488781357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128331787855432653985041809 96248840891574490488781357)
      ·
        refine ⟨36093315334340433933293009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96248840891574490488781357 36093315334340433933293009)
        ·
          refine ⟨27069986500755325449969757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36093315334340433933293009 27069986500755325449969757)
          ·
            refine ⟨10151244937783247043738659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27069986500755325449969757 10151244937783247043738659)
            ·
              refine ⟨15226867406674870565607989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10151244937783247043738659 15226867406674870565607989)
              ·
                refine ⟨1427518819375769115525749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15226867406674870565607989 1427518819375769115525749)
                ·
                  refine ⟨133829889316478354580539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1427518819375769115525749 133829889316478354580539)
                  ·
                    rfl

theorem cell23_2345695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 5].length) (baseStart_2345695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345695 prefixEnd_2345695 := by exact prefixLift 2345695
  have htrace : WordTrace (prefixWord ++ tailWord_2345695) baseStart_2345695 baseEnd_2345695 := by
    simpa [prefixWord, tailWord_2345695, baseEnd_2345695] using wordTrace_append hprefix tailTrace_2345695
  have hstable : (prefixWord ++ tailWord_2345695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345695).length < 2 ^ (prefixWord ++ tailWord_2345695).sum := by decide
  have hdescent : baseEnd_2345695 < baseStart_2345695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345708 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_2345708 : Nat := 118140960795 + 2345708 * 2 ^ 59
def prefixEnd_2345708 : Nat := 4983230072969 + 3 ^ 40 * 2345708 * 2
def baseEnd_2345708 : Nat := 401491893032271213454097

theorem tailTrace_2345708 : CollatzResearch.WordTrace tailWord_2345708 prefixEnd_2345708 401491893032271213454097 := by
  unfold tailWord_2345708
  simp only [CollatzResearch.WordTrace]
  refine ⟨42777499692954002938458889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57036666257272003917945185 42777499692954002938458889)
  ·
    refine ⟨32083124769715502203844167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42777499692954002938458889 32083124769715502203844167)
    ·
      refine ⟨48124687154573253305766251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32083124769715502203844167 48124687154573253305766251)
      ·
        refine ⟨72187030731859879958649377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48124687154573253305766251 72187030731859879958649377)
        ·
          refine ⟨54140273048894909968987033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72187030731859879958649377 54140273048894909968987033)
          ·
            refine ⟨40605204786671182476740275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54140273048894909968987033 40605204786671182476740275)
            ·
              refine ⟨60907807180006773715110413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40605204786671182476740275 60907807180006773715110413)
              ·
                refine ⟨22840427692502540143166405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60907807180006773715110413 22840427692502540143166405)
                ·
                  refine ⟨4282580192344226276843701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22840427692502540143166405 4282580192344226276843701)
                  ·
                    refine ⟨401491893032271213454097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4282580192344226276843701 401491893032271213454097)
                    ·
                      rfl

theorem cell23_2345708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_2345708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345708 prefixEnd_2345708 := by exact prefixLift 2345708
  have htrace : WordTrace (prefixWord ++ tailWord_2345708) baseStart_2345708 baseEnd_2345708 := by
    simpa [prefixWord, tailWord_2345708, baseEnd_2345708] using wordTrace_append hprefix tailTrace_2345708
  have hstable : (prefixWord ++ tailWord_2345708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345708).length < 2 ^ (prefixWord ++ tailWord_2345708).sum := by decide
  have hdescent : baseEnd_2345708 < baseStart_2345708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345738 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_2345738 : Nat := 118140960795 + 2345738 * 2 ^ 59
def prefixEnd_2345738 : Nat := 4983230072969 + 3 ^ 40 * 2345738 * 2
def baseEnd_2345738 : Nat := 401497027838816174329051

theorem tailTrace_2345738 : CollatzResearch.WordTrace tailWord_2345738 prefixEnd_2345738 401497027838816174329051 := by
  unfold tailWord_2345738
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389023393949830250127467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57037395717199547333673245 21389023393949830250127467)
  ·
    refine ⟨32083535090924745375191201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21389023393949830250127467 32083535090924745375191201)
    ·
      refine ⟨24062651318193559031393401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32083535090924745375191201 24062651318193559031393401)
      ·
        refine ⟨18046988488645169273545051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24062651318193559031393401 18046988488645169273545051)
        ·
          refine ⟨27070482732967753910317577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18046988488645169273545051 27070482732967753910317577)
          ·
            refine ⟨20302862049725815432738183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27070482732967753910317577 20302862049725815432738183)
            ·
              refine ⟨30454293074588723149107275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20302862049725815432738183 30454293074588723149107275)
              ·
                refine ⟨45681439611883084723660913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30454293074588723149107275 45681439611883084723660913)
                ·
                  refine ⟨34261079708912313542745685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45681439611883084723660913 34261079708912313542745685)
                  ·
                    refine ⟨401497027838816174329051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34261079708912313542745685 401497027838816174329051)
                    ·
                      rfl

theorem cell23_2345738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_2345738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345738 prefixEnd_2345738 := by exact prefixLift 2345738
  have htrace : WordTrace (prefixWord ++ tailWord_2345738) baseStart_2345738 baseEnd_2345738 := by
    simpa [prefixWord, tailWord_2345738, baseEnd_2345738] using wordTrace_append hprefix tailTrace_2345738
  have hstable : (prefixWord ++ tailWord_2345738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345738).length < 2 ^ (prefixWord ++ tailWord_2345738).sum := by decide
  have hdescent : baseEnd_2345738 < baseStart_2345738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345745 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 1, 6, 2]
def baseStart_2345745 : Nat := 118140960795 + 2345745 * 2 ^ 59
def prefixEnd_2345745 : Nat := 4983230072969 + 3 ^ 40 * 2345745 * 2
def baseEnd_2345745 : Nat := 1204494677881029995599621

theorem tailTrace_2345745 : CollatzResearch.WordTrace tailWord_2345745 prefixEnd_2345745 1204494677881029995599621 := by
  unfold tailWord_2345745
  simp only [CollatzResearch.WordTrace]
  refine ⟨85556348886773961196014689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57037565924515974130676459 85556348886773961196014689)
  ·
    refine ⟨64167261665080470897011017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85556348886773961196014689 64167261665080470897011017)
    ·
      refine ⟨48125446248810353172758263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64167261665080470897011017 48125446248810353172758263)
      ·
        refine ⟨72188169373215529759137395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48125446248810353172758263 72188169373215529759137395)
        ·
          refine ⟨108282254059823294638706093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72188169373215529759137395 108282254059823294638706093)
          ·
            refine ⟨40605845272433735489514785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108282254059823294638706093 40605845272433735489514785)
            ·
              refine ⟨30454383954325301617136089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40605845272433735489514785 30454383954325301617136089)
              ·
                refine ⟨22840787965743976212852067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30454383954325301617136089 22840787965743976212852067)
                ·
                  refine ⟨34261181948615964319278101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22840787965743976212852067 34261181948615964319278101)
                  ·
                    refine ⟨1605992903841373327466161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34261181948615964319278101 1605992903841373327466161)
                    ·
                      refine ⟨1204494677881029995599621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1605992903841373327466161 1204494677881029995599621)
                      ·
                        rfl

theorem cell23_2345745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_2345745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345745 prefixEnd_2345745 := by exact prefixLift 2345745
  have htrace : WordTrace (prefixWord ++ tailWord_2345745) baseStart_2345745 baseEnd_2345745 := by
    simpa [prefixWord, tailWord_2345745, baseEnd_2345745] using wordTrace_append hprefix tailTrace_2345745
  have hstable : (prefixWord ++ tailWord_2345745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345745).length < 2 ^ (prefixWord ++ tailWord_2345745).sum := by decide
  have hdescent : baseEnd_2345745 < baseStart_2345745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345746 : List Nat := [3, 2, 4, 1, 2, 2, 1, 3, 5]
def baseStart_2345746 : Nat := 118140960795 + 2345746 * 2 ^ 59
def prefixEnd_2345746 : Nat := 4983230072969 + 3 ^ 40 * 2345746 * 2
def baseEnd_2345746 : Nat := 133832799040187165743013

theorem tailTrace_2345746 : CollatzResearch.WordTrace tailWord_2345746 prefixEnd_2345746 133832799040187165743013 := by
  unfold tailWord_2345746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389096339942584591700273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57037590239846892244534061 21389096339942584591700273)
  ·
    refine ⟨16041822254956938443775205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21389096339942584591700273 16041822254956938443775205)
    ·
      refine ⟨3007841672804425958207851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16041822254956938443775205 3007841672804425958207851)
      ·
        refine ⟨4511762509206638937311777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007841672804425958207851 4511762509206638937311777)
        ·
          refine ⟨3383821881904979202983833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4511762509206638937311777 3383821881904979202983833)
          ·
            refine ⟨2537866411428734402237875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3383821881904979202983833 2537866411428734402237875)
            ·
              refine ⟨3806799617143101603356813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537866411428734402237875 3806799617143101603356813)
              ·
                refine ⟨1427549856428663101258805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3806799617143101603356813 1427549856428663101258805)
                ·
                  refine ⟨133832799040187165743013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1427549856428663101258805 133832799040187165743013)
                  ·
                    rfl

theorem cell23_2345746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_2345746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345746 prefixEnd_2345746 := by exact prefixLift 2345746
  have htrace : WordTrace (prefixWord ++ tailWord_2345746) baseStart_2345746 baseEnd_2345746 := by
    simpa [prefixWord, tailWord_2345746, baseEnd_2345746] using wordTrace_append hprefix tailTrace_2345746
  have hstable : (prefixWord ++ tailWord_2345746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345746).length < 2 ^ (prefixWord ++ tailWord_2345746).sum := by decide
  have hdescent : baseEnd_2345746 < baseStart_2345746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345762 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2345762 : Nat := 118140960795 + 2345762 * 2 ^ 59
def prefixEnd_2345762 : Nat := 4983230072969 + 3 ^ 40 * 2345762 * 2
def baseEnd_2345762 : Nat := 1204503407052156429087043

theorem tailTrace_2345762 : CollatzResearch.WordTrace tailWord_2345762 prefixEnd_2345762 1204503407052156429087043 := by
  unfold tailWord_2345762
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389242231928093274845885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57037979285141582066255693 21389242231928093274845885)
  ·
    refine ⟨8020965836973034978067207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21389242231928093274845885 8020965836973034978067207)
    ·
      refine ⟨12031448755459552467100811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8020965836973034978067207 12031448755459552467100811)
      ·
        refine ⟨18047173133189328700651217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12031448755459552467100811 18047173133189328700651217)
        ·
          refine ⟨13535379849891996525488413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18047173133189328700651217 13535379849891996525488413)
          ·
            refine ⟨5075767443709498697058155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13535379849891996525488413 5075767443709498697058155)
            ·
              refine ⟨7613651165564248045587233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5075767443709498697058155 7613651165564248045587233)
              ·
                refine ⟨5710238374173186034190425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7613651165564248045587233 5710238374173186034190425)
                ·
                  refine ⟨4282678780629889525642819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5710238374173186034190425 4282678780629889525642819)
                  ·
                    refine ⟨6424018170944834288464229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4282678780629889525642819 6424018170944834288464229)
                    ·
                      refine ⟨1204503407052156429087043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6424018170944834288464229 1204503407052156429087043)
                      ·
                        rfl

theorem cell23_2345762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2345762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345762 prefixEnd_2345762 := by exact prefixLift 2345762
  have htrace : WordTrace (prefixWord ++ tailWord_2345762) baseStart_2345762 baseEnd_2345762 := by
    simpa [prefixWord, tailWord_2345762, baseEnd_2345762] using wordTrace_append hprefix tailTrace_2345762
  have hstable : (prefixWord ++ tailWord_2345762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345762).length < 2 ^ (prefixWord ++ tailWord_2345762).sum := by decide
  have hdescent : baseEnd_2345762 < baseStart_2345762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345796 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2345796 : Nat := 118140960795 + 2345796 * 2 ^ 59
def prefixEnd_2345796 : Nat := 4983230072969 + 3 ^ 40 * 2345796 * 2
def baseEnd_2345796 : Nat := 1204520865394409296061887

theorem tailTrace_2345796 : CollatzResearch.WordTrace tailWord_2345796 prefixEnd_2345796 1204520865394409296061887 := by
  unfold tailWord_2345796
  simp only [CollatzResearch.WordTrace]
  refine ⟨42779104504794598453060621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57038806006392797937414161 42779104504794598453060621)
  ·
    refine ⟨16042164189297974419897733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42779104504794598453060621 16042164189297974419897733)
    ·
      refine ⟨3007905785493370203730825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16042164189297974419897733 3007905785493370203730825)
      ·
        refine ⟨2255929339120027652798119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3007905785493370203730825 2255929339120027652798119)
        ·
          refine ⟨3383894008680041479197179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255929339120027652798119 3383894008680041479197179)
          ·
            refine ⟨5075841013020062218795769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383894008680041479197179 5075841013020062218795769)
            ·
              refine ⟨3806880759765046664096827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075841013020062218795769 3806880759765046664096827)
              ·
                refine ⟨5710321139647569996145241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806880759765046664096827 5710321139647569996145241)
                ·
                  refine ⟨4282740854735677497108931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5710321139647569996145241 4282740854735677497108931)
                  ·
                    refine ⟨6424111282103516245663397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4282740854735677497108931 6424111282103516245663397)
                    ·
                      refine ⟨1204520865394409296061887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6424111282103516245663397 1204520865394409296061887)
                      ·
                        rfl

theorem cell23_2345796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2345796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345796 prefixEnd_2345796 := by exact prefixLift 2345796
  have htrace : WordTrace (prefixWord ++ tailWord_2345796) baseStart_2345796 baseEnd_2345796 := by
    simpa [prefixWord, tailWord_2345796, baseEnd_2345796] using wordTrace_append hprefix tailTrace_2345796
  have hstable : (prefixWord ++ tailWord_2345796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345796).length < 2 ^ (prefixWord ++ tailWord_2345796).sum := by decide
  have hdescent : baseEnd_2345796 < baseStart_2345796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345835 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 4]
def baseStart_2345835 : Nat := 118140960795 + 2345835 * 2 ^ 59
def prefixEnd_2345835 : Nat := 4983230072969 + 3 ^ 40 * 2345835 * 2
def baseEnd_2345835 : Nat := 1204540891139934643474207

theorem tailTrace_2345835 : CollatzResearch.WordTrace tailWord_2345835 prefixEnd_2345835 1204540891139934643474207 := by
  unfold tailWord_2345835
  simp only [CollatzResearch.WordTrace]
  refine ⟨85559631456447906566790959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57039754304298604377860639 85559631456447906566790959)
  ·
    refine ⟨128339447184671859850186439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85559631456447906566790959 128339447184671859850186439)
    ·
      refine ⟨192509170777007789775279659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128339447184671859850186439 192509170777007789775279659)
      ·
        refine ⟨288763756165511684662919489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192509170777007789775279659 288763756165511684662919489)
        ·
          refine ⟨216572817124133763497189617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288763756165511684662919489 216572817124133763497189617)
          ·
            refine ⟨162429612843100322622892213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216572817124133763497189617 162429612843100322622892213)
            ·
              refine ⟨15227776204040655245896145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162429612843100322622892213 15227776204040655245896145)
              ·
                refine ⟨11420832153030491434422109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15227776204040655245896145 11420832153030491434422109)
                ·
                  refine ⟨4282812057386434287908291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11420832153030491434422109 4282812057386434287908291)
                  ·
                    refine ⟨6424218086079651431862437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4282812057386434287908291 6424218086079651431862437)
                    ·
                      refine ⟨1204540891139934643474207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6424218086079651431862437 1204540891139934643474207)
                      ·
                        rfl

theorem cell23_2345835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 4].length) (baseStart_2345835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345835 prefixEnd_2345835 := by exact prefixLift 2345835
  have htrace : WordTrace (prefixWord ++ tailWord_2345835) baseStart_2345835 baseEnd_2345835 := by
    simpa [prefixWord, tailWord_2345835, baseEnd_2345835] using wordTrace_append hprefix tailTrace_2345835
  have hstable : (prefixWord ++ tailWord_2345835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345835).length < 2 ^ (prefixWord ++ tailWord_2345835).sum := by decide
  have hdescent : baseEnd_2345835 < baseStart_2345835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345846 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2345846 : Nat := 118140960795 + 2345846 * 2 ^ 59
def prefixEnd_2345846 : Nat := 4983230072969 + 3 ^ 40 * 2345846 * 2
def baseEnd_2345846 : Nat := 1204546539427134100436657

theorem tailTrace_2345846 : CollatzResearch.WordTrace tailWord_2345846 prefixEnd_2345846 1204546539427134100436657 := by
  unfold tailWord_2345846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5347502041213003465340087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57040021772938703630294261 5347502041213003465340087)
  ·
    refine ⟨8021253061819505198010131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5347502041213003465340087 8021253061819505198010131)
    ·
      refine ⟨12031879592729257797015197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8021253061819505198010131 12031879592729257797015197)
      ·
        refine ⟨4511954847273471673880699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12031879592729257797015197 4511954847273471673880699)
        ·
          refine ⟨6767932270910207510821049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511954847273471673880699 6767932270910207510821049)
          ·
            refine ⟨5075949203182655633115787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6767932270910207510821049 5075949203182655633115787)
            ·
              refine ⟨7613923804773983449673681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5075949203182655633115787 7613923804773983449673681)
              ·
                refine ⟨5710442853580487587255261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7613923804773983449673681 5710442853580487587255261)
                ·
                  refine ⟨2141416070092682845220723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5710442853580487587255261 2141416070092682845220723)
                  ·
                    refine ⟨3212124105139024267831085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2141416070092682845220723 3212124105139024267831085)
                    ·
                      refine ⟨1204546539427134100436657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3212124105139024267831085 1204546539427134100436657)
                      ·
                        rfl

theorem cell23_2345846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2345846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345846 prefixEnd_2345846 := by exact prefixLift 2345846
  have htrace : WordTrace (prefixWord ++ tailWord_2345846) baseStart_2345846 baseEnd_2345846 := by
    simpa [prefixWord, tailWord_2345846, baseEnd_2345846] using wordTrace_append hprefix tailTrace_2345846
  have hstable : (prefixWord ++ tailWord_2345846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345846).length < 2 ^ (prefixWord ++ tailWord_2345846).sum := by decide
  have hdescent : baseEnd_2345846 < baseStart_2345846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345866 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_2345866 : Nat := 118140960795 + 2345866 * 2 ^ 59
def prefixEnd_2345866 : Nat := 4983230072969 + 3 ^ 40 * 2345866 * 2
def baseEnd_2345866 : Nat := 401518936346741340728855

theorem tailTrace_2345866 : CollatzResearch.WordTrace tailWord_2345866 prefixEnd_2345866 401518936346741340728855 := by
  unfold tailWord_2345866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21390190529833899715292363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57040508079557065907446301 21390190529833899715292363)
  ·
    refine ⟨32085285794750849572938545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21390190529833899715292363 32085285794750849572938545)
    ·
      refine ⟨24063964346063137179703909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32085285794750849572938545 24063964346063137179703909)
      ·
        refine ⟨4511993314886838221194483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24063964346063137179703909 4511993314886838221194483)
        ·
          refine ⟨6767989972330257331791725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511993314886838221194483 6767989972330257331791725)
          ·
            refine ⟨2537996239623846499421897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6767989972330257331791725 2537996239623846499421897)
            ·
              refine ⟨1903497179717884874566423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2537996239623846499421897 1903497179717884874566423)
              ·
                refine ⟨2855245769576827311849635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903497179717884874566423 2855245769576827311849635)
                ·
                  refine ⟨4282868654365240967774453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855245769576827311849635 4282868654365240967774453)
                  ·
                    refine ⟨401518936346741340728855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4282868654365240967774453 401518936346741340728855)
                    ·
                      rfl

theorem cell23_2345866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_2345866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345866 prefixEnd_2345866 := by exact prefixLift 2345866
  have htrace : WordTrace (prefixWord ++ tailWord_2345866) baseStart_2345866 baseEnd_2345866 := by
    simpa [prefixWord, tailWord_2345866, baseEnd_2345866] using wordTrace_append hprefix tailTrace_2345866
  have hstable : (prefixWord ++ tailWord_2345866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345866).length < 2 ^ (prefixWord ++ tailWord_2345866).sum := by decide
  have hdescent : baseEnd_2345866 < baseStart_2345866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345962 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2345962 : Nat := 118140960795 + 2345962 * 2 ^ 59
def prefixEnd_2345962 : Nat := 4983230072969 + 3 ^ 40 * 2345962 * 2
def baseEnd_2345962 : Nat := 1204606103183055646586123

theorem tailTrace_2345962 : CollatzResearch.WordTrace tailWord_2345962 prefixEnd_2345962 1204606103183055646586123 := by
  unfold tailWord_2345962
  simp only [CollatzResearch.WordTrace]
  refine ⟨21391065881746951814166035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57042842351325204837776093 21391065881746951814166035)
  ·
    refine ⟨32086598822620427721249053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21391065881746951814166035 32086598822620427721249053)
    ·
      refine ⟨12032474558482660395468395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32086598822620427721249053 12032474558482660395468395)
      ·
        refine ⟨18048711837723990593202593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12032474558482660395468395 18048711837723990593202593)
        ·
          refine ⟨13536533878292992944901945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18048711837723990593202593 13536533878292992944901945)
          ·
            refine ⟨10152400408719744708676459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13536533878292992944901945 10152400408719744708676459)
            ·
              refine ⟨15228600613079617063014689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10152400408719744708676459 15228600613079617063014689)
              ·
                refine ⟨11421450459809712797261017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15228600613079617063014689 11421450459809712797261017)
                ·
                  refine ⟨8566087844857284597945763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11421450459809712797261017 8566087844857284597945763)
                  ·
                    refine ⟨12849131767285926896918645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8566087844857284597945763 12849131767285926896918645)
                    ·
                      refine ⟨1204606103183055646586123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12849131767285926896918645 1204606103183055646586123)
                      ·
                        rfl

theorem cell23_2345962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2345962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2345962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2345962 prefixEnd_2345962 := by exact prefixLift 2345962
  have htrace : WordTrace (prefixWord ++ tailWord_2345962) baseStart_2345962 baseEnd_2345962 := by
    simpa [prefixWord, tailWord_2345962, baseEnd_2345962] using wordTrace_append hprefix tailTrace_2345962
  have hstable : (prefixWord ++ tailWord_2345962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345962).length < 2 ^ (prefixWord ++ tailWord_2345962).sum := by decide
  have hdescent : baseEnd_2345962 < baseStart_2345962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346032 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_2346032 : Nat := 118140960795 + 2346032 * 2 ^ 59
def prefixEnd_2346032 : Nat := 4983230072969 + 3 ^ 40 * 2346032 * 2
def baseEnd_2346032 : Nat := 1204642046828870372710801

theorem tailTrace_2346032 : CollatzResearch.WordTrace tailWord_2346032 prefixEnd_2346032 1204642046828870372710801 := by
  unfold tailWord_2346032
  simp only [CollatzResearch.WordTrace]
  refine ⟨42783408318367104605856175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57044544424489472807808233 42783408318367104605856175)
  ·
    refine ⟨64175112477550656908784263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42783408318367104605856175 64175112477550656908784263)
    ·
      refine ⟨96262668716325985363176395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64175112477550656908784263 96262668716325985363176395)
      ·
        refine ⟨144394003074488978044764593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96262668716325985363176395 144394003074488978044764593)
        ·
          refine ⟨108295502305866733533573445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144394003074488978044764593 108295502305866733533573445)
          ·
            refine ⟨20305406682350012537545021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108295502305866733533573445 20305406682350012537545021)
            ·
              refine ⟨7614527505881254701579383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20305406682350012537545021 7614527505881254701579383)
              ·
                refine ⟨11421791258821882052369075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7614527505881254701579383 11421791258821882052369075)
                ·
                  refine ⟨17132686888232823078553613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11421791258821882052369075 17132686888232823078553613)
                  ·
                    refine ⟨6424757583087308654457605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17132686888232823078553613 6424757583087308654457605)
                    ·
                      refine ⟨1204642046828870372710801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6424757583087308654457605 1204642046828870372710801)
                      ·
                        rfl

theorem cell23_2346032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_2346032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346032 prefixEnd_2346032 := by exact prefixLift 2346032
  have htrace : WordTrace (prefixWord ++ tailWord_2346032) baseStart_2346032 baseEnd_2346032 := by
    simpa [prefixWord, tailWord_2346032, baseEnd_2346032] using wordTrace_append hprefix tailTrace_2346032
  have hstable : (prefixWord ++ tailWord_2346032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346032).length < 2 ^ (prefixWord ++ tailWord_2346032).sum := by decide
  have hdescent : baseEnd_2346032 < baseStart_2346032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346062 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2346062 : Nat := 118140960795 + 2346062 * 2 ^ 59
def prefixEnd_2346062 : Nat := 4983230072969 + 3 ^ 40 * 2346062 * 2
def baseEnd_2346062 : Nat := 1204657451248505255335663

theorem tailTrace_2346062 : CollatzResearch.WordTrace tailWord_2346062 prefixEnd_2346062 1204657451248505255335663 := by
  unfold tailWord_2346062
  simp only [CollatzResearch.WordTrace]
  refine ⟨10695988853328190541913055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57045273884417016223536293 10695988853328190541913055)
  ·
    refine ⟨16043983279992285812869583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10695988853328190541913055 16043983279992285812869583)
    ·
      refine ⟨24065974919988428719304375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16043983279992285812869583 24065974919988428719304375)
      ·
        refine ⟨36098962379982643078956563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24065974919988428719304375 36098962379982643078956563)
        ·
          refine ⟨54148443569973964618434845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36098962379982643078956563 54148443569973964618434845)
          ·
            refine ⟨20305666338740236731913067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54148443569973964618434845 20305666338740236731913067)
            ·
              refine ⟨30458499508110355097869601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20305666338740236731913067 30458499508110355097869601)
              ·
                refine ⟨22843874631082766323402201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30458499508110355097869601 22843874631082766323402201)
                ·
                  refine ⟨17132905973312074742551651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22843874631082766323402201 17132905973312074742551651)
                  ·
                    refine ⟨25699358959968112113827477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17132905973312074742551651 25699358959968112113827477)
                    ·
                      refine ⟨1204657451248505255335663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25699358959968112113827477 1204657451248505255335663)
                      ·
                        rfl

theorem cell23_2346062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2346062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346062 prefixEnd_2346062 := by exact prefixLift 2346062
  have htrace : WordTrace (prefixWord ++ tailWord_2346062) baseStart_2346062 baseEnd_2346062 := by
    simpa [prefixWord, tailWord_2346062, baseEnd_2346062] using wordTrace_append hprefix tailTrace_2346062
  have hstable : (prefixWord ++ tailWord_2346062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346062).length < 2 ^ (prefixWord ++ tailWord_2346062).sum := by decide
  have hdescent : baseEnd_2346062 < baseStart_2346062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346066 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_2346066 : Nat := 118140960795 + 2346066 * 2 ^ 59
def prefixEnd_2346066 : Nat := 4983230072969 + 3 ^ 40 * 2346066 * 2
def baseEnd_2346066 : Nat := 1204659505171123239685645

theorem tailTrace_2346066 : CollatzResearch.WordTrace tailWord_2346066 prefixEnd_2346066 1204659505171123239685645 := by
  unfold tailWord_2346066
  simp only [CollatzResearch.WordTrace]
  refine ⟨21392014179652758254612513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57045371145740688678966701 21392014179652758254612513)
  ·
    refine ⟨16044010634739568690959385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21392014179652758254612513 16044010634739568690959385)
    ·
      refine ⟨12033007976054676518219539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16044010634739568690959385 12033007976054676518219539)
      ·
        refine ⟨18049511964082014777329309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12033007976054676518219539 18049511964082014777329309)
        ·
          refine ⟨6768566986530755541498491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18049511964082014777329309 6768566986530755541498491)
          ·
            refine ⟨10152850479796133312247737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6768566986530755541498491 10152850479796133312247737)
            ·
              refine ⟨7614637859847099984185803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10152850479796133312247737 7614637859847099984185803)
              ·
                refine ⟨11421956789770649976278705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7614637859847099984185803 11421956789770649976278705)
                ·
                  refine ⟨8566467592327987482209029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11421956789770649976278705 8566467592327987482209029)
                  ·
                    refine ⟨1606212673561497652914193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8566467592327987482209029 1606212673561497652914193)
                    ·
                      refine ⟨1204659505171123239685645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606212673561497652914193 1204659505171123239685645)
                      ·
                        rfl

theorem cell23_2346066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_2346066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346066 prefixEnd_2346066 := by exact prefixLift 2346066
  have htrace : WordTrace (prefixWord ++ tailWord_2346066) baseStart_2346066 baseEnd_2346066 := by
    simpa [prefixWord, tailWord_2346066, baseEnd_2346066] using wordTrace_append hprefix tailTrace_2346066
  have hstable : (prefixWord ++ tailWord_2346066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346066).length < 2 ^ (prefixWord ++ tailWord_2346066).sum := by decide
  have hdescent : baseEnd_2346066 < baseStart_2346066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346093 : List Nat := [1, 5, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_2346093 : Nat := 118140960795 + 2346093 * 2 ^ 59
def prefixEnd_2346093 : Nat := 4983230072969 + 3 ^ 40 * 2346093 * 2
def baseEnd_2346093 : Nat := 401557789716264878016007

theorem tailTrace_2346093 : CollatzResearch.WordTrace tailWord_2346093 prefixEnd_2346093 401557789716264878016007 := by
  unfold tailWord_2346093
  simp only [CollatzResearch.WordTrace]
  refine ⟨85569041489513216629682933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57046027659675477753121955 85569041489513216629682933)
  ·
    refine ⟨8022097639641864059032775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85569041489513216629682933 8022097639641864059032775)
    ·
      refine ⟨12033146459462796088549163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8022097639641864059032775 12033146459462796088549163)
      ·
        refine ⟨18049719689194194132823745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12033146459462796088549163 18049719689194194132823745)
        ·
          refine ⟨13537289766895645599617809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18049719689194194132823745 13537289766895645599617809)
          ·
            refine ⟨10152967325171734199713357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13537289766895645599617809 10152967325171734199713357)
            ·
              refine ⟨3807362746939400324892509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10152967325171734199713357 3807362746939400324892509)
              ·
                refine ⟨1427761030102275121834691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3807362746939400324892509 1427761030102275121834691)
                ·
                  refine ⟨2141641545153412682752037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427761030102275121834691 2141641545153412682752037)
                  ·
                    refine ⟨401557789716264878016007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2141641545153412682752037 401557789716264878016007)
                    ·
                      rfl

theorem cell23_2346093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_2346093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346093 prefixEnd_2346093 := by exact prefixLift 2346093
  have htrace : WordTrace (prefixWord ++ tailWord_2346093) baseStart_2346093 baseEnd_2346093 := by
    simpa [prefixWord, tailWord_2346093, baseEnd_2346093] using wordTrace_append hprefix tailTrace_2346093
  have hstable : (prefixWord ++ tailWord_2346093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346093).length < 2 ^ (prefixWord ++ tailWord_2346093).sum := by decide
  have hdescent : baseEnd_2346093 < baseStart_2346093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346136 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 1, 5]
def baseStart_2346136 : Nat := 118140960795 + 2346136 * 2 ^ 59
def prefixEnd_2346136 : Nat := 4983230072969 + 3 ^ 40 * 2346136 * 2
def baseEnd_2346136 : Nat := 401565149605645988603441

theorem tailTrace_2346136 : CollatzResearch.WordTrace tailWord_2346136 prefixEnd_2346136 401565149605645988603441 := by
  unfold tailWord_2346136
  simp only [CollatzResearch.WordTrace]
  refine ⟨42785304914178717486749131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57047073218904956648998841 42785304914178717486749131)
  ·
    refine ⟨64177957371268076230123697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42785304914178717486749131 64177957371268076230123697)
    ·
      refine ⟨48133468028451057172592773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64177957371268076230123697 48133468028451057172592773)
      ·
        refine ⟨9025025255334573219861145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48133468028451057172592773 9025025255334573219861145)
        ·
          refine ⟨6768768941500929914895859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9025025255334573219861145 6768768941500929914895859)
          ·
            refine ⟨10153153412251394872343789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6768768941500929914895859 10153153412251394872343789)
            ·
              refine ⟨3807432529594273077128921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10153153412251394872343789 3807432529594273077128921)
              ·
                refine ⟨2855574397195704807846691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3807432529594273077128921 2855574397195704807846691)
                ·
                  refine ⟨4283361595793557211770037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855574397195704807846691 4283361595793557211770037)
                  ·
                    refine ⟨401565149605645988603441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4283361595793557211770037 401565149605645988603441)
                    ·
                      rfl

theorem cell23_2346136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_2346136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346136 prefixEnd_2346136 := by exact prefixLift 2346136
  have htrace : WordTrace (prefixWord ++ tailWord_2346136) baseStart_2346136 baseEnd_2346136 := by
    simpa [prefixWord, tailWord_2346136, baseEnd_2346136] using wordTrace_append hprefix tailTrace_2346136
  have hstable : (prefixWord ++ tailWord_2346136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346136).length < 2 ^ (prefixWord ++ tailWord_2346136).sum := by decide
  have hdescent : baseEnd_2346136 < baseStart_2346136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346149 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_2346149 : Nat := 118140960795 + 2346149 * 2 ^ 59
def prefixEnd_2346149 : Nat := 4983230072969 + 3 ^ 40 * 2346149 * 2
def baseEnd_2346149 : Nat := 401567374688482138315921

theorem tailTrace_2346149 : CollatzResearch.WordTrace tailWord_2346149 prefixEnd_2346149 401567374688482138315921 := by
  unfold tailWord_2346149
  simp only [CollatzResearch.WordTrace]
  refine ⟨85571083977310338193721501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57047389318206892129147667 85571083977310338193721501)
  ·
    refine ⟨32089156491491376822645563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85571083977310338193721501 32089156491491376822645563)
    ·
      refine ⟨48133734737237065233968345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32089156491491376822645563 48133734737237065233968345)
      ·
        refine ⟨36100301052927798925476259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48133734737237065233968345 36100301052927798925476259)
        ·
          refine ⟨54150451579391698388214389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36100301052927798925476259 54150451579391698388214389)
          ·
            refine ⟨5076604835567971723895099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54150451579391698388214389 5076604835567971723895099)
            ·
              refine ⟨7614907253351957585842649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076604835567971723895099 7614907253351957585842649)
              ·
                refine ⟨5711180440013968189381987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7614907253351957585842649 5711180440013968189381987)
                ·
                  refine ⟨8566770660020952284072981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5711180440013968189381987 8566770660020952284072981)
                  ·
                    refine ⟨401567374688482138315921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8566770660020952284072981 401567374688482138315921)
                    ·
                      rfl

theorem cell23_2346149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_2346149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346149 prefixEnd_2346149 := by exact prefixLift 2346149
  have htrace : WordTrace (prefixWord ++ tailWord_2346149) baseStart_2346149 baseEnd_2346149 := by
    simpa [prefixWord, tailWord_2346149, baseEnd_2346149] using wordTrace_append hprefix tailTrace_2346149
  have hstable : (prefixWord ++ tailWord_2346149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346149).length < 2 ^ (prefixWord ++ tailWord_2346149).sum := by decide
  have hdescent : baseEnd_2346149 < baseStart_2346149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346156 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 7, 2, 2]
def baseStart_2346156 : Nat := 118140960795 + 2346156 * 2 ^ 59
def prefixEnd_2346156 : Nat := 4983230072969 + 3 ^ 40 * 2346156 * 2
def baseEnd_2346156 : Nat := 1204705718430027887560231

theorem tailTrace_2346156 : CollatzResearch.WordTrace tailWord_2346156 prefixEnd_2346156 1204705718430027887560231 := by
  unfold tailWord_2346156
  simp only [CollatzResearch.WordTrace]
  refine ⟨42785669644142489194613161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57047559525523318926150881 42785669644142489194613161)
  ·
    refine ⟨32089252233106866895959871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42785669644142489194613161 32089252233106866895959871)
    ·
      refine ⟨48133878349660300343939807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32089252233106866895959871 48133878349660300343939807)
      ·
        refine ⟨72200817524490450515909711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48133878349660300343939807 72200817524490450515909711)
        ·
          refine ⟨108301226286735675773864567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72200817524490450515909711 108301226286735675773864567)
          ·
            refine ⟨162451839430103513660796851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108301226286735675773864567 162451839430103513660796851)
            ·
              refine ⟨243677759145155270491195277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162451839430103513660796851 243677759145155270491195277)
              ·
                refine ⟨91379159679433226434198229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243677759145155270491195277 91379159679433226434198229)
                ·
                  refine ⟨2141699054986716244551521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91379159679433226434198229 2141699054986716244551521)
                  ·
                    refine ⟨1606274291240037183413641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2141699054986716244551521 1606274291240037183413641)
                    ·
                      refine ⟨1204705718430027887560231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606274291240037183413641 1204705718430027887560231)
                      ·
                        rfl

theorem cell23_2346156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_2346156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346156 prefixEnd_2346156 := by exact prefixLift 2346156
  have htrace : WordTrace (prefixWord ++ tailWord_2346156) baseStart_2346156 baseEnd_2346156 := by
    simpa [prefixWord, tailWord_2346156, baseEnd_2346156] using wordTrace_append hprefix tailTrace_2346156
  have hstable : (prefixWord ++ tailWord_2346156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346156).length < 2 ^ (prefixWord ++ tailWord_2346156).sum := by decide
  have hdescent : baseEnd_2346156 < baseStart_2346156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346159 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 5]
def baseStart_2346159 : Nat := 118140960795 + 2346159 * 2 ^ 59
def prefixEnd_2346159 : Nat := 4983230072969 + 3 ^ 40 * 2346159 * 2
def baseEnd_2346159 : Nat := 1204707258871991375822717

theorem tailTrace_2346159 : CollatzResearch.WordTrace tailWord_2346159 prefixEnd_2346159 1204707258871991375822717 := by
  unfold tailWord_2346159
  simp only [CollatzResearch.WordTrace]
  refine ⟨85571448707274109901585531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57047632471516073267723687 85571448707274109901585531)
  ·
    refine ⟨128357173060911164852378297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85571448707274109901585531 128357173060911164852378297)
    ·
      refine ⟨96267879795683373639283723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128357173060911164852378297 96267879795683373639283723)
      ·
        refine ⟨144401819693525060458925585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96267879795683373639283723 144401819693525060458925585)
        ·
          refine ⟨108301364770143795344194189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144401819693525060458925585 108301364770143795344194189)
          ·
            refine ⟨40613011788803923254072821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108301364770143795344194189 40613011788803923254072821)
            ·
              refine ⟨3807469855200367805069327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40613011788803923254072821 3807469855200367805069327)
              ·
                refine ⟨5711204782800551707603991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3807469855200367805069327 5711204782800551707603991)
                ·
                  refine ⟨8566807174200827561405987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5711204782800551707603991 8566807174200827561405987)
                  ·
                    refine ⟨12850210761301241342108981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8566807174200827561405987 12850210761301241342108981)
                    ·
                      refine ⟨1204707258871991375822717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12850210761301241342108981 1204707258871991375822717)
                      ·
                        rfl

theorem cell23_2346159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_2346159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346159 prefixEnd_2346159 := by exact prefixLift 2346159
  have htrace : WordTrace (prefixWord ++ tailWord_2346159) baseStart_2346159 baseEnd_2346159 := by
    simpa [prefixWord, tailWord_2346159, baseEnd_2346159] using wordTrace_append hprefix tailTrace_2346159
  have hstable : (prefixWord ++ tailWord_2346159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346159).length < 2 ^ (prefixWord ++ tailWord_2346159).sum := by decide
  have hdescent : baseEnd_2346159 < baseStart_2346159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346162 : List Nat := [3, 2, 1, 1, 1, 15]
def baseStart_2346162 : Nat := 118140960795 + 2346162 * 2 ^ 59
def prefixEnd_2346162 : Nat := 4983230072969 + 3 ^ 40 * 2346162 * 2
def baseEnd_2346162 : Nat := 4957649379892818370721

theorem tailTrace_2346162 : CollatzResearch.WordTrace tailWord_2346162 prefixEnd_2346162 4957649379892818370721 := by
  unfold tailWord_2346162
  simp only [CollatzResearch.WordTrace]
  refine ⟨21392889531565810353486185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57047705417508827609296493 21392889531565810353486185)
  ·
    refine ⟨16044667148674357765114639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21392889531565810353486185 16044667148674357765114639)
    ·
      refine ⟨24067000723011536647671959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16044667148674357765114639 24067000723011536647671959)
      ·
        refine ⟨36100501084517304971507939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24067000723011536647671959 36100501084517304971507939)
        ·
          refine ⟨54150751626775957457261909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36100501084517304971507939 54150751626775957457261909)
          ·
            refine ⟨4957649379892818370721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 54150751626775957457261909 4957649379892818370721)
            ·
              rfl

theorem cell23_2346162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 15].length) (baseStart_2346162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346162 prefixEnd_2346162 := by exact prefixLift 2346162
  have htrace : WordTrace (prefixWord ++ tailWord_2346162) baseStart_2346162 baseEnd_2346162 := by
    simpa [prefixWord, tailWord_2346162, baseEnd_2346162] using wordTrace_append hprefix tailTrace_2346162
  have hstable : (prefixWord ++ tailWord_2346162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346162).length < 2 ^ (prefixWord ++ tailWord_2346162).sum := by decide
  have hdescent : baseEnd_2346162 < baseStart_2346162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346186 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_2346186 : Nat := 118140960795 + 2346186 * 2 ^ 59
def prefixEnd_2346186 : Nat := 4983230072969 + 3 ^ 40 * 2346186 * 2
def baseEnd_2346186 : Nat := 1204721122849662770185093

theorem tailTrace_2346186 : CollatzResearch.WordTrace tailWord_2346186 prefixEnd_2346186 1204721122849662770185093 := by
  unfold tailWord_2346186
  simp only [CollatzResearch.WordTrace]
  refine ⟨21393108369544073378204603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57048288985450862341878941 21393108369544073378204603)
  ·
    refine ⟨32089662554316110067306905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21393108369544073378204603 32089662554316110067306905)
    ·
      refine ⟨24067246915737082550480179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32089662554316110067306905 24067246915737082550480179)
      ·
        refine ⟨36100870373605623825720269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24067246915737082550480179 36100870373605623825720269)
        ·
          refine ⟨13537826390102108934645101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36100870373605623825720269 13537826390102108934645101)
          ·
            refine ⟨5076684896288290850491913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13537826390102108934645101 5076684896288290850491913)
            ·
              refine ⟨3807513672216218137868935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5076684896288290850491913 3807513672216218137868935)
              ·
                refine ⟨5711270508324327206803403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3807513672216218137868935 5711270508324327206803403)
                ·
                  refine ⟨8566905762486490810205105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5711270508324327206803403 8566905762486490810205105)
                  ·
                    refine ⟨6425179321864868107653829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8566905762486490810205105 6425179321864868107653829)
                    ·
                      refine ⟨1204721122849662770185093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6425179321864868107653829 1204721122849662770185093)
                      ·
                        rfl

theorem cell23_2346186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_2346186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346186 prefixEnd_2346186 := by exact prefixLift 2346186
  have htrace : WordTrace (prefixWord ++ tailWord_2346186) baseStart_2346186 baseEnd_2346186 := by
    simpa [prefixWord, tailWord_2346186, baseEnd_2346186] using wordTrace_append hprefix tailTrace_2346186
  have hstable : (prefixWord ++ tailWord_2346186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346186).length < 2 ^ (prefixWord ++ tailWord_2346186).sum := by decide
  have hdescent : baseEnd_2346186 < baseStart_2346186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346190 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_2346190 : Nat := 118140960795 + 2346190 * 2 ^ 59
def prefixEnd_2346190 : Nat := 4983230072969 + 3 ^ 40 * 2346190 * 2
def baseEnd_2346190 : Nat := 1204723176772280754535075

theorem tailTrace_2346190 : CollatzResearch.WordTrace tailWord_2346190 prefixEnd_2346190 1204723176772280754535075 := by
  unfold tailWord_2346190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10696572421270225274495503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57048386246774534797309349 10696572421270225274495503)
  ·
    refine ⟨16044858631905337911743255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10696572421270225274495503 16044858631905337911743255)
    ·
      refine ⟨24067287947858006867614883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16044858631905337911743255 24067287947858006867614883)
      ·
        refine ⟨36100931921787010301422325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24067287947858006867614883 36100931921787010301422325)
        ·
          refine ⟨3384462367667532215758343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36100931921787010301422325 3384462367667532215758343)
          ·
            refine ⟨5076693551501298323637515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384462367667532215758343 5076693551501298323637515)
            ·
              refine ⟨7615040327251947485456273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076693551501298323637515 7615040327251947485456273)
              ·
                refine ⟨5711280245438960614092205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7615040327251947485456273 5711280245438960614092205)
                ·
                  refine ⟨2141730092039610230284577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5711280245438960614092205 2141730092039610230284577)
                  ·
                    refine ⟨1606297569029707672713433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2141730092039610230284577 1606297569029707672713433)
                    ·
                      refine ⟨1204723176772280754535075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606297569029707672713433 1204723176772280754535075)
                      ·
                        rfl

theorem cell23_2346190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_2346190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346190 prefixEnd_2346190 := by exact prefixLift 2346190
  have htrace : WordTrace (prefixWord ++ tailWord_2346190) baseStart_2346190 baseEnd_2346190 := by
    simpa [prefixWord, tailWord_2346190, baseEnd_2346190] using wordTrace_append hprefix tailTrace_2346190
  have hstable : (prefixWord ++ tailWord_2346190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346190).length < 2 ^ (prefixWord ++ tailWord_2346190).sum := by decide
  have hdescent : baseEnd_2346190 < baseStart_2346190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346223 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 3]
def baseStart_2346223 : Nat := 118140960795 + 2346223 * 2 ^ 59
def prefixEnd_2346223 : Nat := 4983230072969 + 3 ^ 40 * 2346223 * 2
def baseEnd_2346223 : Nat := 1204740121633879125422423

theorem tailTrace_2346223 : CollatzResearch.WordTrace tailWord_2346223 prefixEnd_2346223 1204740121633879125422423 := by
  unfold tailWord_2346223
  simp only [CollatzResearch.WordTrace]
  refine ⟨85573782979042248831915323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57049188652694832554610215 85573782979042248831915323)
  ·
    refine ⟨128360674468563373247872985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85573782979042248831915323 128360674468563373247872985)
    ·
      refine ⟨96270505851422529935904739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128360674468563373247872985 96270505851422529935904739)
      ·
        refine ⟨144405758777133794903857109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96270505851422529935904739 144405758777133794903857109)
        ·
          refine ⟨3384509971339073318059151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 144405758777133794903857109 3384509971339073318059151)
          ·
            refine ⟨5076764957008609977088727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384509971339073318059151 5076764957008609977088727)
            ·
              refine ⟨7615147435512914965633091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076764957008609977088727 7615147435512914965633091)
              ·
                refine ⟨11422721153269372448449637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7615147435512914965633091 11422721153269372448449637)
                ·
                  refine ⟨2141760216238007334084307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11422721153269372448449637 2141760216238007334084307)
                  ·
                    refine ⟨3212640324357011001126461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2141760216238007334084307 3212640324357011001126461)
                    ·
                      refine ⟨1204740121633879125422423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3212640324357011001126461 1204740121633879125422423)
                      ·
                        rfl

theorem cell23_2346223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 3].length) (baseStart_2346223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346223 prefixEnd_2346223 := by exact prefixLift 2346223
  have htrace : WordTrace (prefixWord ++ tailWord_2346223) baseStart_2346223 baseEnd_2346223 := by
    simpa [prefixWord, tailWord_2346223, baseEnd_2346223] using wordTrace_append hprefix tailTrace_2346223
  have hstable : (prefixWord ++ tailWord_2346223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346223).length < 2 ^ (prefixWord ++ tailWord_2346223).sum := by decide
  have hdescent : baseEnd_2346223 < baseStart_2346223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346239 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 2, 6]
def baseStart_2346239 : Nat := 118140960795 + 2346239 * 2 ^ 59
def prefixEnd_2346239 : Nat := 4983230072969 + 3 ^ 40 * 2346239 * 2
def baseEnd_2346239 : Nat := 401582779108117020940783

theorem tailTrace_2346239 : CollatzResearch.WordTrace tailWord_2346239 prefixEnd_2346239 401582779108117020940783 := by
  unfold tailWord_2346239
  simp only [CollatzResearch.WordTrace]
  refine ⟨85574366546984283564497771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57049577697989522376331847 85574366546984283564497771)
  ·
    refine ⟨128361549820476425346746657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85574366546984283564497771 128361549820476425346746657)
    ·
      refine ⟨96271162365357319010059993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128361549820476425346746657 96271162365357319010059993)
      ·
        refine ⟨72203371774017989257544995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96271162365357319010059993 72203371774017989257544995)
        ·
          refine ⟨108305057661026983886317493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72203371774017989257544995 108305057661026983886317493)
          ·
            refine ⟨10153599155721279739342265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108305057661026983886317493 10153599155721279739342265)
            ·
              refine ⟨7615199366790959804506699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10153599155721279739342265 7615199366790959804506699)
              ·
                refine ⟨11422799050186439706760049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7615199366790959804506699 11422799050186439706760049)
                ·
                  refine ⟨8567099287639829780070037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11422799050186439706760049 8567099287639829780070037)
                  ·
                    refine ⟨401582779108117020940783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8567099287639829780070037 401582779108117020940783)
                    ·
                      rfl

theorem cell23_2346239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_2346239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346239 prefixEnd_2346239 := by exact prefixLift 2346239
  have htrace : WordTrace (prefixWord ++ tailWord_2346239) baseStart_2346239 baseEnd_2346239 := by
    simpa [prefixWord, tailWord_2346239, baseEnd_2346239] using wordTrace_append hprefix tailTrace_2346239
  have hstable : (prefixWord ++ tailWord_2346239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346239).length < 2 ^ (prefixWord ++ tailWord_2346239).sum := by decide
  have hdescent : baseEnd_2346239 < baseStart_2346239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346249 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_2346249 : Nat := 118140960795 + 2346249 * 2 ^ 59
def prefixEnd_2346249 : Nat := 4983230072969 + 3 ^ 40 * 2346249 * 2
def baseEnd_2346249 : Nat := 1204753472130896023697303

theorem tailTrace_2346249 : CollatzResearch.WordTrace tailWord_2346249 prefixEnd_2346249 1204753472130896023697303 := by
  unfold tailWord_2346249
  simp only [CollatzResearch.WordTrace]
  refine ⟨85574731276948055272361801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57049820851298703514907867 85574731276948055272361801)
  ·
    refine ⟨64181048457711041454271351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85574731276948055272361801 64181048457711041454271351)
    ·
      refine ⟨96271572686566562181407027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64181048457711041454271351 96271572686566562181407027)
      ·
        refine ⟨144407359029849843272110541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96271572686566562181407027 144407359029849843272110541)
        ·
          refine ⟨54152759636193691227041453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144407359029849843272110541 54152759636193691227041453)
          ·
            refine ⟨20307284863572634210140545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54152759636193691227041453 20307284863572634210140545)
            ·
              refine ⟨15230463647679475657605409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20307284863572634210140545 15230463647679475657605409)
              ·
                refine ⟨11422847735759606743204057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15230463647679475657605409 11422847735759606743204057)
                ·
                  refine ⟨8567135801819705057403043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11422847735759606743204057 8567135801819705057403043)
                  ·
                    refine ⟨12850703702729557586104565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8567135801819705057403043 12850703702729557586104565)
                    ·
                      refine ⟨1204753472130896023697303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12850703702729557586104565 1204753472130896023697303)
                      ·
                        rfl

theorem cell23_2346249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_2346249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346249 prefixEnd_2346249 := by exact prefixLift 2346249
  have htrace : WordTrace (prefixWord ++ tailWord_2346249) baseStart_2346249 baseEnd_2346249 := by
    simpa [prefixWord, tailWord_2346249, baseEnd_2346249] using wordTrace_append hprefix tailTrace_2346249
  have hstable : (prefixWord ++ tailWord_2346249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346249).length < 2 ^ (prefixWord ++ tailWord_2346249).sum := by decide
  have hdescent : baseEnd_2346249 < baseStart_2346249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346258 : List Nat := [3, 2, 4, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2346258 : Nat := 118140960795 + 2346258 * 2 ^ 59
def prefixEnd_2346258 : Nat := 4983230072969 + 3 ^ 40 * 2346258 * 2
def baseEnd_2346258 : Nat := 1204758093456786488484763

theorem tailTrace_2346258 : CollatzResearch.WordTrace tailWord_2346258 prefixEnd_2346258 1204758093456786488484763 := by
  unfold tailWord_2346258
  simp only [CollatzResearch.WordTrace]
  refine ⟨21393764883478862452359857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57050039689276966539626285 21393764883478862452359857)
  ·
    refine ⟨16045323662609146839269893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21393764883478862452359857 16045323662609146839269893)
    ·
      refine ⟨3008498186739215032363105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16045323662609146839269893 3008498186739215032363105)
      ·
        refine ⟨2256373640054411274272329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3008498186739215032363105 2256373640054411274272329)
        ·
          refine ⟨1692280230040808455704247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2256373640054411274272329 1692280230040808455704247)
          ·
            refine ⟨2538420345061212683556371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692280230040808455704247 2538420345061212683556371)
            ·
              refine ⟨3807630517591819025334557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538420345061212683556371 3807630517591819025334557)
              ·
                refine ⟨1427861444096932134500459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3807630517591819025334557 1427861444096932134500459)
                ·
                  refine ⟨2141792166145398201750689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427861444096932134500459 2141792166145398201750689)
                  ·
                    refine ⟨1606344124609048651313017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2141792166145398201750689 1606344124609048651313017)
                    ·
                      refine ⟨1204758093456786488484763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606344124609048651313017 1204758093456786488484763)
                      ·
                        rfl

theorem cell23_2346258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2346258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346258 prefixEnd_2346258 := by exact prefixLift 2346258
  have htrace : WordTrace (prefixWord ++ tailWord_2346258) baseStart_2346258 baseEnd_2346258 := by
    simpa [prefixWord, tailWord_2346258, baseEnd_2346258] using wordTrace_append hprefix tailTrace_2346258
  have hstable : (prefixWord ++ tailWord_2346258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346258).length < 2 ^ (prefixWord ++ tailWord_2346258).sum := by decide
  have hdescent : baseEnd_2346258 < baseStart_2346258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346263 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 6, 2, 2]
def baseStart_2346263 : Nat := 118140960795 + 2346263 * 2 ^ 59
def prefixEnd_2346263 : Nat := 4983230072969 + 3 ^ 40 * 2346263 * 2
def baseEnd_2346263 : Nat := 1204760660860058968922239

theorem tailTrace_2346263 : CollatzResearch.WordTrace tailWord_2346263 prefixEnd_2346263 1204760660860058968922239 := by
  unfold tailWord_2346263
  simp only [CollatzResearch.WordTrace]
  refine ⟨85575241898897335663371443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57050161265931557108914295 85575241898897335663371443)
  ·
    refine ⟨128362862848346003495057165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85575241898897335663371443 128362862848346003495057165)
    ·
      refine ⟨48136073568129751310646437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128362862848346003495057165 48136073568129751310646437)
      ·
        refine ⟨9025513794024328370746207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48136073568129751310646437 9025513794024328370746207)
        ·
          refine ⟨13538270691036492556119311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9025513794024328370746207 13538270691036492556119311)
          ·
            refine ⟨20307406036554738834178967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13538270691036492556119311 20307406036554738834178967)
            ·
              refine ⟨30461109054832108251268451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20307406036554738834178967 30461109054832108251268451)
              ·
                refine ⟨45691663582248162376902677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30461109054832108251268451 45691663582248162376902677)
                ·
                  refine ⟨2141796730417882611417313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45691663582248162376902677 2141796730417882611417313)
                  ·
                    refine ⟨1606347547813411958562985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2141796730417882611417313 1606347547813411958562985)
                    ·
                      refine ⟨1204760660860058968922239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606347547813411958562985 1204760660860058968922239)
                      ·
                        rfl

theorem cell23_2346263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_2346263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346263 prefixEnd_2346263 := by exact prefixLift 2346263
  have htrace : WordTrace (prefixWord ++ tailWord_2346263) baseStart_2346263 baseEnd_2346263 := by
    simpa [prefixWord, tailWord_2346263, baseEnd_2346263] using wordTrace_append hprefix tailTrace_2346263
  have hstable : (prefixWord ++ tailWord_2346263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346263).length < 2 ^ (prefixWord ++ tailWord_2346263).sum := by decide
  have hdescent : baseEnd_2346263 < baseStart_2346263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346266 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_2346266 : Nat := 118140960795 + 2346266 * 2 ^ 59
def prefixEnd_2346266 : Nat := 4983230072969 + 3 ^ 40 * 2346266 * 2
def baseEnd_2346266 : Nat := 1204762201302022457184725

theorem tailTrace_2346266 : CollatzResearch.WordTrace tailWord_2346266 prefixEnd_2346266 1204762201302022457184725 := by
  unfold tailWord_2346266
  simp only [CollatzResearch.WordTrace]
  refine ⟨21393837829471616793932663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57050234211924311450487101 21393837829471616793932663)
  ·
    refine ⟨32090756744207425190898995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21393837829471616793932663 32090756744207425190898995)
    ·
      refine ⟨48136135116311137786348493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32090756744207425190898995 48136135116311137786348493)
      ·
        refine ⟨18051050668616676669880685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48136135116311137786348493 18051050668616676669880685)
        ·
          refine ⟨6769144000731253751205257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18051050668616676669880685 6769144000731253751205257)
          ·
            refine ⟨5076858000548440313403943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6769144000731253751205257 5076858000548440313403943)
            ·
              refine ⟨7615287000822660470105915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076858000548440313403943 7615287000822660470105915)
              ·
                refine ⟨11422930501233990705158873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7615287000822660470105915 11422930501233990705158873)
                ·
                  refine ⟨8567197875925493028869155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11422930501233990705158873 8567197875925493028869155)
                  ·
                    refine ⟨12850796813888239543303733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8567197875925493028869155 12850796813888239543303733)
                    ·
                      refine ⟨1204762201302022457184725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12850796813888239543303733 1204762201302022457184725)
                      ·
                        rfl

theorem cell23_2346266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_2346266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346266 prefixEnd_2346266 := by exact prefixLift 2346266
  have htrace : WordTrace (prefixWord ++ tailWord_2346266) baseStart_2346266 baseEnd_2346266 := by
    simpa [prefixWord, tailWord_2346266, baseEnd_2346266] using wordTrace_append hprefix tailTrace_2346266
  have hstable : (prefixWord ++ tailWord_2346266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346266).length < 2 ^ (prefixWord ++ tailWord_2346266).sum := by decide
  have hdescent : baseEnd_2346266 < baseStart_2346266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346280 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_2346280 : Nat := 118140960795 + 2346280 * 2 ^ 59
def prefixEnd_2346280 : Nat := 4983230072969 + 3 ^ 40 * 2346280 * 2
def baseEnd_2346280 : Nat := 1204769390031185402409661

theorem tailTrace_2346280 : CollatzResearch.WordTrace tailWord_2346280 prefixEnd_2346280 1204769390031185402409661 := by
  unfold tailWord_2346280
  simp only [CollatzResearch.WordTrace]
  refine ⟨42787930969917873783370147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57050574626557165044493529 42787930969917873783370147)
  ·
    refine ⟨64181896454876810675055221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42787930969917873783370147 64181896454876810675055221)
    ·
      refine ⟨6017052792644701000786427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64181896454876810675055221 6017052792644701000786427)
      ·
        refine ⟨9025579188967051501179641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6017052792644701000786427 9025579188967051501179641)
        ·
          refine ⟨6769184391725288625884731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9025579188967051501179641 6769184391725288625884731)
          ·
            refine ⟨10153776587587932938827097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6769184391725288625884731 10153776587587932938827097)
            ·
              refine ⟨7615332440690949704120323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10153776587587932938827097 7615332440690949704120323)
              ·
                refine ⟨11422998661036424556180485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7615332440690949704120323 11422998661036424556180485)
                ·
                  refine ⟨2141812248944329604283841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11422998661036424556180485 2141812248944329604283841)
                  ·
                    refine ⟨1606359186708247203212881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2141812248944329604283841 1606359186708247203212881)
                    ·
                      refine ⟨1204769390031185402409661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606359186708247203212881 1204769390031185402409661)
                      ·
                        rfl

theorem cell23_2346280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_2346280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346280 prefixEnd_2346280 := by exact prefixLift 2346280
  have htrace : WordTrace (prefixWord ++ tailWord_2346280) baseStart_2346280 baseEnd_2346280 := by
    simpa [prefixWord, tailWord_2346280, baseEnd_2346280] using wordTrace_append hprefix tailTrace_2346280
  have hstable : (prefixWord ++ tailWord_2346280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346280).length < 2 ^ (prefixWord ++ tailWord_2346280).sum := by decide
  have hdescent : baseEnd_2346280 < baseStart_2346280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346297 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2346297 : Nat := 118140960795 + 2346297 * 2 ^ 59
def prefixEnd_2346297 : Nat := 4983230072969 + 3 ^ 40 * 2346297 * 2
def baseEnd_2346297 : Nat := 1204778119202311835897083

theorem tailTrace_2346297 : CollatzResearch.WordTrace tailWord_2346297 prefixEnd_2346297 1204778119202311835897083 := by
  unfold tailWord_2346297
  simp only [CollatzResearch.WordTrace]
  refine ⟨85576481980774159470109145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57050987987182772980072763 85576481980774159470109145)
  ·
    refine ⟨64182361485580619602581859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85576481980774159470109145 64182361485580619602581859)
    ·
      refine ⟨96273542228370929403872789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64182361485580619602581859 96273542228370929403872789)
      ·
        refine ⟨4512822291954887315806537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96273542228370929403872789 4512822291954887315806537)
        ·
          refine ⟨3384616718966165486854903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4512822291954887315806537 3384616718966165486854903)
          ·
            refine ⟨5076925078449248230282355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384616718966165486854903 5076925078449248230282355)
            ·
              refine ⟨7615387617673872345423533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076925078449248230282355 7615387617673872345423533)
              ·
                refine ⟨2855770356627702129533825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7615387617673872345423533 2855770356627702129533825)
                ·
                  refine ⟨2141827767470776597150369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2855770356627702129533825 2141827767470776597150369)
                  ·
                    refine ⟨1606370825603082447862777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2141827767470776597150369 1606370825603082447862777)
                    ·
                      refine ⟨1204778119202311835897083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606370825603082447862777 1204778119202311835897083)
                      ·
                        rfl

theorem cell23_2346297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2346297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346297 prefixEnd_2346297 := by exact prefixLift 2346297
  have htrace : WordTrace (prefixWord ++ tailWord_2346297) baseStart_2346297 baseEnd_2346297 := by
    simpa [prefixWord, tailWord_2346297, baseEnd_2346297] using wordTrace_append hprefix tailTrace_2346297
  have hstable : (prefixWord ++ tailWord_2346297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346297).length < 2 ^ (prefixWord ++ tailWord_2346297).sum := by decide
  have hdescent : baseEnd_2346297 < baseStart_2346297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346316 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_2346316 : Nat := 118140960795 + 2346316 * 2 ^ 59
def prefixEnd_2346316 : Nat := 4983230072969 + 3 ^ 40 * 2346316 * 2
def baseEnd_2346316 : Nat := 401595958444915753853165

theorem tailTrace_2346316 : CollatzResearch.WordTrace tailWord_2346316 prefixEnd_2346316 401595958444915753853165 := by
  unfold tailWord_2346316
  simp only [CollatzResearch.WordTrace]
  refine ⟨42788587483852662857525401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57051449978470217143367201 42788587483852662857525401)
  ·
    refine ⟨32091440612889497143144051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42788587483852662857525401 32091440612889497143144051)
    ·
      refine ⟨48137160919334245714716077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32091440612889497143144051 48137160919334245714716077)
      ·
        refine ⟨18051435344750342143018529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48137160919334245714716077 18051435344750342143018529)
        ·
          refine ⟨13538576508562756607263897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18051435344750342143018529 13538576508562756607263897)
          ·
            refine ⟨10153932381422067455447923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13538576508562756607263897 10153932381422067455447923)
            ·
              refine ⟨15230898572133101183171885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10153932381422067455447923 15230898572133101183171885)
              ·
                refine ⟨5711586964549912943689457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15230898572133101183171885 5711586964549912943689457)
                ·
                  refine ⟨4283690223412434707767093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5711586964549912943689457 4283690223412434707767093)
                  ·
                    refine ⟨401595958444915753853165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4283690223412434707767093 401595958444915753853165)
                    ·
                      rfl

theorem cell23_2346316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_2346316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346316 prefixEnd_2346316 := by exact prefixLift 2346316
  have htrace : WordTrace (prefixWord ++ tailWord_2346316) baseStart_2346316 baseEnd_2346316 := by
    simpa [prefixWord, tailWord_2346316, baseEnd_2346316] using wordTrace_append hprefix tailTrace_2346316
  have hstable : (prefixWord ++ tailWord_2346316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346316).length < 2 ^ (prefixWord ++ tailWord_2346316).sum := by decide
  have hdescent : baseEnd_2346316 < baseStart_2346316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346319 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_2346319 : Nat := 118140960795 + 2346319 * 2 ^ 59
def prefixEnd_2346319 : Nat := 4983230072969 + 3 ^ 40 * 2346319 * 2
def baseEnd_2346319 : Nat := 1204789415776710749821981

theorem tailTrace_2346319 : CollatzResearch.WordTrace tailWord_2346319 prefixEnd_2346319 1204789415776710749821981 := by
  unfold tailWord_2346319
  simp only [CollatzResearch.WordTrace]
  refine ⟨85577284386694457227410011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57051522924462971484940007 85577284386694457227410011)
  ·
    refine ⟨128365926580041685841115017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85577284386694457227410011 128365926580041685841115017)
    ·
      refine ⟨96274444935031264380836263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128365926580041685841115017 96274444935031264380836263)
      ·
        refine ⟨144411667402546896571254395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96274444935031264380836263 144411667402546896571254395)
        ·
          refine ⟨216617501103820344856881593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144411667402546896571254395 216617501103820344856881593)
          ·
            refine ⟨162463125827865258642661195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216617501103820344856881593 162463125827865258642661195)
            ·
              refine ⟨243694688741797887963991793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162463125827865258642661195 243694688741797887963991793)
              ·
                refine ⟨182771016556348415972993845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243694688741797887963991793 182771016556348415972993845)
                ·
                  refine ⟨17134782802157663997468173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182771016556348415972993845 17134782802157663997468173)
                  ·
                    refine ⟨6425543550809123999050565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17134782802157663997468173 6425543550809123999050565)
                    ·
                      refine ⟨1204789415776710749821981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6425543550809123999050565 1204789415776710749821981)
                      ·
                        rfl

theorem cell23_2346319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_2346319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346319 prefixEnd_2346319 := by exact prefixLift 2346319
  have htrace : WordTrace (prefixWord ++ tailWord_2346319) baseStart_2346319 baseEnd_2346319 := by
    simpa [prefixWord, tailWord_2346319, baseEnd_2346319] using wordTrace_append hprefix tailTrace_2346319
  have hstable : (prefixWord ++ tailWord_2346319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346319).length < 2 ^ (prefixWord ++ tailWord_2346319).sum := by decide
  have hdescent : baseEnd_2346319 < baseStart_2346319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346370 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2346370 : Nat := 118140960795 + 2346370 * 2 ^ 59
def prefixEnd_2346370 : Nat := 4983230072969 + 3 ^ 40 * 2346370 * 2
def baseEnd_2346370 : Nat := 1204815603290090050284247

theorem tailTrace_2346370 : CollatzResearch.WordTrace tailWord_2346370 prefixEnd_2346370 1204815603290090050284247 := by
  unfold tailWord_2346370
  simp only [CollatzResearch.WordTrace]
  refine ⟨21394786127377423234379141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57052763006339795291677709 21394786127377423234379141)
  ·
    refine ⟨4011522398883266856446089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21394786127377423234379141 4011522398883266856446089)
    ·
      refine ⟨3008641799162450142334567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4011522398883266856446089 3008641799162450142334567)
      ·
        refine ⟨4512962698743675213501851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008641799162450142334567 4512962698743675213501851)
        ·
          refine ⟨6769444048115512820252777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512962698743675213501851 6769444048115512820252777)
          ·
            refine ⟨5077083036086634615189583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6769444048115512820252777 5077083036086634615189583)
            ·
              refine ⟨7615624554129951922784375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077083036086634615189583 7615624554129951922784375)
              ·
                refine ⟨11423436831194927884176563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7615624554129951922784375 11423436831194927884176563)
                ·
                  refine ⟨17135155246792391826264845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11423436831194927884176563 17135155246792391826264845)
                  ·
                    refine ⟨6425683217547146934849317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17135155246792391826264845 6425683217547146934849317)
                    ·
                      refine ⟨1204815603290090050284247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6425683217547146934849317 1204815603290090050284247)
                      ·
                        rfl

theorem cell23_2346370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2346370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346370 prefixEnd_2346370 := by exact prefixLift 2346370
  have htrace : WordTrace (prefixWord ++ tailWord_2346370) baseStart_2346370 baseEnd_2346370 := by
    simpa [prefixWord, tailWord_2346370, baseEnd_2346370] using wordTrace_append hprefix tailTrace_2346370
  have hstable : (prefixWord ++ tailWord_2346370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346370).length < 2 ^ (prefixWord ++ tailWord_2346370).sum := by decide
  have hdescent : baseEnd_2346370 < baseStart_2346370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346373 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_2346373 : Nat := 118140960795 + 2346373 * 2 ^ 59
def prefixEnd_2346373 : Nat := 4983230072969 + 3 ^ 40 * 2346373 * 2
def baseEnd_2346373 : Nat := 1204817143732053538546733

theorem tailTrace_2346373 : CollatzResearch.WordTrace tailWord_2346373 prefixEnd_2346373 1204817143732053538546733 := by
  unfold tailWord_2346373
  simp only [CollatzResearch.WordTrace]
  refine ⟨85579253928498824449875773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57052835952332549633250515 85579253928498824449875773)
  ·
    refine ⟨32092220223187059168703415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85579253928498824449875773 32092220223187059168703415)
    ·
      refine ⟨48138330334780588753055123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32092220223187059168703415 48138330334780588753055123)
      ·
        refine ⟨72207495502170883129582685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48138330334780588753055123 72207495502170883129582685)
        ·
          refine ⟨27077810813314081173593507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72207495502170883129582685 27077810813314081173593507)
          ·
            refine ⟨40616716219971121760390261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27077810813314081173593507 40616716219971121760390261)
            ·
              refine ⟨3807817145622292665036587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40616716219971121760390261 3807817145622292665036587)
              ·
                refine ⟨5711725718433438997554881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3807817145622292665036587 5711725718433438997554881)
                ·
                  refine ⟨4283794288825079248166161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5711725718433438997554881 4283794288825079248166161)
                  ·
                    refine ⟨3212845716618809436124621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283794288825079248166161 3212845716618809436124621)
                    ·
                      refine ⟨1204817143732053538546733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3212845716618809436124621 1204817143732053538546733)
                      ·
                        rfl

theorem cell23_2346373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_2346373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346373 prefixEnd_2346373 := by exact prefixLift 2346373
  have htrace : WordTrace (prefixWord ++ tailWord_2346373) baseStart_2346373 baseEnd_2346373 := by
    simpa [prefixWord, tailWord_2346373, baseEnd_2346373] using wordTrace_append hprefix tailTrace_2346373
  have hstable : (prefixWord ++ tailWord_2346373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346373).length < 2 ^ (prefixWord ++ tailWord_2346373).sum := by decide
  have hdescent : baseEnd_2346373 < baseStart_2346373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346380 : List Nat := [2, 2, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_2346380 : Nat := 118140960795 + 2346380 * 2 ^ 59
def prefixEnd_2346380 : Nat := 4983230072969 + 3 ^ 40 * 2346380 * 2
def baseEnd_2346380 : Nat := 401606912698878337053067

theorem tailTrace_2346380 : CollatzResearch.WordTrace tailWord_2346380 prefixEnd_2346380 401606912698878337053067 := by
  unfold tailWord_2346380
  simp only [CollatzResearch.WordTrace]
  refine ⟨42789754619736732322690297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57053006159648976430253729 42789754619736732322690297)
  ·
    refine ⟨32092315964802549242017723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42789754619736732322690297 32092315964802549242017723)
    ·
      refine ⟨48138473947203823863026585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32092315964802549242017723 48138473947203823863026585)
      ·
        refine ⟨36103855460402867897269939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48138473947203823863026585 36103855460402867897269939)
        ·
          refine ⟨54155783190604301845904909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36103855460402867897269939 54155783190604301845904909)
          ·
            refine ⟨20308418696476613192214341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54155783190604301845904909 20308418696476613192214341)
            ·
              refine ⟨3807828505589364973540189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20308418696476613192214341 3807828505589364973540189)
              ·
                refine ⟨1427935689596011865077571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3807828505589364973540189 1427935689596011865077571)
                ·
                  refine ⟨2141903534394017797616357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427935689596011865077571 2141903534394017797616357)
                  ·
                    refine ⟨401606912698878337053067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2141903534394017797616357 401606912698878337053067)
                    ·
                      rfl

theorem cell23_2346380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_2346380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346380 prefixEnd_2346380 := by exact prefixLift 2346380
  have htrace : WordTrace (prefixWord ++ tailWord_2346380) baseStart_2346380 baseEnd_2346380 := by
    simpa [prefixWord, tailWord_2346380, baseEnd_2346380] using wordTrace_append hprefix tailTrace_2346380
  have hstable : (prefixWord ++ tailWord_2346380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346380).length < 2 ^ (prefixWord ++ tailWord_2346380).sum := by decide
  have hdescent : baseEnd_2346380 < baseStart_2346380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346393 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 6]
def baseStart_2346393 : Nat := 118140960795 + 2346393 * 2 ^ 59
def prefixEnd_2346393 : Nat := 4983230072969 + 3 ^ 40 * 2346393 * 2
def baseEnd_2346393 : Nat := 133869712593904828921849

theorem tailTrace_2346393 : CollatzResearch.WordTrace tailWord_2346393 prefixEnd_2346393 133869712593904828921849 := by
  unfold tailWord_2346393
  simp only [CollatzResearch.WordTrace]
  refine ⟨85579983388426367865603833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57053322258950911910402555 85579983388426367865603833)
  ·
    refine ⟨64184987541319775899202875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85579983388426367865603833 64184987541319775899202875)
    ·
      refine ⟨96277481311979663848804313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64184987541319775899202875 96277481311979663848804313)
      ·
        refine ⟨72208110983984747886603235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96277481311979663848804313 72208110983984747886603235)
        ·
          refine ⟨108312166475977121829904853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72208110983984747886603235 108312166475977121829904853)
          ·
            refine ⟨2538566401780713792888395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 108312166475977121829904853 2538566401780713792888395)
            ·
              refine ⟨3807849602671070689332593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538566401780713792888395 3807849602671070689332593)
              ·
                refine ⟨2855887202003303016999445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3807849602671070689332593 2855887202003303016999445)
                ·
                  refine ⟨133869712593904828921849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2855887202003303016999445 133869712593904828921849)
                  ·
                    rfl

theorem cell23_2346393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 6].length) (baseStart_2346393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346393 prefixEnd_2346393 := by exact prefixLift 2346393
  have htrace : WordTrace (prefixWord ++ tailWord_2346393) baseStart_2346393 baseEnd_2346393 := by
    simpa [prefixWord, tailWord_2346393, baseEnd_2346393] using wordTrace_append hprefix tailTrace_2346393
  have hstable : (prefixWord ++ tailWord_2346393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346393).length < 2 ^ (prefixWord ++ tailWord_2346393).sum := by decide
  have hdescent : baseEnd_2346393 < baseStart_2346393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346423 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 1, 5]
def baseStart_2346423 : Nat := 118140960795 + 2346423 * 2 ^ 59
def prefixEnd_2346423 : Nat := 4983230072969 + 3 ^ 40 * 2346423 * 2
def baseEnd_2346423 : Nat := 401614272588259447640501

theorem tailTrace_2346423 : CollatzResearch.WordTrace tailWord_2346423 prefixEnd_2346423 401614272588259447640501 := by
  unfold tailWord_2346423
  simp only [CollatzResearch.WordTrace]
  refine ⟨85581077578317682989195923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57054051718878455326130615 85581077578317682989195923)
  ·
    refine ⟨128371616367476524483793885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85581077578317682989195923 128371616367476524483793885)
    ·
      refine ⟨48139356137803696681422707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128371616367476524483793885 48139356137803696681422707)
      ·
        refine ⟨72209034206705545022134061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48139356137803696681422707 72209034206705545022134061)
        ·
          refine ⟨27078387827514579383300273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72209034206705545022134061 27078387827514579383300273)
          ·
            refine ⟨20308790870635934537475205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27078387827514579383300273 20308790870635934537475205)
            ·
              refine ⟨3807898288244237725776601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20308790870635934537475205 3807898288244237725776601)
              ·
                refine ⟨2855923716183178294332451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3807898288244237725776601 2855923716183178294332451)
                ·
                  refine ⟨4283885574274767441498677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855923716183178294332451 4283885574274767441498677)
                  ·
                    refine ⟨401614272588259447640501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4283885574274767441498677 401614272588259447640501)
                    ·
                      rfl

theorem cell23_2346423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_2346423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346423 prefixEnd_2346423 := by exact prefixLift 2346423
  have htrace : WordTrace (prefixWord ++ tailWord_2346423) baseStart_2346423 baseEnd_2346423 := by
    simpa [prefixWord, tailWord_2346423, baseEnd_2346423] using wordTrace_append hprefix tailTrace_2346423
  have hstable : (prefixWord ++ tailWord_2346423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346423).length < 2 ^ (prefixWord ++ tailWord_2346423).sum := by decide
  have hdescent : baseEnd_2346423 < baseStart_2346423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346430 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_2346430 : Nat := 118140960795 + 2346430 * 2 ^ 59
def prefixEnd_2346430 : Nat := 4983230072969 + 3 ^ 40 * 2346430 * 2
def baseEnd_2346430 : Nat := 1204846412129359815533971

theorem tailTrace_2346430 : CollatzResearch.WordTrace tailWord_2346430 prefixEnd_2346430 1204846412129359815533971 := by
  unfold tailWord_2346430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697666611161540398087593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57054221926194882123133829 10697666611161540398087593)
  ·
    refine ⟨8023249958371155298565695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10697666611161540398087593 8023249958371155298565695)
    ·
      refine ⟨12034874937556732947848543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8023249958371155298565695 12034874937556732947848543)
      ·
        refine ⟨18052312406335099421772815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12034874937556732947848543 18052312406335099421772815)
        ·
          refine ⟨27078468609502649132659223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18052312406335099421772815 27078468609502649132659223)
          ·
            refine ⟨40617702914253973698988835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27078468609502649132659223 40617702914253973698988835)
            ·
              refine ⟨60926554371380960548483253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40617702914253973698988835 60926554371380960548483253)
              ·
                refine ⟨5711864472316965051420305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60926554371380960548483253 5711864472316965051420305)
                ·
                  refine ⟨4283898354237723788565229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5711864472316965051420305 4283898354237723788565229)
                  ·
                    refine ⟨1606461882839146420711961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4283898354237723788565229 1606461882839146420711961)
                    ·
                      refine ⟨1204846412129359815533971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606461882839146420711961 1204846412129359815533971)
                      ·
                        rfl

theorem cell23_2346430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_2346430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346430 prefixEnd_2346430 := by exact prefixLift 2346430
  have htrace : WordTrace (prefixWord ++ tailWord_2346430) baseStart_2346430 baseEnd_2346430 := by
    simpa [prefixWord, tailWord_2346430, baseEnd_2346430] using wordTrace_append hprefix tailTrace_2346430
  have hstable : (prefixWord ++ tailWord_2346430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346430).length < 2 ^ (prefixWord ++ tailWord_2346430).sum := by decide
  have hdescent : baseEnd_2346430 < baseStart_2346430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346443 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 4]
def baseStart_2346443 : Nat := 118140960795 + 2346443 * 2 ^ 59
def prefixEnd_2346443 : Nat := 4983230072969 + 3 ^ 40 * 2346443 * 2
def baseEnd_2346443 : Nat := 1204853087377868264671411

theorem tailTrace_2346443 : CollatzResearch.WordTrace tailWord_2346443 prefixEnd_2346443 1204853087377868264671411 := by
  unfold tailWord_2346443
  simp only [CollatzResearch.WordTrace]
  refine ⟨85581807038245226404923983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57054538025496817603282655 85581807038245226404923983)
  ·
    refine ⟨128372710557367839607385975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85581807038245226404923983 128372710557367839607385975)
    ·
      refine ⟨192559065836051759411078963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128372710557367839607385975 192559065836051759411078963)
      ·
        refine ⟨288838598754077639116618445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192559065836051759411078963 288838598754077639116618445)
        ·
          refine ⟨108314474532779114668731917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288838598754077639116618445 108314474532779114668731917)
          ·
            refine ⟨40617927949792168000774469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108314474532779114668731917 40617927949792168000774469)
            ·
              refine ⟨7615861490586031500145213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40617927949792168000774469 7615861490586031500145213)
              ·
                refine ⟨2855948058969761812554455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7615861490586031500145213 2855948058969761812554455)
                ·
                  refine ⟨4283922088454642718831683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855948058969761812554455 4283922088454642718831683)
                  ·
                    refine ⟨6425883132681964078247525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4283922088454642718831683 6425883132681964078247525)
                    ·
                      refine ⟨1204853087377868264671411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6425883132681964078247525 1204853087377868264671411)
                      ·
                        rfl

theorem cell23_2346443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 4].length) (baseStart_2346443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346443 prefixEnd_2346443 := by exact prefixLift 2346443
  have htrace : WordTrace (prefixWord ++ tailWord_2346443) baseStart_2346443 baseEnd_2346443 := by
    simpa [prefixWord, tailWord_2346443, baseEnd_2346443] using wordTrace_append hprefix tailTrace_2346443
  have hstable : (prefixWord ++ tailWord_2346443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346443).length < 2 ^ (prefixWord ++ tailWord_2346443).sum := by decide
  have hdescent : baseEnd_2346443 < baseStart_2346443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346453 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2346453 : Nat := 118140960795 + 2346453 * 2 ^ 59
def prefixEnd_2346453 : Nat := 4983230072969 + 3 ^ 40 * 2346453 * 2
def baseEnd_2346453 : Nat := 401619407394804408515455

theorem tailTrace_2346453 : CollatzResearch.WordTrace tailWord_2346453 prefixEnd_2346453 401619407394804408515455 := by
  unfold tailWord_2346453
  simp only [CollatzResearch.WordTrace]
  refine ⟨85582171768208998112788013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57054781178805998741858675 85582171768208998112788013)
  ·
    refine ⟨32093314413078374292295505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85582171768208998112788013 32093314413078374292295505)
    ·
      refine ⟨24069985809808780719221629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32093314413078374292295505 24069985809808780719221629)
      ·
        refine ⟨9026244678678292769708111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24069985809808780719221629 9026244678678292769708111)
        ·
          refine ⟨13539367018017439154562167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9026244678678292769708111 13539367018017439154562167)
          ·
            refine ⟨20309050527026158731843251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13539367018017439154562167 20309050527026158731843251)
            ·
              refine ⟨30463575790539238097764877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20309050527026158731843251 30463575790539238097764877)
              ·
                refine ⟨11423840921452214286661829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30463575790539238097764877 11423840921452214286661829)
                ·
                  refine ⟨2141970172772290178749093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11423840921452214286661829 2141970172772290178749093)
                  ·
                    refine ⟨401619407394804408515455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2141970172772290178749093 401619407394804408515455)
                    ·
                      rfl

theorem cell23_2346453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2346453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346453 prefixEnd_2346453 := by exact prefixLift 2346453
  have htrace : WordTrace (prefixWord ++ tailWord_2346453) baseStart_2346453 baseEnd_2346453 := by
    simpa [prefixWord, tailWord_2346453, baseEnd_2346453] using wordTrace_append hprefix tailTrace_2346453
  have hstable : (prefixWord ++ tailWord_2346453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346453).length < 2 ^ (prefixWord ++ tailWord_2346453).sum := by decide
  have hdescent : baseEnd_2346453 < baseStart_2346453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346454 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2346454 : Nat := 118140960795 + 2346454 * 2 ^ 59
def prefixEnd_2346454 : Nat := 4983230072969 + 3 ^ 40 * 2346454 * 2
def baseEnd_2346454 : Nat := 1204858735665067721633861

theorem tailTrace_2346454 : CollatzResearch.WordTrace tailWord_2346454 prefixEnd_2346454 1204858735665067721633861 := by
  unfold tailWord_2346454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348888015075335955223401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57054805494136916855716277 5348888015075335955223401)
  ·
    refine ⟨4011666011306501966417551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5348888015075335955223401 4011666011306501966417551)
    ·
      refine ⟨6017499016959752949626327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4011666011306501966417551 6017499016959752949626327)
      ·
        refine ⟨9026248525439629424439491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6017499016959752949626327 9026248525439629424439491)
        ·
          refine ⟨13539372788159444136659237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9026248525439629424439491 13539372788159444136659237)
          ·
            refine ⟨2538632397779895775623607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13539372788159444136659237 2538632397779895775623607)
            ·
              refine ⟨3807948596669843663435411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538632397779895775623607 3807948596669843663435411)
              ·
                refine ⟨5711922895004765495153117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3807948596669843663435411 5711922895004765495153117)
                ·
                  refine ⟨2141971085626787060682419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5711922895004765495153117 2141971085626787060682419)
                  ·
                    refine ⟨3212956628440180591023629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2141971085626787060682419 3212956628440180591023629)
                    ·
                      refine ⟨1204858735665067721633861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3212956628440180591023629 1204858735665067721633861)
                      ·
                        rfl

theorem cell23_2346454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2346454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346454 prefixEnd_2346454 := by exact prefixLift 2346454
  have htrace : WordTrace (prefixWord ++ tailWord_2346454) baseStart_2346454 baseEnd_2346454 := by
    simpa [prefixWord, tailWord_2346454, baseEnd_2346454] using wordTrace_append hprefix tailTrace_2346454
  have hstable : (prefixWord ++ tailWord_2346454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346454).length < 2 ^ (prefixWord ++ tailWord_2346454).sum := by decide
  have hdescent : baseEnd_2346454 < baseStart_2346454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346456 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2346456 : Nat := 118140960795 + 2346456 * 2 ^ 59
def prefixEnd_2346456 : Nat := 4983230072969 + 3 ^ 40 * 2346456 * 2
def baseEnd_2346456 : Nat := 1204859762626376713808851

theorem tailTrace_2346456 : CollatzResearch.WordTrace tailWord_2346456 prefixEnd_2346456 1204859762626376713808851 := by
  unfold tailWord_2346456
  simp only [CollatzResearch.WordTrace]
  refine ⟨42791140593599064812573611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57054854124798753083431481 42791140593599064812573611)
  ·
    refine ⟨64186710890398597218860417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42791140593599064812573611 64186710890398597218860417)
    ·
      refine ⟨48140033167798947914145313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64186710890398597218860417 48140033167798947914145313)
      ·
        refine ⟨36105024875849210935608985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48140033167798947914145313 36105024875849210935608985)
        ·
          refine ⟨27078768656886908201706739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36105024875849210935608985 27078768656886908201706739)
          ·
            refine ⟨40618152985330362302560109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27078768656886908201706739 40618152985330362302560109)
            ·
              refine ⟨15231807369498885863460041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40618152985330362302560109 15231807369498885863460041)
              ·
                refine ⟨11423855527124164397595031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15231807369498885863460041 11423855527124164397595031)
                ·
                  refine ⟨17135783290686246596392547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11423855527124164397595031 17135783290686246596392547)
                  ·
                    refine ⟨25703674936029369894588821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17135783290686246596392547 25703674936029369894588821)
                    ·
                      refine ⟨1204859762626376713808851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25703674936029369894588821 1204859762626376713808851)
                      ·
                        rfl

theorem cell23_2346456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2346456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346456 prefixEnd_2346456 := by exact prefixLift 2346456
  have htrace : WordTrace (prefixWord ++ tailWord_2346456) baseStart_2346456 baseEnd_2346456 := by
    simpa [prefixWord, tailWord_2346456, baseEnd_2346456] using wordTrace_append hprefix tailTrace_2346456
  have hstable : (prefixWord ++ tailWord_2346456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346456).length < 2 ^ (prefixWord ++ tailWord_2346456).sum := by decide
  have hdescent : baseEnd_2346456 < baseStart_2346456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346463 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 3]
def baseStart_2346463 : Nat := 118140960795 + 2346463 * 2 ^ 59
def prefixEnd_2346463 : Nat := 4983230072969 + 3 ^ 40 * 2346463 * 2
def baseEnd_2346463 : Nat := 1204863356990958186421319

theorem tailTrace_2346463 : CollatzResearch.WordTrace tailWord_2346463 prefixEnd_2346463 1204863356990958186421319 := by
  unfold tailWord_2346463
  simp only [CollatzResearch.WordTrace]
  refine ⟨85582536498172769820652043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57055024332115179880434695 85582536498172769820652043)
  ·
    refine ⟨128373804747259154730978065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85582536498172769820652043 128373804747259154730978065)
    ·
      refine ⟨96280353560444366048233549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128373804747259154730978065 96280353560444366048233549)
      ·
        refine ⟨36105132585166637268087581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96280353560444366048233549 36105132585166637268087581)
        ·
          refine ⟨13539424719437488975532843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36105132585166637268087581 13539424719437488975532843)
          ·
            refine ⟨20309137079156233463299265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13539424719437488975532843 20309137079156233463299265)
            ·
              refine ⟨15231852809367175097474449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20309137079156233463299265 15231852809367175097474449)
              ·
                refine ⟨11423889607025381323105837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15231852809367175097474449 11423889607025381323105837)
                ·
                  refine ⟨4283958602634517996164689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11423889607025381323105837 4283958602634517996164689)
                  ·
                    refine ⟨3212968951975888497123517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283958602634517996164689 3212968951975888497123517)
                    ·
                      refine ⟨1204863356990958186421319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3212968951975888497123517 1204863356990958186421319)
                      ·
                        rfl

theorem cell23_2346463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_2346463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346463 prefixEnd_2346463 := by exact prefixLift 2346463
  have htrace : WordTrace (prefixWord ++ tailWord_2346463) baseStart_2346463 baseEnd_2346463 := by
    simpa [prefixWord, tailWord_2346463, baseEnd_2346463] using wordTrace_append hprefix tailTrace_2346463
  have hstable : (prefixWord ++ tailWord_2346463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346463).length < 2 ^ (prefixWord ++ tailWord_2346463).sum := by decide
  have hdescent : baseEnd_2346463 < baseStart_2346463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346480 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 3]
def baseStart_2346480 : Nat := 118140960795 + 2346480 * 2 ^ 59
def prefixEnd_2346480 : Nat := 4983230072969 + 3 ^ 40 * 2346480 * 2
def baseEnd_2346480 : Nat := 1204872086162084619908741

theorem tailTrace_2346480 : CollatzResearch.WordTrace tailWord_2346480 prefixEnd_2346480 1204872086162084619908741 := by
  unfold tailWord_2346480
  simp only [CollatzResearch.WordTrace]
  refine ⟨42791578269555590862010447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57055437692740787816013929 42791578269555590862010447)
  ·
    refine ⟨64187367404333386293015671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42791578269555590862010447 64187367404333386293015671)
    ·
      refine ⟨96281051106500079439523507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64187367404333386293015671 96281051106500079439523507)
      ·
        refine ⟨144421576659750119159285261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96281051106500079439523507 144421576659750119159285261)
        ·
          refine ⟨54158091247406294684731973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144421576659750119159285261 54158091247406294684731973)
          ·
            refine ⟨10154642108888680253387245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54158091247406294684731973 10154642108888680253387245)
            ·
              refine ⟨3807990790833255095020217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10154642108888680253387245 3807990790833255095020217)
              ·
                refine ⟨2855993093124941321265163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3807990790833255095020217 2855993093124941321265163)
                ·
                  refine ⟨4283989639687411981897745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855993093124941321265163 4283989639687411981897745)
                  ·
                    refine ⟨3212992229765558986423309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283989639687411981897745 3212992229765558986423309)
                    ·
                      refine ⟨1204872086162084619908741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3212992229765558986423309 1204872086162084619908741)
                      ·
                        rfl

theorem cell23_2346480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 3].length) (baseStart_2346480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346480 prefixEnd_2346480 := by exact prefixLift 2346480
  have htrace : WordTrace (prefixWord ++ tailWord_2346480) baseStart_2346480 baseEnd_2346480 := by
    simpa [prefixWord, tailWord_2346480, baseEnd_2346480] using wordTrace_append hprefix tailTrace_2346480
  have hstable : (prefixWord ++ tailWord_2346480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346480).length < 2 ^ (prefixWord ++ tailWord_2346480).sum := by decide
  have hdescent : baseEnd_2346480 < baseStart_2346480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346493 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_2346493 : Nat := 118140960795 + 2346493 * 2 ^ 59
def prefixEnd_2346493 : Nat := 4983230072969 + 3 ^ 40 * 2346493 * 2
def baseEnd_2346493 : Nat := 1204878761410593069046181

theorem tailTrace_2346493 : CollatzResearch.WordTrace tailWord_2346493 prefixEnd_2346493 1204878761410593069046181 := by
  unfold tailWord_2346493
  simp only [CollatzResearch.WordTrace]
  refine ⟨85583630688064084944244133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57055753792042723296162755 85583630688064084944244133)
  ·
    refine ⟨16046930754012015927045775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85583630688064084944244133 16046930754012015927045775)
    ·
      refine ⟨24070396131018023890568663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16046930754012015927045775 24070396131018023890568663)
      ·
        refine ⟨36105594196527035835852995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24070396131018023890568663 36105594196527035835852995)
        ·
          refine ⟨54158391294790553753779493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36105594196527035835852995 54158391294790553753779493)
          ·
            refine ⟨10154698367773228828833655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54158391294790553753779493 10154698367773228828833655)
            ·
              refine ⟨15232047551659843243250483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10154698367773228828833655 15232047551659843243250483)
              ·
                refine ⟨22848071327489764864875725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15232047551659843243250483 22848071327489764864875725)
                ·
                  refine ⟨8568026747808661824328397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22848071327489764864875725 8568026747808661824328397)
                  ·
                    refine ⟨3213010030428248184123149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8568026747808661824328397 3213010030428248184123149)
                    ·
                      refine ⟨1204878761410593069046181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3213010030428248184123149 1204878761410593069046181)
                      ·
                        rfl

theorem cell23_2346493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_2346493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346493 prefixEnd_2346493 := by exact prefixLift 2346493
  have htrace : WordTrace (prefixWord ++ tailWord_2346493) baseStart_2346493 baseEnd_2346493 := by
    simpa [prefixWord, tailWord_2346493, baseEnd_2346493] using wordTrace_append hprefix tailTrace_2346493
  have hstable : (prefixWord ++ tailWord_2346493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346493).length < 2 ^ (prefixWord ++ tailWord_2346493).sum := by decide
  have hdescent : baseEnd_2346493 < baseStart_2346493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346497 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_2346497 : Nat := 118140960795 + 2346497 * 2 ^ 59
def prefixEnd_2346497 : Nat := 4983230072969 + 3 ^ 40 * 2346497 * 2
def baseEnd_2346497 : Nat := 1204880815333211053396163

theorem tailTrace_2346497 : CollatzResearch.WordTrace tailWord_2346497 prefixEnd_2346497 1204880815333211053396163 := by
  unfold tailWord_2346497
  simp only [CollatzResearch.WordTrace]
  refine ⟨85583776580049593627389745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57055851053366395751593163 85583776580049593627389745)
  ·
    refine ⟨64187832435037195220542309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85583776580049593627389745 64187832435037195220542309)
    ·
      refine ⟨12035218581569474103851683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64187832435037195220542309 12035218581569474103851683)
      ·
        refine ⟨18052827872354211155777525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12035218581569474103851683 18052827872354211155777525)
        ·
          refine ⟨1692452613033207295854143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18052827872354211155777525 1692452613033207295854143)
          ·
            refine ⟨2538678919549810943781215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692452613033207295854143 2538678919549810943781215)
            ·
              refine ⟨3808018379324716415671823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538678919549810943781215 3808018379324716415671823)
              ·
                refine ⟨5712027568987074623507735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808018379324716415671823 5712027568987074623507735)
                ·
                  refine ⟨8568041353480611935261603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5712027568987074623507735 8568041353480611935261603)
                  ·
                    refine ⟨12852062030220917902892405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8568041353480611935261603 12852062030220917902892405)
                    ·
                      refine ⟨1204880815333211053396163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12852062030220917902892405 1204880815333211053396163)
                      ·
                        rfl

theorem cell23_2346497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_2346497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346497 prefixEnd_2346497 := by exact prefixLift 2346497
  have htrace : WordTrace (prefixWord ++ tailWord_2346497) baseStart_2346497 baseEnd_2346497 := by
    simpa [prefixWord, tailWord_2346497, baseEnd_2346497] using wordTrace_append hprefix tailTrace_2346497
  have hstable : (prefixWord ++ tailWord_2346497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346497).length < 2 ^ (prefixWord ++ tailWord_2346497).sum := by decide
  have hdescent : baseEnd_2346497 < baseStart_2346497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346640 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 2, 4, 2]
def baseStart_2346640 : Nat := 118140960795 + 2346640 * 2 ^ 59
def prefixEnd_2346640 : Nat := 4983230072969 + 3 ^ 40 * 2346640 * 2
def baseEnd_2346640 : Nat := 1204954243066803993908005

theorem tailTrace_2346640 : CollatzResearch.WordTrace tailWord_2346640 prefixEnd_2346640 1204954243066803993908005 := by
  unfold tailWord_2346640
  simp only [CollatzResearch.WordTrace]
  refine ⟨42794496109265764524922687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57059328145687686033230249 42794496109265764524922687)
  ·
    refine ⟨64191744163898646787384031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42794496109265764524922687 64191744163898646787384031)
    ·
      refine ⟨96287616245847970181076047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64191744163898646787384031 96287616245847970181076047)
      ·
        refine ⟨144431424368771955271614071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96287616245847970181076047 144431424368771955271614071)
        ·
          refine ⟨216647136553157932907421107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144431424368771955271614071 216647136553157932907421107)
          ·
            refine ⟨324970704829736899361131661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216647136553157932907421107 324970704829736899361131661)
            ·
              refine ⟨121864014311151337260424373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324970704829736899361131661 121864014311151337260424373)
              ·
                refine ⟨11424751341670437868164785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121864014311151337260424373 11424751341670437868164785)
                ·
                  refine ⟨8568563506252828401123589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11424751341670437868164785 8568563506252828401123589)
                  ·
                    refine ⟨1606605657422405325210673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8568563506252828401123589 1606605657422405325210673)
                    ·
                      refine ⟨1204954243066803993908005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606605657422405325210673 1204954243066803993908005)
                      ·
                        rfl

theorem cell23_2346640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 4, 2].length) (baseStart_2346640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346640 prefixEnd_2346640 := by exact prefixLift 2346640
  have htrace : WordTrace (prefixWord ++ tailWord_2346640) baseStart_2346640 baseEnd_2346640 := by
    simpa [prefixWord, tailWord_2346640, baseEnd_2346640] using wordTrace_append hprefix tailTrace_2346640
  have hstable : (prefixWord ++ tailWord_2346640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346640).length < 2 ^ (prefixWord ++ tailWord_2346640).sum := by decide
  have hdescent : baseEnd_2346640 < baseStart_2346640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346653 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2346653 : Nat := 118140960795 + 2346653 * 2 ^ 59
def prefixEnd_2346653 : Nat := 4983230072969 + 3 ^ 40 * 2346653 * 2
def baseEnd_2346653 : Nat := 1204960918315312443045445

theorem tailTrace_2346653 : CollatzResearch.WordTrace tailWord_2346653 prefixEnd_2346653 1204960918315312443045445 := by
  unfold tailWord_2346653
  simp only [CollatzResearch.WordTrace]
  refine ⟨85589466367484432270068613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57059644244989621513379075 85589466367484432270068613)
  ·
    refine ⟨16048024943903331050637865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85589466367484432270068613 16048024943903331050637865)
    ·
      refine ⟨12036018707927498287978399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16048024943903331050637865 12036018707927498287978399)
      ·
        refine ⟨18054028061891247431967599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12036018707927498287978399 18054028061891247431967599)
        ·
          refine ⟨27081042092836871147951399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18054028061891247431967599 27081042092836871147951399)
          ·
            refine ⟨40621563139255306721927099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27081042092836871147951399 40621563139255306721927099)
            ·
              refine ⟨60932344708882960082890649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40621563139255306721927099 60932344708882960082890649)
              ·
                refine ⟨45699258531662220062167987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60932344708882960082890649 45699258531662220062167987)
                ·
                  refine ⟨68548887797493330093251981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45699258531662220062167987 68548887797493330093251981)
                  ·
                    refine ⟨25705832924059998784969493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68548887797493330093251981 25705832924059998784969493)
                    ·
                      refine ⟨1204960918315312443045445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25705832924059998784969493 1204960918315312443045445)
                      ·
                        rfl

theorem cell23_2346653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2346653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346653 prefixEnd_2346653 := by exact prefixLift 2346653
  have htrace : WordTrace (prefixWord ++ tailWord_2346653) baseStart_2346653 baseEnd_2346653 := by
    simpa [prefixWord, tailWord_2346653, baseEnd_2346653] using wordTrace_append hprefix tailTrace_2346653
  have hstable : (prefixWord ++ tailWord_2346653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346653).length < 2 ^ (prefixWord ++ tailWord_2346653).sum := by decide
  have hdescent : baseEnd_2346653 < baseStart_2346653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346657 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2346657 : Nat := 118140960795 + 2346657 * 2 ^ 59
def prefixEnd_2346657 : Nat := 4983230072969 + 3 ^ 40 * 2346657 * 2
def baseEnd_2346657 : Nat := 1204962972237930427395427

theorem tailTrace_2346657 : CollatzResearch.WordTrace tailWord_2346657 prefixEnd_2346657 1204962972237930427395427 := by
  unfold tailWord_2346657
  simp only [CollatzResearch.WordTrace]
  refine ⟨85589612259469940953214225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57059741506313293968809483 85589612259469940953214225)
  ·
    refine ⟨64192209194602455714910669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85589612259469940953214225 64192209194602455714910669)
    ·
      refine ⟨24072078447975920893091501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64192209194602455714910669 24072078447975920893091501)
      ·
        refine ⟨9027029417990970334909313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24072078447975920893091501 9027029417990970334909313)
        ·
          refine ⟨6770272063493227751181985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9027029417990970334909313 6770272063493227751181985)
          ·
            refine ⟨5077704047619920813386489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6770272063493227751181985 5077704047619920813386489)
            ·
              refine ⟨3808278035714940610039867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5077704047619920813386489 3808278035714940610039867)
              ·
                refine ⟨5712417053572410915059801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808278035714940610039867 5712417053572410915059801)
                ·
                  refine ⟨4284312790179308186294851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5712417053572410915059801 4284312790179308186294851)
                  ·
                    refine ⟨6426469185268962279442277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4284312790179308186294851 6426469185268962279442277)
                    ·
                      refine ⟨1204962972237930427395427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6426469185268962279442277 1204962972237930427395427)
                      ·
                        rfl

theorem cell23_2346657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2346657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346657 prefixEnd_2346657 := by exact prefixLift 2346657
  have htrace : WordTrace (prefixWord ++ tailWord_2346657) baseStart_2346657 baseEnd_2346657 := by
    simpa [prefixWord, tailWord_2346657, baseEnd_2346657] using wordTrace_append hprefix tailTrace_2346657
  have hstable : (prefixWord ++ tailWord_2346657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346657).length < 2 ^ (prefixWord ++ tailWord_2346657).sum := by decide
  have hdescent : baseEnd_2346657 < baseStart_2346657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346684 : List Nat := [2, 2, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_2346684 : Nat := 118140960795 + 2346684 * 2 ^ 59
def prefixEnd_2346684 : Nat := 4983230072969 + 3 ^ 40 * 2346684 * 2
def baseEnd_2346684 : Nat := 401658945405200607252601

theorem tailTrace_2346684 : CollatzResearch.WordTrace tailWord_2346684 prefixEnd_2346684 401658945405200607252601 := by
  unfold tailWord_2346684
  simp only [CollatzResearch.WordTrace]
  refine ⟨42795298515186062282223553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57060398020248083042964737 42795298515186062282223553)
  ·
    refine ⟨32096473886389546711667665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42795298515186062282223553 32096473886389546711667665)
    ·
      refine ⟨24072355414792160033750749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32096473886389546711667665 24072355414792160033750749)
      ·
        refine ⟨9027133280547060012656531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24072355414792160033750749 9027133280547060012656531)
        ·
          refine ⟨13540699920820590018984797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9027133280547060012656531 13540699920820590018984797)
          ·
            refine ⟨5077762470307721257119299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13540699920820590018984797 5077762470307721257119299)
            ·
              refine ⟨7616643705461581885678949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077762470307721257119299 7616643705461581885678949)
              ·
                refine ⟨1428120694774046603564803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7616643705461581885678949 1428120694774046603564803)
                ·
                  refine ⟨2142181042161069905347205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428120694774046603564803 2142181042161069905347205)
                  ·
                    refine ⟨401658945405200607252601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142181042161069905347205 401658945405200607252601)
                    ·
                      rfl

theorem cell23_2346684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_2346684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346684 prefixEnd_2346684 := by exact prefixLift 2346684
  have htrace : WordTrace (prefixWord ++ tailWord_2346684) baseStart_2346684 baseEnd_2346684 := by
    simpa [prefixWord, tailWord_2346684, baseEnd_2346684] using wordTrace_append hprefix tailTrace_2346684
  have hstable : (prefixWord ++ tailWord_2346684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346684).length < 2 ^ (prefixWord ++ tailWord_2346684).sum := by decide
  have hdescent : baseEnd_2346684 < baseStart_2346684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346760 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2346760 : Nat := 118140960795 + 2346760 * 2 ^ 59
def prefixEnd_2346760 : Nat := 4983230072969 + 3 ^ 40 * 2346760 * 2
def baseEnd_2346760 : Nat := 1205015860745343524407453

theorem tailTrace_2346760 : CollatzResearch.WordTrace tailWord_2346760 prefixEnd_2346760 1205015860745343524407453 := by
  unfold tailWord_2346760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42796684489048394772106867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57062245985397859696142489 42796684489048394772106867)
  ·
    refine ⟨64195026733572592158160301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42796684489048394772106867 64195026733572592158160301)
    ·
      refine ⟨24073135025089722059310113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64195026733572592158160301 24073135025089722059310113)
      ·
        refine ⟨18054851268817291544482585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24073135025089722059310113 18054851268817291544482585)
        ·
          refine ⟨13541138451612968658361939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18054851268817291544482585 13541138451612968658361939)
          ·
            refine ⟨20311707677419452987542909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13541138451612968658361939 20311707677419452987542909)
            ·
              refine ⟨7616890379032294870328591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20311707677419452987542909 7616890379032294870328591)
              ·
                refine ⟨11425335568548442305492887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7616890379032294870328591 11425335568548442305492887)
                ·
                  refine ⟨17138003352822663458239331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11425335568548442305492887 17138003352822663458239331)
                  ·
                    refine ⟨25707005029233995187358997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17138003352822663458239331 25707005029233995187358997)
                    ·
                      refine ⟨1205015860745343524407453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25707005029233995187358997 1205015860745343524407453)
                      ·
                        rfl

theorem cell23_2346760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2346760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346760 prefixEnd_2346760 := by exact prefixLift 2346760
  have htrace : WordTrace (prefixWord ++ tailWord_2346760) baseStart_2346760 baseEnd_2346760 := by
    simpa [prefixWord, tailWord_2346760, baseEnd_2346760] using wordTrace_append hprefix tailTrace_2346760
  have hstable : (prefixWord ++ tailWord_2346760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346760).length < 2 ^ (prefixWord ++ tailWord_2346760).sum := by decide
  have hdescent : baseEnd_2346760 < baseStart_2346760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346764 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 3, 2, 2]
def baseStart_2346764 : Nat := 118140960795 + 2346764 * 2 ^ 59
def prefixEnd_2346764 : Nat := 4983230072969 + 3 ^ 40 * 2346764 * 2
def baseEnd_2346764 : Nat := 1205017914667961508757435

theorem tailTrace_2346764 : CollatzResearch.WordTrace tailWord_2346764 prefixEnd_2346764 1205017914667961508757435 := by
  unfold tailWord_2346764
  simp only [CollatzResearch.WordTrace]
  refine ⟨42796757435041149113679673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57062343246721532151572897 42796757435041149113679673)
  ·
    refine ⟨32097568076280861835259755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42796757435041149113679673 32097568076280861835259755)
    ·
      refine ⟨48146352114421292752889633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32097568076280861835259755 48146352114421292752889633)
      ·
        refine ⟨36109764085815969564667225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48146352114421292752889633 36109764085815969564667225)
        ·
          refine ⟨27082323064361977173500419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36109764085815969564667225 27082323064361977173500419)
          ·
            refine ⟨40623484596542965760250629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27082323064361977173500419 40623484596542965760250629)
            ·
              refine ⟨7616903361851806080046993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40623484596542965760250629 7616903361851806080046993)
              ·
                refine ⟨5712677521388854560035245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7616903361851806080046993 5712677521388854560035245)
                ·
                  refine ⟨2142254070520820460013217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5712677521388854560035245 2142254070520820460013217)
                  ·
                    refine ⟨1606690552890615345009913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2142254070520820460013217 1606690552890615345009913)
                    ·
                      refine ⟨1205017914667961508757435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606690552890615345009913 1205017914667961508757435)
                      ·
                        rfl

theorem cell23_2346764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_2346764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346764 prefixEnd_2346764 := by exact prefixLift 2346764
  have htrace : WordTrace (prefixWord ++ tailWord_2346764) baseStart_2346764 baseEnd_2346764 := by
    simpa [prefixWord, tailWord_2346764, baseEnd_2346764] using wordTrace_append hprefix tailTrace_2346764
  have hstable : (prefixWord ++ tailWord_2346764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346764).length < 2 ^ (prefixWord ++ tailWord_2346764).sum := by decide
  have hdescent : baseEnd_2346764 < baseStart_2346764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346824 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_2346824 : Nat := 118140960795 + 2346824 * 2 ^ 59
def prefixEnd_2346824 : Nat := 4983230072969 + 3 ^ 40 * 2346824 * 2
def baseEnd_2346824 : Nat := 1205048723507231274007159

theorem tailTrace_2346824 : CollatzResearch.WordTrace tailWord_2346824 prefixEnd_2346824 1205048723507231274007159 := by
  unfold tailWord_2346824
  simp only [CollatzResearch.WordTrace]
  refine ⟨42797851624932464237271763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57063802166576618983029017 42797851624932464237271763)
  ·
    refine ⟨64196777437398696355907645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42797851624932464237271763 64196777437398696355907645)
    ·
      refine ⟨24073791539024511133465367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64196777437398696355907645 24073791539024511133465367)
      ·
        refine ⟨36110687308536766700198051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24073791539024511133465367 36110687308536766700198051)
        ·
          refine ⟨54166030962805150050297077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36110687308536766700198051 54166030962805150050297077)
          ·
            refine ⟨5078065402762982817215351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54166030962805150050297077 5078065402762982817215351)
            ·
              refine ⟨7617098104144474225823027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078065402762982817215351 7617098104144474225823027)
              ·
                refine ⟨11425647156216711338734541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7617098104144474225823027 11425647156216711338734541)
                ·
                  refine ⟨4284617683581266752025453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11425647156216711338734541 4284617683581266752025453)
                  ·
                    refine ⟨1606731631342975032009545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4284617683581266752025453 1606731631342975032009545)
                    ·
                      refine ⟨1205048723507231274007159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606731631342975032009545 1205048723507231274007159)
                      ·
                        rfl

theorem cell23_2346824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_2346824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346824 prefixEnd_2346824 := by exact prefixLift 2346824
  have htrace : WordTrace (prefixWord ++ tailWord_2346824) baseStart_2346824 baseEnd_2346824 := by
    simpa [prefixWord, tailWord_2346824, baseEnd_2346824] using wordTrace_append hprefix tailTrace_2346824
  have hstable : (prefixWord ++ tailWord_2346824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346824).length < 2 ^ (prefixWord ++ tailWord_2346824).sum := by decide
  have hdescent : baseEnd_2346824 < baseStart_2346824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346830 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2346830 : Nat := 118140960795 + 2346830 * 2 ^ 59
def prefixEnd_2346830 : Nat := 4983230072969 + 3 ^ 40 * 2346830 * 2
def baseEnd_2346830 : Nat := 401683934797052750177377

theorem tailTrace_2346830 : CollatzResearch.WordTrace tailWord_2346830 prefixEnd_2346830 401683934797052750177377 := by
  unfold tailWord_2346830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10699490260980398937407743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57063948058562127666174629 10699490260980398937407743)
  ·
    refine ⟨16049235391470598406111615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10699490260980398937407743 16049235391470598406111615)
    ·
      refine ⟨24073853087205897609167423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16049235391470598406111615 24073853087205897609167423)
      ·
        refine ⟨36110779630808846413751135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24073853087205897609167423 36110779630808846413751135)
        ·
          refine ⟨54166169446213269620626703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36110779630808846413751135 54166169446213269620626703)
          ·
            refine ⟨81249254169319904430940055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54166169446213269620626703 81249254169319904430940055)
            ·
              refine ⟨121873881253979856646410083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81249254169319904430940055 121873881253979856646410083)
              ·
                refine ⟨182810821880969784969615125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121873881253979856646410083 182810821880969784969615125)
                ·
                  refine ⟨8569257275670458670450709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 182810821880969784969615125 8569257275670458670450709)
                  ·
                    refine ⟨401683934797052750177377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8569257275670458670450709 401683934797052750177377)
                    ·
                      rfl

theorem cell23_2346830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2346830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346830 prefixEnd_2346830 := by exact prefixLift 2346830
  have htrace : WordTrace (prefixWord ++ tailWord_2346830) baseStart_2346830 baseEnd_2346830 := by
    simpa [prefixWord, tailWord_2346830, baseEnd_2346830] using wordTrace_append hprefix tailTrace_2346830
  have hstable : (prefixWord ++ tailWord_2346830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346830).length < 2 ^ (prefixWord ++ tailWord_2346830).sum := by decide
  have hdescent : baseEnd_2346830 < baseStart_2346830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346841 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 1, 3, 2]
def baseStart_2346841 : Nat := 118140960795 + 2346841 * 2 ^ 59
def prefixEnd_2346841 : Nat := 4983230072969 + 3 ^ 40 * 2346841 * 2
def baseEnd_2346841 : Nat := 1205057452678357707494581

theorem tailTrace_2346841 : CollatzResearch.WordTrace tailWord_2346841 prefixEnd_2346841 1205057452678357707494581 := by
  unfold tailWord_2346841
  simp only [CollatzResearch.WordTrace]
  refine ⟨85596323290803340377912377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57064215527202226918608251 85596323290803340377912377)
  ·
    refine ⟨64197242468102505283434283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85596323290803340377912377 64197242468102505283434283)
    ·
      refine ⟨96295863702153757925151425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64197242468102505283434283 96295863702153757925151425)
      ·
        refine ⟨72221897776615318443863569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96295863702153757925151425 72221897776615318443863569)
        ·
          refine ⟨54166423332461488832897677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72221897776615318443863569 54166423332461488832897677)
          ·
            refine ⟨20312408749673058312336629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54166423332461488832897677 20312408749673058312336629)
            ·
              refine ⟨1904288320281849216781559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20312408749673058312336629 1904288320281849216781559)
              ·
                refine ⟨2856432480422773825172339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904288320281849216781559 2856432480422773825172339)
                ·
                  refine ⟨4284648720634160737758509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856432480422773825172339 4284648720634160737758509)
                  ·
                    refine ⟨1606743270237810276659441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4284648720634160737758509 1606743270237810276659441)
                    ·
                      refine ⟨1205057452678357707494581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606743270237810276659441 1205057452678357707494581)
                      ·
                        rfl

theorem cell23_2346841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_2346841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346841 prefixEnd_2346841 := by exact prefixLift 2346841
  have htrace : WordTrace (prefixWord ++ tailWord_2346841) baseStart_2346841 baseEnd_2346841 := by
    simpa [prefixWord, tailWord_2346841, baseEnd_2346841] using wordTrace_append hprefix tailTrace_2346841
  have hstable : (prefixWord ++ tailWord_2346841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346841).length < 2 ^ (prefixWord ++ tailWord_2346841).sum := by decide
  have hdescent : baseEnd_2346841 < baseStart_2346841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346967 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 6]
def baseStart_2346967 : Nat := 118140960795 + 2346967 * 2 ^ 59
def prefixEnd_2346967 : Nat := 4983230072969 + 3 ^ 40 * 2346967 * 2
def baseEnd_2346967 : Nat := 133902461248980468279889

theorem tailTrace_2346967 : CollatzResearch.WordTrace tailWord_2346967 prefixEnd_2346967 133902461248980468279889 := by
  unfold tailWord_2346967
  simp only [CollatzResearch.WordTrace]
  refine ⟨85600918888346863896999155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57067279258897909264666103 85600918888346863896999155)
  ·
    refine ⟨128401378332520295845498733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85600918888346863896999155 128401378332520295845498733)
    ·
      refine ⟨48150516874695110942062025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128401378332520295845498733 48150516874695110942062025)
      ·
        refine ⟨36112887656021333206546519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48150516874695110942062025 36112887656021333206546519)
        ·
          refine ⟨54169331484031999809819779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36112887656021333206546519 54169331484031999809819779)
          ·
            refine ⟨81253997226047999714729669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54169331484031999809819779 81253997226047999714729669)
            ·
              refine ⟨15235124479883999946511813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81253997226047999714729669 15235124479883999946511813)
              ·
                refine ⟨2856585839978249989970965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15235124479883999946511813 2856585839978249989970965)
                ·
                  refine ⟨133902461248980468279889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2856585839978249989970965 133902461248980468279889)
                  ·
                    rfl

theorem cell23_2346967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 6].length) (baseStart_2346967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346967 prefixEnd_2346967 := by exact prefixLift 2346967
  have htrace : WordTrace (prefixWord ++ tailWord_2346967) baseStart_2346967 baseEnd_2346967 := by
    simpa [prefixWord, tailWord_2346967, baseEnd_2346967] using wordTrace_append hprefix tailTrace_2346967
  have hstable : (prefixWord ++ tailWord_2346967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346967).length < 2 ^ (prefixWord ++ tailWord_2346967).sum := by decide
  have hdescent : baseEnd_2346967 < baseStart_2346967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346998 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2346998 : Nat := 118140960795 + 2346998 * 2 ^ 59
def prefixEnd_2346998 : Nat := 4983230072969 + 3 ^ 40 * 2346998 * 2
def baseEnd_2346998 : Nat := 1205138069141113593231359

theorem tailTrace_2346998 : CollatzResearch.WordTrace tailWord_2346998 prefixEnd_2346998 1205138069141113593231359 := by
  unfold tailWord_2346998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350128096952159761961103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57068033034156370794251765 5350128096952159761961103)
  ·
    refine ⟨8025192145428239642941655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5350128096952159761961103 8025192145428239642941655)
    ·
      refine ⟨12037788218142359464412483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8025192145428239642941655 12037788218142359464412483)
      ·
        refine ⟨18056682327213539196618725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12037788218142359464412483 18056682327213539196618725)
        ·
          refine ⟨3385627936352538599366011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18056682327213539196618725 3385627936352538599366011)
          ·
            refine ⟨5078441904528807899049017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385627936352538599366011 5078441904528807899049017)
            ·
              refine ⟨3808831428396605924286763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5078441904528807899049017 3808831428396605924286763)
              ·
                refine ⟨5713247142594908886430145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808831428396605924286763 5713247142594908886430145)
                ·
                  refine ⟨4284935356946181664822609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5713247142594908886430145 4284935356946181664822609)
                  ·
                    refine ⟨3213701517709636248616957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4284935356946181664822609 3213701517709636248616957)
                    ·
                      refine ⟨1205138069141113593231359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3213701517709636248616957 1205138069141113593231359)
                      ·
                        rfl

theorem cell23_2346998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2346998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2346998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2346998 prefixEnd_2346998 := by exact prefixLift 2346998
  have htrace : WordTrace (prefixWord ++ tailWord_2346998) baseStart_2346998 baseEnd_2346998 := by
    simpa [prefixWord, tailWord_2346998, baseEnd_2346998] using wordTrace_append hprefix tailTrace_2346998
  have hstable : (prefixWord ++ tailWord_2346998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346998).length < 2 ^ (prefixWord ++ tailWord_2346998).sum := by decide
  have hdescent : baseEnd_2346998 < baseStart_2346998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347034 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_2347034 : Nat := 118140960795 + 2347034 * 2 ^ 59
def prefixEnd_2347034 : Nat := 4983230072969 + 3 ^ 40 * 2347034 * 2
def baseEnd_2347034 : Nat := 1205156554444675452381193

theorem tailTrace_2347034 : CollatzResearch.WordTrace tailWord_2347034 prefixEnd_2347034 1205156554444675452381193 := by
  unfold tailWord_2347034
  simp only [CollatzResearch.WordTrace]
  refine ⟨21400840644776033584922039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57068908386069422893125437 21400840644776033584922039)
  ·
    refine ⟨32101260967164050377383059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21400840644776033584922039 32101260967164050377383059)
    ·
      refine ⟨48151891450746075566074589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32101260967164050377383059 48151891450746075566074589)
      ·
        refine ⟨18056959294029778337277971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48151891450746075566074589 18056959294029778337277971)
        ·
          refine ⟨27085438941044667505916957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18056959294029778337277971 27085438941044667505916957)
          ·
            refine ⟨10157039602891750314718859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27085438941044667505916957 10157039602891750314718859)
            ·
              refine ⟨15235559404337625472078289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157039602891750314718859 15235559404337625472078289)
              ·
                refine ⟨11426669553253219104058717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15235559404337625472078289 11426669553253219104058717)
                ·
                  refine ⟨4285001082469957164022019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11426669553253219104058717 4285001082469957164022019)
                  ·
                    refine ⟨6427501623704935746033029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4285001082469957164022019 6427501623704935746033029)
                    ·
                      refine ⟨1205156554444675452381193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6427501623704935746033029 1205156554444675452381193)
                      ·
                        rfl

theorem cell23_2347034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_2347034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347034 prefixEnd_2347034 := by exact prefixLift 2347034
  have htrace : WordTrace (prefixWord ++ tailWord_2347034) baseStart_2347034 baseEnd_2347034 := by
    simpa [prefixWord, tailWord_2347034, baseEnd_2347034] using wordTrace_append hprefix tailTrace_2347034
  have hstable : (prefixWord ++ tailWord_2347034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347034).length < 2 ^ (prefixWord ++ tailWord_2347034).sum := by decide
  have hdescent : baseEnd_2347034 < baseStart_2347034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347065 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 1, 5]
def baseStart_2347065 : Nat := 118140960795 + 2347065 * 2 ^ 59
def prefixEnd_2347065 : Nat := 4983230072969 + 3 ^ 40 * 2347065 * 2
def baseEnd_2347065 : Nat := 401724157448321610364517

theorem tailTrace_2347065 : CollatzResearch.WordTrace tailWord_2347065 prefixEnd_2347065 401724157448321610364517 := by
  unfold tailWord_2347065
  simp only [CollatzResearch.WordTrace]
  refine ⟨85604493241991826634066649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57069662161327884422711099 85604493241991826634066649)
  ·
    refine ⟨64203369931493869975549987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85604493241991826634066649 64203369931493869975549987)
    ·
      refine ⟨96305054897240804963324981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64203369931493869975549987 96305054897240804963324981)
      ·
        refine ⟨9028598896616325465311717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96305054897240804963324981 9028598896616325465311717)
        ·
          refine ⟨1692862293115561024745947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9028598896616325465311717 1692862293115561024745947)
          ·
            refine ⟨2539293439673341537118921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692862293115561024745947 2539293439673341537118921)
            ·
              refine ⟨1904470079755006152839191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539293439673341537118921 1904470079755006152839191)
              ·
                refine ⟨2856705119632509229258787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904470079755006152839191 2856705119632509229258787)
                ·
                  refine ⟨4285057679448763843888181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856705119632509229258787 4285057679448763843888181)
                  ·
                    refine ⟨401724157448321610364517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4285057679448763843888181 401724157448321610364517)
                    ·
                      rfl

theorem cell23_2347065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 5].length) (baseStart_2347065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347065 prefixEnd_2347065 := by exact prefixLift 2347065
  have htrace : WordTrace (prefixWord ++ tailWord_2347065) baseStart_2347065 baseEnd_2347065 := by
    simpa [prefixWord, tailWord_2347065, baseEnd_2347065] using wordTrace_append hprefix tailTrace_2347065
  have hstable : (prefixWord ++ tailWord_2347065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347065).length < 2 ^ (prefixWord ++ tailWord_2347065).sum := by decide
  have hdescent : baseEnd_2347065 < baseStart_2347065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347077 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_2347077 : Nat := 118140960795 + 2347077 * 2 ^ 59
def prefixEnd_2347077 : Nat := 4983230072969 + 3 ^ 40 * 2347077 * 2
def baseEnd_2347077 : Nat := 1205178634112818784143495

theorem tailTrace_2347077 : CollatzResearch.WordTrace tailWord_2347077 prefixEnd_2347077 1205178634112818784143495 := by
  unfold tailWord_2347077
  simp only [CollatzResearch.WordTrace]
  refine ⟨85604930917948352683503485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57069953945298901789002323 85604930917948352683503485)
  ·
    refine ⟨32101849094230632256313807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85604930917948352683503485 32101849094230632256313807)
    ·
      refine ⟨48152773641345948384470711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32101849094230632256313807 48152773641345948384470711)
      ·
        refine ⟨72229160462018922576706067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48152773641345948384470711 72229160462018922576706067)
        ·
          refine ⟨108343740693028383865059101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72229160462018922576706067 108343740693028383865059101)
          ·
            refine ⟨40628902759885643949397163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108343740693028383865059101 40628902759885643949397163)
            ·
              refine ⟨60943354139828465924095745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40628902759885643949397163 60943354139828465924095745)
              ·
                refine ⟨45707515604871349443071809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60943354139828465924095745 45707515604871349443071809)
                ·
                  refine ⟨34280636703653512082303857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45707515604871349443071809 34280636703653512082303857)
                  ·
                    refine ⟨25710477527740134061727893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34280636703653512082303857 25710477527740134061727893)
                    ·
                      refine ⟨1205178634112818784143495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25710477527740134061727893 1205178634112818784143495)
                      ·
                        rfl

theorem cell23_2347077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_2347077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347077 prefixEnd_2347077 := by exact prefixLift 2347077
  have htrace : WordTrace (prefixWord ++ tailWord_2347077) baseStart_2347077 baseEnd_2347077 := by
    simpa [prefixWord, tailWord_2347077, baseEnd_2347077] using wordTrace_append hprefix tailTrace_2347077
  have hstable : (prefixWord ++ tailWord_2347077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347077).length < 2 ^ (prefixWord ++ tailWord_2347077).sum := by decide
  have hdescent : baseEnd_2347077 < baseStart_2347077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347078 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_2347078 : Nat := 118140960795 + 2347078 * 2 ^ 59
def prefixEnd_2347078 : Nat := 4983230072969 + 3 ^ 40 * 2347078 * 2
def baseEnd_2347078 : Nat := 401726382531157760076997

theorem tailTrace_2347078 : CollatzResearch.WordTrace tailWord_2347078 prefixEnd_2347078 401726382531157760076997 := by
  unfold tailWord_2347078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675155230967022807946559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57069978260629819902859925 2675155230967022807946559)
  ·
    refine ⟨4012732846450534211919839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2675155230967022807946559 4012732846450534211919839)
    ·
      refine ⟨6019099269675801317879759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012732846450534211919839 6019099269675801317879759)
      ·
        refine ⟨9028648904513701976819639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6019099269675801317879759 9028648904513701976819639)
        ·
          refine ⟨13542973356770552965229459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9028648904513701976819639 13542973356770552965229459)
          ·
            refine ⟨20314460035155829447844189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13542973356770552965229459 20314460035155829447844189)
            ·
              refine ⟨7617922513183436042941571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20314460035155829447844189 7617922513183436042941571)
              ·
                refine ⟨11426883769775154064412357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7617922513183436042941571 11426883769775154064412357)
                ·
                  refine ⟨2142540706832841387077317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11426883769775154064412357 2142540706832841387077317)
                  ·
                    refine ⟨401726382531157760076997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142540706832841387077317 401726382531157760076997)
                    ·
                      rfl

theorem cell23_2347078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_2347078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347078 prefixEnd_2347078 := by exact prefixLift 2347078
  have htrace : WordTrace (prefixWord ++ tailWord_2347078) baseStart_2347078 baseEnd_2347078 := by
    simpa [prefixWord, tailWord_2347078, baseEnd_2347078] using wordTrace_append hprefix tailTrace_2347078
  have hstable : (prefixWord ++ tailWord_2347078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347078).length < 2 ^ (prefixWord ++ tailWord_2347078).sum := by decide
  have hdescent : baseEnd_2347078 < baseStart_2347078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347084 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2347084 : Nat := 118140960795 + 2347084 * 2 ^ 59
def prefixEnd_2347084 : Nat := 4983230072969 + 3 ^ 40 * 2347084 * 2
def baseEnd_2347084 : Nat := 1205182228477400256755963

theorem tailTrace_2347084 : CollatzResearch.WordTrace tailWord_2347084 prefixEnd_2347084 1205182228477400256755963 := by
  unfold tailWord_2347084
  simp only [CollatzResearch.WordTrace]
  refine ⟨42802593114461496439504153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57070124152615328586005537 42802593114461496439504153)
  ·
    refine ⟨32101944835846122329628115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42802593114461496439504153 32101944835846122329628115)
    ·
      refine ⟨48152917253769183494442173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32101944835846122329628115 48152917253769183494442173)
      ·
        refine ⟨18057343970163443810415815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48152917253769183494442173 18057343970163443810415815)
        ·
          refine ⟨27086015955245165715623723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18057343970163443810415815 27086015955245165715623723)
          ·
            refine ⟨40629023932867748573435585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27086015955245165715623723 40629023932867748573435585)
            ·
              refine ⟨30471767949650811430076689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40629023932867748573435585 30471767949650811430076689)
              ·
                refine ⟨22853825962238108572557517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30471767949650811430076689 22853825962238108572557517)
                ·
                  refine ⟨8570184735839290714709069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22853825962238108572557517 8570184735839290714709069)
                  ·
                    refine ⟨3213819275939734018015901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8570184735839290714709069 3213819275939734018015901)
                    ·
                      refine ⟨1205182228477400256755963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3213819275939734018015901 1205182228477400256755963)
                      ·
                        rfl

theorem cell23_2347084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2347084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347084 prefixEnd_2347084 := by exact prefixLift 2347084
  have htrace : WordTrace (prefixWord ++ tailWord_2347084) baseStart_2347084 baseEnd_2347084 := by
    simpa [prefixWord, tailWord_2347084, baseEnd_2347084] using wordTrace_append hprefix tailTrace_2347084
  have hstable : (prefixWord ++ tailWord_2347084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347084).length < 2 ^ (prefixWord ++ tailWord_2347084).sum := by decide
  have hdescent : baseEnd_2347084 < baseStart_2347084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347085 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_2347085 : Nat := 118140960795 + 2347085 * 2 ^ 59
def prefixEnd_2347085 : Nat := 4983230072969 + 3 ^ 40 * 2347085 * 2
def baseEnd_2347085 : Nat := 1205182741958054752843459

theorem tailTrace_2347085 : CollatzResearch.WordTrace tailWord_2347085 prefixEnd_2347085 1205182741958054752843459 := by
  unfold tailWord_2347085
  simp only [CollatzResearch.WordTrace]
  refine ⟨85605222701919370049794709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57070148467946246699863139 85605222701919370049794709)
  ·
    refine ⟨4012744814152470471084127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85605222701919370049794709 4012744814152470471084127)
    ·
      refine ⟨6019117221228705706626191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012744814152470471084127 6019117221228705706626191)
      ·
        refine ⟨9028675831843058559939287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6019117221228705706626191 9028675831843058559939287)
        ·
          refine ⟨13543013747764587839908931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9028675831843058559939287 13543013747764587839908931)
          ·
            refine ⟨20314520621646881759863397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13543013747764587839908931 20314520621646881759863397)
            ·
              refine ⟨3808972616558790329974387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20314520621646881759863397 3808972616558790329974387)
              ·
                refine ⟨5713458924838185494961581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808972616558790329974387 5713458924838185494961581)
                ·
                  refine ⟨2142547096814319560610593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5713458924838185494961581 2142547096814319560610593)
                  ·
                    refine ⟨1606910322610739670457945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2142547096814319560610593 1606910322610739670457945)
                    ·
                      refine ⟨1205182741958054752843459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606910322610739670457945 1205182741958054752843459)
                      ·
                        rfl

theorem cell23_2347085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_2347085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347085 prefixEnd_2347085 := by exact prefixLift 2347085
  have htrace : WordTrace (prefixWord ++ tailWord_2347085) baseStart_2347085 baseEnd_2347085 := by
    simpa [prefixWord, tailWord_2347085, baseEnd_2347085] using wordTrace_append hprefix tailTrace_2347085
  have hstable : (prefixWord ++ tailWord_2347085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347085).length < 2 ^ (prefixWord ++ tailWord_2347085).sum := by decide
  have hdescent : baseEnd_2347085 < baseStart_2347085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347102 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2347102 : Nat := 118140960795 + 2347102 * 2 ^ 59
def prefixEnd_2347102 : Nat := 4983230072969 + 3 ^ 40 * 2347102 * 2
def baseEnd_2347102 : Nat := 1205191471129181186330881

theorem tailTrace_2347102 : CollatzResearch.WordTrace tailWord_2347102 prefixEnd_2347102 1205191471129181186330881 := by
  unfold tailWord_2347102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10700730342857222744145445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57070561828571854635442373 10700730342857222744145445)
  ·
    refine ⟨2006386939285729264527271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10700730342857222744145445 2006386939285729264527271)
    ·
      refine ⟨3009580408928593896790907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006386939285729264527271 3009580408928593896790907)
      ·
        refine ⟨4514370613392890845186361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3009580408928593896790907 4514370613392890845186361)
        ·
          refine ⟨3385777960044668133889771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4514370613392890845186361 3385777960044668133889771)
          ·
            refine ⟨5078666940067002200834657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385777960044668133889771 5078666940067002200834657)
            ·
              refine ⟨3809000205050251650625993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5078666940067002200834657 3809000205050251650625993)
              ·
                refine ⟨2856750153787688737969495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3809000205050251650625993 2856750153787688737969495)
                ·
                  refine ⟨4285125230681533106954243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856750153787688737969495 4285125230681533106954243)
                  ·
                    refine ⟨6427687846022299660431365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4285125230681533106954243 6427687846022299660431365)
                    ·
                      refine ⟨1205191471129181186330881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6427687846022299660431365 1205191471129181186330881)
                      ·
                        rfl

theorem cell23_2347102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2347102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347102 prefixEnd_2347102 := by exact prefixLift 2347102
  have htrace : WordTrace (prefixWord ++ tailWord_2347102) baseStart_2347102 baseEnd_2347102 := by
    simpa [prefixWord, tailWord_2347102, baseEnd_2347102] using wordTrace_append hprefix tailTrace_2347102
  have hstable : (prefixWord ++ tailWord_2347102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347102).length < 2 ^ (prefixWord ++ tailWord_2347102).sum := by decide
  have hdescent : baseEnd_2347102 < baseStart_2347102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347162 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2347162 : Nat := 118140960795 + 2347162 * 2 ^ 59
def prefixEnd_2347162 : Nat := 4983230072969 + 3 ^ 40 * 2347162 * 2
def baseEnd_2347162 : Nat := 1205222279968450951580605

theorem tailTrace_2347162 : CollatzResearch.WordTrace tailWord_2347162 prefixEnd_2347162 1205222279968450951580605 := by
  unfold tailWord_2347162
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402007780660103050086935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57072020748426941466898493 21402007780660103050086935)
  ·
    refine ⟨32103011670990154575130403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21402007780660103050086935 32103011670990154575130403)
    ·
      refine ⟨48154517506485231862695605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32103011670990154575130403 48154517506485231862695605)
      ·
        refine ⟨4514486016232990487127713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48154517506485231862695605 4514486016232990487127713)
        ·
          refine ⟨3385864512174742865345785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4514486016232990487127713 3385864512174742865345785)
          ·
            refine ⟨2539398384131057149009339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3385864512174742865345785 2539398384131057149009339)
            ·
              refine ⟨3809097576196585723514009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539398384131057149009339 3809097576196585723514009)
              ·
                refine ⟨2856823182147439292635507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3809097576196585723514009 2856823182147439292635507)
                ·
                  refine ⟨4285234773221158938953261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856823182147439292635507 4285234773221158938953261)
                  ·
                    refine ⟨1606963039957934602107473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4285234773221158938953261 1606963039957934602107473)
                    ·
                      refine ⟨1205222279968450951580605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606963039957934602107473 1205222279968450951580605)
                      ·
                        rfl

theorem cell23_2347162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2347162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347162 prefixEnd_2347162 := by exact prefixLift 2347162
  have htrace : WordTrace (prefixWord ++ tailWord_2347162) baseStart_2347162 baseEnd_2347162 := by
    simpa [prefixWord, tailWord_2347162, baseEnd_2347162] using wordTrace_append hprefix tailTrace_2347162
  have hstable : (prefixWord ++ tailWord_2347162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347162).length < 2 ^ (prefixWord ++ tailWord_2347162).sum := by decide
  have hdescent : baseEnd_2347162 < baseStart_2347162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347164 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 9]
def baseStart_2347164 : Nat := 118140960795 + 2347164 * 2 ^ 59
def prefixEnd_2347164 : Nat := 4983230072969 + 3 ^ 40 * 2347164 * 2
def baseEnd_2347164 : Nat := 133913700769973327083955

theorem tailTrace_2347164 : CollatzResearch.WordTrace tailWord_2347164 prefixEnd_2347164 133913700769973327083955 := by
  unfold tailWord_2347164
  simp only [CollatzResearch.WordTrace]
  refine ⟨42804052034316583270960273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57072069379088777694613697 42804052034316583270960273)
  ·
    refine ⟨32103039025737437453220205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42804052034316583270960273 32103039025737437453220205)
    ·
      refine ⟨12038639634651539044957577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32103039025737437453220205 12038639634651539044957577)
      ·
        refine ⟨9028979725988654283718183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12038639634651539044957577 9028979725988654283718183)
        ·
          refine ⟨13543469588982981425577275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9028979725988654283718183 13543469588982981425577275)
          ·
            refine ⟨20315204383474472138365913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13543469588982981425577275 20315204383474472138365913)
            ·
              refine ⟨15236403287605854103774435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20315204383474472138365913 15236403287605854103774435)
              ·
                refine ⟨22854604931408781155661653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15236403287605854103774435 22854604931408781155661653)
                ·
                  refine ⟨133913700769973327083955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22854604931408781155661653 133913700769973327083955)
                  ·
                    rfl

theorem cell23_2347164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_2347164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347164 prefixEnd_2347164 := by exact prefixLift 2347164
  have htrace : WordTrace (prefixWord ++ tailWord_2347164) baseStart_2347164 baseEnd_2347164 := by
    simpa [prefixWord, tailWord_2347164, baseEnd_2347164] using wordTrace_append hprefix tailTrace_2347164
  have hstable : (prefixWord ++ tailWord_2347164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347164).length < 2 ^ (prefixWord ++ tailWord_2347164).sum := by decide
  have hdescent : baseEnd_2347164 < baseStart_2347164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347175 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_2347175 : Nat := 118140960795 + 2347175 * 2 ^ 59
def prefixEnd_2347175 : Nat := 4983230072969 + 3 ^ 40 * 2347175 * 2
def baseEnd_2347175 : Nat := 1205228955216959400718045

theorem tailTrace_2347175 : CollatzResearch.WordTrace tailWord_2347175 prefixEnd_2347175 1205228955216959400718045 := by
  unfold tailWord_2347175
  simp only [CollatzResearch.WordTrace]
  refine ⟨85608505271593315420570979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57072336847728876947047319 85608505271593315420570979)
  ·
    refine ⟨128412757907389973130856469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85608505271593315420570979 128412757907389973130856469)
    ·
      refine ⟨6019348026908904990508897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128412757907389973130856469 6019348026908904990508897)
      ·
        refine ⟨4514511020181678742881673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6019348026908904990508897 4514511020181678742881673)
        ·
          refine ⟨3385883265136259057161255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4514511020181678742881673 3385883265136259057161255)
          ·
            refine ⟨5078824897704388585741883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385883265136259057161255 5078824897704388585741883)
            ·
              refine ⟨7618237346556582878612825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078824897704388585741883 7618237346556582878612825)
              ·
                refine ⟨5713678009917437158959619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7618237346556582878612825 5713678009917437158959619)
                ·
                  refine ⟨8570517014876155738439429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5713678009917437158959619 8570517014876155738439429)
                  ·
                    refine ⟨1606971940289279200957393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8570517014876155738439429 1606971940289279200957393)
                    ·
                      refine ⟨1205228955216959400718045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1606971940289279200957393 1205228955216959400718045)
                      ·
                        rfl

theorem cell23_2347175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_2347175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347175 prefixEnd_2347175 := by exact prefixLift 2347175
  have htrace : WordTrace (prefixWord ++ tailWord_2347175) baseStart_2347175 baseEnd_2347175 := by
    simpa [prefixWord, tailWord_2347175, baseEnd_2347175] using wordTrace_append hprefix tailTrace_2347175
  have hstable : (prefixWord ++ tailWord_2347175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347175).length < 2 ^ (prefixWord ++ tailWord_2347175).sum := by decide
  have hdescent : baseEnd_2347175 < baseStart_2347175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347231 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 3, 6, 2]
def baseStart_2347231 : Nat := 118140960795 + 2347231 * 2 ^ 59
def prefixEnd_2347231 : Nat := 4983230072969 + 3 ^ 40 * 2347231 * 2
def baseEnd_2347231 : Nat := 1205257710133611181617787

theorem tailTrace_2347231 : CollatzResearch.WordTrace tailWord_2347231 prefixEnd_2347231 1205257710133611181617787 := by
  unfold tailWord_2347231
  simp only [CollatzResearch.WordTrace]
  refine ⟨85610547759390436984609547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57073698506260291323073031 85610547759390436984609547)
  ·
    refine ⟨128415821639085655476914321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85610547759390436984609547 128415821639085655476914321)
    ·
      refine ⟨96311866229314241607685741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128415821639085655476914321 96311866229314241607685741)
      ·
        refine ⟨36116949835992840602882153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96311866229314241607685741 36116949835992840602882153)
        ·
          refine ⟨27087712376994630452161615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36116949835992840602882153 27087712376994630452161615)
          ·
            refine ⟨40631568565491945678242423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27087712376994630452161615 40631568565491945678242423)
            ·
              refine ⟨60947352848237918517363635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40631568565491945678242423 60947352848237918517363635)
              ·
                refine ⟨91421029272356877776045453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60947352848237918517363635 91421029272356877776045453)
                ·
                  refine ⟨34282885977133829166017045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91421029272356877776045453 34282885977133829166017045)
                  ·
                    refine ⟨1607010280178148242157049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34282885977133829166017045 1607010280178148242157049)
                    ·
                      refine ⟨1205257710133611181617787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607010280178148242157049 1205257710133611181617787)
                      ·
                        rfl

theorem cell23_2347231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_2347231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347231 prefixEnd_2347231 := by exact prefixLift 2347231
  have htrace : WordTrace (prefixWord ++ tailWord_2347231) baseStart_2347231 baseEnd_2347231 := by
    simpa [prefixWord, tailWord_2347231, baseEnd_2347231] using wordTrace_append hprefix tailTrace_2347231
  have hstable : (prefixWord ++ tailWord_2347231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347231).length < 2 ^ (prefixWord ++ tailWord_2347231).sum := by decide
  have hdescent : baseEnd_2347231 < baseStart_2347231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347244 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2347244 : Nat := 118140960795 + 2347244 * 2 ^ 59
def prefixEnd_2347244 : Nat := 4983230072969 + 3 ^ 40 * 2347244 * 2
def baseEnd_2347244 : Nat := 1205264385382119630755227

theorem tailTrace_2347244 : CollatzResearch.WordTrace tailWord_2347244 prefixEnd_2347244 1205264385382119630755227 := by
  unfold tailWord_2347244
  simp only [CollatzResearch.WordTrace]
  refine ⟨42805510954171670102416393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57074014605562226803221857 42805510954171670102416393)
  ·
    refine ⟨32104133215628752576812295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42805510954171670102416393 32104133215628752576812295)
    ·
      refine ⟨48156199823443128865218443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32104133215628752576812295 48156199823443128865218443)
      ·
        refine ⟨72234299735164693297827665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48156199823443128865218443 72234299735164693297827665)
        ·
          refine ⟨54175724801373519973370749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72234299735164693297827665 54175724801373519973370749)
          ·
            refine ⟨20315896800515069990014031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54175724801373519973370749 20315896800515069990014031)
            ·
              refine ⟨30473845200772604985021047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20315896800515069990014031 30473845200772604985021047)
              ·
                refine ⟨45710767801158907477531571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30473845200772604985021047 45710767801158907477531571)
                ·
                  refine ⟨68566151701738361216297357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45710767801158907477531571 68566151701738361216297357)
                  ·
                    refine ⟨25712306888151885456111509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68566151701738361216297357 25712306888151885456111509)
                    ·
                      refine ⟨1205264385382119630755227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25712306888151885456111509 1205264385382119630755227)
                      ·
                        rfl

theorem cell23_2347244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2347244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347244 prefixEnd_2347244 := by exact prefixLift 2347244
  have htrace : WordTrace (prefixWord ++ tailWord_2347244) baseStart_2347244 baseEnd_2347244 := by
    simpa [prefixWord, tailWord_2347244, baseEnd_2347244] using wordTrace_append hprefix tailTrace_2347244
  have hstable : (prefixWord ++ tailWord_2347244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347244).length < 2 ^ (prefixWord ++ tailWord_2347244).sum := by decide
  have hdescent : baseEnd_2347244 < baseStart_2347244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347251 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 3]
def baseStart_2347251 : Nat := 118140960795 + 2347251 * 2 ^ 59
def prefixEnd_2347251 : Nat := 4983230072969 + 3 ^ 40 * 2347251 * 2
def baseEnd_2347251 : Nat := 1205267979746701103367695

theorem tailTrace_2347251 : CollatzResearch.WordTrace tailWord_2347251 prefixEnd_2347251 1205267979746701103367695 := by
  unfold tailWord_2347251
  simp only [CollatzResearch.WordTrace]
  refine ⟨85611277219317980400337607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57074184812878653600225071 85611277219317980400337607)
  ·
    refine ⟨128416915828976970600506411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85611277219317980400337607 128416915828976970600506411)
    ·
      refine ⟨192625373743465455900759617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128416915828976970600506411 192625373743465455900759617)
      ·
        refine ⟨144469030307599091925569713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192625373743465455900759617 144469030307599091925569713)
        ·
          refine ⟨108351772730699318944177285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144469030307599091925569713 108351772730699318944177285)
          ·
            refine ⟨20315957387006122302033241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108351772730699318944177285 20315957387006122302033241)
            ·
              refine ⟨15236968040254591726524931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20315957387006122302033241 15236968040254591726524931)
              ·
                refine ⟨22855452060381887589787397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15236968040254591726524931 22855452060381887589787397)
                ·
                  refine ⟨4285397261321603923085137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22855452060381887589787397 4285397261321603923085137)
                  ·
                    refine ⟨3214047945991202942313853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4285397261321603923085137 3214047945991202942313853)
                    ·
                      refine ⟨1205267979746701103367695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3214047945991202942313853 1205267979746701103367695)
                      ·
                        rfl

theorem cell23_2347251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_2347251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347251 prefixEnd_2347251 := by exact prefixLift 2347251
  have htrace : WordTrace (prefixWord ++ tailWord_2347251) baseStart_2347251 baseEnd_2347251 := by
    simpa [prefixWord, tailWord_2347251, baseEnd_2347251] using wordTrace_append hprefix tailTrace_2347251
  have hstable : (prefixWord ++ tailWord_2347251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347251).length < 2 ^ (prefixWord ++ tailWord_2347251).sum := by decide
  have hdescent : baseEnd_2347251 < baseStart_2347251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347258 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_2347258 : Nat := 118140960795 + 2347258 * 2 ^ 59
def prefixEnd_2347258 : Nat := 4983230072969 + 3 ^ 40 * 2347258 * 2
def baseEnd_2347258 : Nat := 401757191370427525326721

theorem tailTrace_2347258 : CollatzResearch.WordTrace tailWord_2347258 prefixEnd_2347258 401757191370427525326721 := by
  unfold tailWord_2347258
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402883132573155148960607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57074355020195080397228285 21402883132573155148960607)
  ·
    refine ⟨32104324698859732723440911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21402883132573155148960607 32104324698859732723440911)
    ·
      refine ⟨48156487048289599085161367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32104324698859732723440911 48156487048289599085161367)
      ·
        refine ⟨72234730572434398627742051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48156487048289599085161367 72234730572434398627742051)
        ·
          refine ⟨108352095858651597941613077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72234730572434398627742051 108352095858651597941613077)
          ·
            refine ⟨5079004493374293653513113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108352095858651597941613077 5079004493374293653513113)
            ·
              refine ⟨3809253370030720240134835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5079004493374293653513113 3809253370030720240134835)
              ·
                refine ⟨5713880055046080360202253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809253370030720240134835 5713880055046080360202253)
                ·
                  refine ⟨2142705020642280135075845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5713880055046080360202253 2142705020642280135075845)
                  ·
                    refine ⟨401757191370427525326721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142705020642280135075845 401757191370427525326721)
                    ·
                      rfl

theorem cell23_2347258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_2347258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347258 prefixEnd_2347258 := by exact prefixLift 2347258
  have htrace : WordTrace (prefixWord ++ tailWord_2347258) baseStart_2347258 baseEnd_2347258 := by
    simpa [prefixWord, tailWord_2347258, baseEnd_2347258] using wordTrace_append hprefix tailTrace_2347258
  have hstable : (prefixWord ++ tailWord_2347258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347258).length < 2 ^ (prefixWord ++ tailWord_2347258).sum := by decide
  have hdescent : baseEnd_2347258 < baseStart_2347258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347308 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 4, 3, 2]
def baseStart_2347308 : Nat := 118140960795 + 2347308 * 2 ^ 59
def prefixEnd_2347308 : Nat := 4983230072969 + 3 ^ 40 * 2347308 * 2
def baseEnd_2347308 : Nat := 1205297248144007380354933

theorem tailTrace_2347308 : CollatzResearch.WordTrace tailWord_2347308 prefixEnd_2347308 1205297248144007380354933 := by
  unfold tailWord_2347308
  simp only [CollatzResearch.WordTrace]
  refine ⟨42806678090055739567581289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57075570786740986090108385 42806678090055739567581289)
  ·
    refine ⟨32105008567541804675685967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42806678090055739567581289 32105008567541804675685967)
    ·
      refine ⟨48157512851312707013528951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32105008567541804675685967 48157512851312707013528951)
      ·
        refine ⟨72236269276969060520293427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48157512851312707013528951 72236269276969060520293427)
        ·
          refine ⟨108354403915453590780440141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72236269276969060520293427 108354403915453590780440141)
          ·
            refine ⟨40632901468295096542665053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108354403915453590780440141 40632901468295096542665053)
            ·
              refine ⟨15237338050610661203499395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40632901468295096542665053 15237338050610661203499395)
              ·
                refine ⟨22856007075915991805249093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15237338050610661203499395 22856007075915991805249093)
                ·
                  refine ⟨4285501326734248463484205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22856007075915991805249093 4285501326734248463484205)
                  ·
                    refine ⟨1607062997525343173806577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4285501326734248463484205 1607062997525343173806577)
                    ·
                      refine ⟨1205297248144007380354933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607062997525343173806577 1205297248144007380354933)
                      ·
                        rfl

theorem cell23_2347308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_2347308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347308 prefixEnd_2347308 := by exact prefixLift 2347308
  have htrace : WordTrace (prefixWord ++ tailWord_2347308) baseStart_2347308 baseEnd_2347308 := by
    simpa [prefixWord, tailWord_2347308, baseEnd_2347308] using wordTrace_append hprefix tailTrace_2347308
  have hstable : (prefixWord ++ tailWord_2347308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347308).length < 2 ^ (prefixWord ++ tailWord_2347308).sum := by decide
  have hdescent : baseEnd_2347308 < baseStart_2347308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347309 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2347309 : Nat := 118140960795 + 2347309 * 2 ^ 59
def prefixEnd_2347309 : Nat := 4983230072969 + 3 ^ 40 * 2347309 * 2
def baseEnd_2347309 : Nat := 401765920541553958814143

theorem tailTrace_2347309 : CollatzResearch.WordTrace tailWord_2347309 prefixEnd_2347309 401765920541553958814143 := by
  unfold tailWord_2347309
  simp only [CollatzResearch.WordTrace]
  refine ⟨85613392653107856305948981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57075595102071904203965987 85613392653107856305948981)
  ·
    refine ⟨8026255561228861528682717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85613392653107856305948981 8026255561228861528682717)
    ·
      refine ⟨3009845835460823073256019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8026255561228861528682717 3009845835460823073256019)
      ·
        refine ⟨4514768753191234609884029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3009845835460823073256019 4514768753191234609884029)
        ·
          refine ⟨1693038282446712978706511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4514768753191234609884029 1693038282446712978706511)
          ·
            refine ⟨2539557423670069468059767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693038282446712978706511 2539557423670069468059767)
            ·
              refine ⟨3809336135505104202089651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539557423670069468059767 3809336135505104202089651)
              ·
                refine ⟨5714004203257656303134477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809336135505104202089651 5714004203257656303134477)
                ·
                  refine ⟨2142751576221621113675429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5714004203257656303134477 2142751576221621113675429)
                  ·
                    refine ⟨401765920541553958814143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142751576221621113675429 401765920541553958814143)
                    ·
                      rfl

theorem cell23_2347309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2347309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347309 prefixEnd_2347309 := by exact prefixLift 2347309
  have htrace : WordTrace (prefixWord ++ tailWord_2347309) baseStart_2347309 baseEnd_2347309 := by
    simpa [prefixWord, tailWord_2347309, baseEnd_2347309] using wordTrace_append hprefix tailTrace_2347309
  have hstable : (prefixWord ++ tailWord_2347309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347309).length < 2 ^ (prefixWord ++ tailWord_2347309).sum := by decide
  have hdescent : baseEnd_2347309 < baseStart_2347309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347348 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_2347348 : Nat := 118140960795 + 2347348 * 2 ^ 59
def prefixEnd_2347348 : Nat := 4983230072969 + 3 ^ 40 * 2347348 * 2
def baseEnd_2347348 : Nat := 401772595790062407951583

theorem tailTrace_2347348 : CollatzResearch.WordTrace tailWord_2347348 prefixEnd_2347348 401772595790062407951583 := by
  unfold tailWord_2347348
  simp only [CollatzResearch.WordTrace]
  refine ⟨42807407549983282983309349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57076543399977710644412465 42807407549983282983309349)
  ·
    refine ⟨8026388915621865559370503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42807407549983282983309349 8026388915621865559370503)
    ·
      refine ⟨12039583373432798339055755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8026388915621865559370503 12039583373432798339055755)
      ·
        refine ⟨18059375060149197508583633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12039583373432798339055755 18059375060149197508583633)
        ·
          refine ⟨13544531295111898131437725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18059375060149197508583633 13544531295111898131437725)
          ·
            refine ⟨5079199235666961799289147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13544531295111898131437725 5079199235666961799289147)
            ·
              refine ⟨7618798853500442698933721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079199235666961799289147 7618798853500442698933721)
              ·
                refine ⟨5714099140125332024200291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7618798853500442698933721 5714099140125332024200291)
                ·
                  refine ⟨8571148710187998036300437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5714099140125332024200291 8571148710187998036300437)
                  ·
                    refine ⟨401772595790062407951583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8571148710187998036300437 401772595790062407951583)
                    ·
                      rfl

theorem cell23_2347348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_2347348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347348 prefixEnd_2347348 := by exact prefixLift 2347348
  have htrace : WordTrace (prefixWord ++ tailWord_2347348) baseStart_2347348 baseEnd_2347348 := by
    simpa [prefixWord, tailWord_2347348, baseEnd_2347348] using wordTrace_append hprefix tailTrace_2347348
  have hstable : (prefixWord ++ tailWord_2347348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347348).length < 2 ^ (prefixWord ++ tailWord_2347348).sum := by decide
  have hdescent : baseEnd_2347348 < baseStart_2347348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347365 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_2347365 : Nat := 118140960795 + 2347365 * 2 ^ 59
def prefixEnd_2347365 : Nat := 4983230072969 + 3 ^ 40 * 2347365 * 2
def baseEnd_2347365 : Nat := 401775505513771219114057

theorem tailTrace_2347365 : CollatzResearch.WordTrace tailWord_2347365 prefixEnd_2347365 401775505513771219114057 := by
  unfold tailWord_2347365
  simp only [CollatzResearch.WordTrace]
  refine ⟨85615435140904977869987549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57076956760603318579991699 85615435140904977869987549)
  ·
    refine ⟨32105788177839366701245331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85615435140904977869987549 32105788177839366701245331)
    ·
      refine ⟨48158682266759050051867997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32105788177839366701245331 48158682266759050051867997)
      ·
        refine ⟨18059505850034643769450499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48158682266759050051867997 18059505850034643769450499)
        ·
          refine ⟨27089258775051965654175749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18059505850034643769450499 27089258775051965654175749)
          ·
            refine ⟨5079236020322243560157953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27089258775051965654175749 5079236020322243560157953)
            ·
              refine ⟨3809427015241682670118465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5079236020322243560157953 3809427015241682670118465)
              ·
                refine ⟨2857070261431262002588849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3809427015241682670118465 2857070261431262002588849)
                ·
                  refine ⟨2142802696073446501941637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2857070261431262002588849 2142802696073446501941637)
                  ·
                    refine ⟨401775505513771219114057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142802696073446501941637 401775505513771219114057)
                    ·
                      rfl

theorem cell23_2347365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_2347365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347365 prefixEnd_2347365 := by exact prefixLift 2347365
  have htrace : WordTrace (prefixWord ++ tailWord_2347365) baseStart_2347365 baseEnd_2347365 := by
    simpa [prefixWord, tailWord_2347365, baseEnd_2347365] using wordTrace_append hprefix tailTrace_2347365
  have hstable : (prefixWord ++ tailWord_2347365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347365).length < 2 ^ (prefixWord ++ tailWord_2347365).sum := by decide
  have hdescent : baseEnd_2347365 < baseStart_2347365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347378 : List Nat := [3, 2, 1, 2, 1, 5, 1, 8]
def baseStart_2347378 : Nat := 118140960795 + 2347378 * 2 ^ 59
def prefixEnd_2347378 : Nat := 4983230072969 + 3 ^ 40 * 2347378 * 2
def baseEnd_2347378 : Nat := 44641970066289707647393

theorem tailTrace_2347378 : CollatzResearch.WordTrace tailWord_2347378 prefixEnd_2347378 44641970066289707647393 := by
  unfold tailWord_2347378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21403977322464470272552697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57077272859905254060140525 21403977322464470272552697)
  ·
    refine ⟨16052982991848352704414523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21403977322464470272552697 16052982991848352704414523)
    ·
      refine ⟨24079474487772529056621785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16052982991848352704414523 24079474487772529056621785)
      ·
        refine ⟨18059605865829396792466339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24079474487772529056621785 18059605865829396792466339)
        ·
          refine ⟨27089408798744095188699509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18059605865829396792466339 27089408798744095188699509)
          ·
            refine ⟨2539632074882258923940579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27089408798744095188699509 2539632074882258923940579)
            ·
              refine ⟨3809448112323388385910869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539632074882258923940579 3809448112323388385910869)
              ·
                refine ⟨44641970066289707647393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3809448112323388385910869 44641970066289707647393)
                ·
                  rfl

theorem cell23_2347378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 8].length) (baseStart_2347378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347378 prefixEnd_2347378 := by exact prefixLift 2347378
  have htrace : WordTrace (prefixWord ++ tailWord_2347378) baseStart_2347378 baseEnd_2347378 := by
    simpa [prefixWord, tailWord_2347378, baseEnd_2347378] using wordTrace_append hprefix tailTrace_2347378
  have hstable : (prefixWord ++ tailWord_2347378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347378).length < 2 ^ (prefixWord ++ tailWord_2347378).sum := by decide
  have hdescent : baseEnd_2347378 < baseStart_2347378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347382 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_2347382 : Nat := 118140960795 + 2347382 * 2 ^ 59
def prefixEnd_2347382 : Nat := 4983230072969 + 3 ^ 40 * 2347382 * 2
def baseEnd_2347382 : Nat := 401778415237480030276531

theorem tailTrace_2347382 : CollatzResearch.WordTrace tailWord_2347382 prefixEnd_2347382 401778415237480030276531 := by
  unfold tailWord_2347382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5351003448865211860834775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57077370121228926515570933 5351003448865211860834775)
  ·
    refine ⟨8026505173297817791252163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5351003448865211860834775 8026505173297817791252163)
    ·
      refine ⟨12039757759946726686878245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8026505173297817791252163 12039757759946726686878245)
      ·
        refine ⟨2257454579990011253789671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12039757759946726686878245 2257454579990011253789671)
        ·
          refine ⟨3386181869985016880684507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257454579990011253789671 3386181869985016880684507)
          ·
            refine ⟨5079272804977525321026761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3386181869985016880684507 5079272804977525321026761)
            ·
              refine ⟨3809454603733143990770071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5079272804977525321026761 3809454603733143990770071)
              ·
                refine ⟨5714181905599715986155107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809454603733143990770071 5714181905599715986155107)
                ·
                  refine ⟨8571272858399573979232661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5714181905599715986155107 8571272858399573979232661)
                  ·
                    refine ⟨401778415237480030276531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8571272858399573979232661 401778415237480030276531)
                    ·
                      rfl

theorem cell23_2347382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_2347382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347382 prefixEnd_2347382 := by exact prefixLift 2347382
  have htrace : WordTrace (prefixWord ++ tailWord_2347382) baseStart_2347382 baseEnd_2347382 := by
    simpa [prefixWord, tailWord_2347382, baseEnd_2347382] using wordTrace_append hprefix tailTrace_2347382
  have hstable : (prefixWord ++ tailWord_2347382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347382).length < 2 ^ (prefixWord ++ tailWord_2347382).sum := by decide
  have hdescent : baseEnd_2347382 < baseStart_2347382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347406 : List Nat := [4, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2347406 : Nat := 118140960795 + 2347406 * 2 ^ 59
def prefixEnd_2347406 : Nat := 4983230072969 + 3 ^ 40 * 2347406 * 2
def baseEnd_2347406 : Nat := 1205347569248147996929483

theorem tailTrace_2347406 : CollatzResearch.WordTrace tailWord_2347406 prefixEnd_2347406 1205347569248147996929483 := by
  unfold tailWord_2347406
  simp only [CollatzResearch.WordTrace]
  refine ⟨10702116316719555234028759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57077953689170961248153381 10702116316719555234028759)
  ·
    refine ⟨16053174475079332851043139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10702116316719555234028759 16053174475079332851043139)
    ·
      refine ⟨24079761712618999276564709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16053174475079332851043139 24079761712618999276564709)
      ·
        refine ⟨4514955321116062364355883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24079761712618999276564709 4514955321116062364355883)
        ·
          refine ⟨6772432981674093546533825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4514955321116062364355883 6772432981674093546533825)
          ·
            refine ⟨5079324736255570159900369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6772432981674093546533825 5079324736255570159900369)
            ·
              refine ⟨3809493552191677619925277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5079324736255570159900369 3809493552191677619925277)
              ·
                refine ⟨1428560082071879107471979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3809493552191677619925277 1428560082071879107471979)
                ·
                  refine ⟨2142840123107818661207969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428560082071879107471979 2142840123107818661207969)
                  ·
                    refine ⟨1607130092330863995905977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2142840123107818661207969 1607130092330863995905977)
                    ·
                      refine ⟨1205347569248147996929483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607130092330863995905977 1205347569248147996929483)
                      ·
                        rfl

theorem cell23_2347406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2347406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347406 prefixEnd_2347406 := by exact prefixLift 2347406
  have htrace : WordTrace (prefixWord ++ tailWord_2347406) baseStart_2347406 baseEnd_2347406 := by
    simpa [prefixWord, tailWord_2347406, baseEnd_2347406] using wordTrace_append hprefix tailTrace_2347406
  have hstable : (prefixWord ++ tailWord_2347406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347406).length < 2 ^ (prefixWord ++ tailWord_2347406).sum := by decide
  have hdescent : baseEnd_2347406 < baseStart_2347406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347457 : List Nat := [1, 2, 7, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2347457 : Nat := 118140960795 + 2347457 * 2 ^ 59
def prefixEnd_2347457 : Nat := 4983230072969 + 3 ^ 40 * 2347457 * 2
def baseEnd_2347457 : Nat := 1205373756761527297391749

theorem tailTrace_2347457 : CollatzResearch.WordTrace tailWord_2347457 prefixEnd_2347457 1205373756761527297391749 := by
  unfold tailWord_2347457
  simp only [CollatzResearch.WordTrace]
  refine ⟨85618790656571677582336625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57079193771047785054891083 85618790656571677582336625)
  ·
    refine ⟨64214092992428758186752469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85618790656571677582336625 64214092992428758186752469)
    ·
      refine ⟨1505017804510049020002011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 64214092992428758186752469 1505017804510049020002011)
      ·
        refine ⟨2257526706765073530003017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1505017804510049020002011 2257526706765073530003017)
        ·
          refine ⟨1693145030073805147502263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2257526706765073530003017 1693145030073805147502263)
          ·
            refine ⟨2539717545110707721253395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693145030073805147502263 2539717545110707721253395)
            ·
              refine ⟨3809576317666061581880093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539717545110707721253395 3809576317666061581880093)
              ·
                refine ⟨1428591119124773093205035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3809576317666061581880093 1428591119124773093205035)
                ·
                  refine ⟨2142886678687159639807553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428591119124773093205035 2142886678687159639807553)
                  ·
                    refine ⟨1607165009015369729855665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2142886678687159639807553 1607165009015369729855665)
                    ·
                      refine ⟨1205373756761527297391749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607165009015369729855665 1205373756761527297391749)
                      ·
                        rfl

theorem cell23_2347457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2347457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347457 prefixEnd_2347457 := by exact prefixLift 2347457
  have htrace : WordTrace (prefixWord ++ tailWord_2347457) baseStart_2347457 baseEnd_2347457 := by
    simpa [prefixWord, tailWord_2347457, baseEnd_2347457] using wordTrace_append hprefix tailTrace_2347457
  have hstable : (prefixWord ++ tailWord_2347457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347457).length < 2 ^ (prefixWord ++ tailWord_2347457).sum := by decide
  have hdescent : baseEnd_2347457 < baseStart_2347457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347490 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2347490 : Nat := 118140960795 + 2347490 * 2 ^ 59
def prefixEnd_2347490 : Nat := 4983230072969 + 3 ^ 40 * 2347490 * 2
def baseEnd_2347490 : Nat := 1205390701623125668279097

theorem tailTrace_2347490 : CollatzResearch.WordTrace tailWord_2347490 prefixEnd_2347490 1205390701623125668279097 := by
  unfold tailWord_2347490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21404998566363031054571981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57079996176968082812191949 21404998566363031054571981)
  ·
    refine ⟨8026874462386136645464493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21404998566363031054571981 8026874462386136645464493)
    ·
      refine ⟨3010077923394801242049185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8026874462386136645464493 3010077923394801242049185)
      ·
        refine ⟨2257558442546100931536889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3010077923394801242049185 2257558442546100931536889)
        ·
          refine ⟨1693168831909575698652667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2257558442546100931536889 1693168831909575698652667)
          ·
            refine ⟨2539753247864363547979001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693168831909575698652667 2539753247864363547979001)
            ·
              refine ⟨1904814935898272660984251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539753247864363547979001 1904814935898272660984251)
              ·
                refine ⟨2857222403847408991476377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904814935898272660984251 2857222403847408991476377)
                ·
                  refine ⟨2142916802885556743607283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2857222403847408991476377 2142916802885556743607283)
                  ·
                    refine ⟨3214375204328335115410925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2142916802885556743607283 3214375204328335115410925)
                    ·
                      refine ⟨1205390701623125668279097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3214375204328335115410925 1205390701623125668279097)
                      ·
                        rfl

theorem cell23_2347490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2347490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347490 prefixEnd_2347490 := by exact prefixLift 2347490
  have htrace : WordTrace (prefixWord ++ tailWord_2347490) baseStart_2347490 baseEnd_2347490 := by
    simpa [prefixWord, tailWord_2347490, baseEnd_2347490] using wordTrace_append hprefix tailTrace_2347490
  have hstable : (prefixWord ++ tailWord_2347490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347490).length < 2 ^ (prefixWord ++ tailWord_2347490).sum := by decide
  have hdescent : baseEnd_2347490 < baseStart_2347490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347496 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_2347496 : Nat := 118140960795 + 2347496 * 2 ^ 59
def prefixEnd_2347496 : Nat := 4983230072969 + 3 ^ 40 * 2347496 * 2
def baseEnd_2347496 : Nat := 1205393782507052644804069

theorem tailTrace_2347496 : CollatzResearch.WordTrace tailWord_2347496 prefixEnd_2347496 1205393782507052644804069 := by
  unfold tailWord_2347496
  simp only [CollatzResearch.WordTrace]
  refine ⟨42810106551715193621503171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57080142068953591495337561 42810106551715193621503171)
  ·
    refine ⟨64215159827572790432254757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42810106551715193621503171 64215159827572790432254757)
    ·
      refine ⟨12040342467669898206047767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64215159827572790432254757 12040342467669898206047767)
      ·
        refine ⟨18060513701504847309071651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12040342467669898206047767 18060513701504847309071651)
        ·
          refine ⟨27090770552257270963607477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18060513701504847309071651 27090770552257270963607477)
          ·
            refine ⟨2539759739274119152838201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27090770552257270963607477 2539759739274119152838201)
            ·
              refine ⟨1904819804455589364628651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539759739274119152838201 1904819804455589364628651)
              ·
                refine ⟨2857229706683384046942977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904819804455589364628651 2857229706683384046942977)
                ·
                  refine ⟨2142922280012538035207233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2857229706683384046942977 2142922280012538035207233)
                  ·
                    refine ⟨1607191710009403526405425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2142922280012538035207233 1607191710009403526405425)
                    ·
                      refine ⟨1205393782507052644804069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607191710009403526405425 1205393782507052644804069)
                      ·
                        rfl

theorem cell23_2347496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_2347496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347496 prefixEnd_2347496 := by exact prefixLift 2347496
  have htrace : WordTrace (prefixWord ++ tailWord_2347496) baseStart_2347496 baseEnd_2347496 := by
    simpa [prefixWord, tailWord_2347496, baseEnd_2347496] using wordTrace_append hprefix tailTrace_2347496
  have hstable : (prefixWord ++ tailWord_2347496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347496).length < 2 ^ (prefixWord ++ tailWord_2347496).sum := by decide
  have hdescent : baseEnd_2347496 < baseStart_2347496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347562 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2347562 : Nat := 118140960795 + 2347562 * 2 ^ 59
def prefixEnd_2347562 : Nat := 4983230072969 + 3 ^ 40 * 2347562 * 2
def baseEnd_2347562 : Nat := 401809224076749795526255

theorem tailTrace_2347562 : CollatzResearch.WordTrace tailWord_2347562 prefixEnd_2347562 401809224076749795526255 := by
  unfold tailWord_2347562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21405655080297820128727235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57081746880794187009939293 21405655080297820128727235)
  ·
    refine ⟨32108482620446730193090853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21405655080297820128727235 32108482620446730193090853)
    ·
      refine ⟨6020340491333761911204535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32108482620446730193090853 6020340491333761911204535)
      ·
        refine ⟨9030510737000642866806803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6020340491333761911204535 9030510737000642866806803)
        ·
          refine ⟨13545766105500964300210205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9030510737000642866806803 13545766105500964300210205)
          ·
            refine ⟨5079662289562861612578827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13545766105500964300210205 5079662289562861612578827)
            ·
              refine ⟨7619493434344292418868241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079662289562861612578827 7619493434344292418868241)
              ·
                refine ⟨5714620075758219314151181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7619493434344292418868241 5714620075758219314151181)
                ·
                  refine ⟨2142982528409332242806693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5714620075758219314151181 2142982528409332242806693)
                  ·
                    refine ⟨401809224076749795526255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2142982528409332242806693 401809224076749795526255)
                    ·
                      rfl

theorem cell23_2347562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2347562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347562 prefixEnd_2347562 := by exact prefixLift 2347562
  have htrace : WordTrace (prefixWord ++ tailWord_2347562) baseStart_2347562 baseEnd_2347562 := by
    simpa [prefixWord, tailWord_2347562, baseEnd_2347562] using wordTrace_append hprefix tailTrace_2347562
  have hstable : (prefixWord ++ tailWord_2347562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347562).length < 2 ^ (prefixWord ++ tailWord_2347562).sum := by decide
  have hdescent : baseEnd_2347562 < baseStart_2347562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347625 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 8, 2]
def baseStart_2347625 : Nat := 118140960795 + 2347625 * 2 ^ 59
def prefixEnd_2347625 : Nat := 4983230072969 + 3 ^ 40 * 2347625 * 2
def baseEnd_2347625 : Nat := 1205460021511482640090975

theorem tailTrace_2347625 : CollatzResearch.WordTrace tailWord_2347625 prefixEnd_2347625 1205460021511482640090975 := by
  unfold tailWord_2347625
  simp only [CollatzResearch.WordTrace]
  refine ⟨85624918119963042274452329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57083278746642028182968219 85624918119963042274452329)
  ·
    refine ⟨64218688589972281705839247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85624918119963042274452329 64218688589972281705839247)
    ·
      refine ⟨96328032884958422558758871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64218688589972281705839247 96328032884958422558758871)
      ·
        refine ⟨144492049327437633838138307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96328032884958422558758871 144492049327437633838138307)
        ·
          refine ⟨216738073991156450757207461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144492049327437633838138307 216738073991156450757207461)
          ·
            refine ⟨40638388873341834516976399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216738073991156450757207461 40638388873341834516976399)
            ·
              refine ⟨60957583310012751775464599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40638388873341834516976399 60957583310012751775464599)
              ·
                refine ⟨91436374965019127663196899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60957583310012751775464599 91436374965019127663196899)
                ·
                  refine ⟨137154562447528691494795349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91436374965019127663196899 137154562447528691494795349)
                  ·
                    refine ⟨1607280028681976853454633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 137154562447528691494795349 1607280028681976853454633)
                    ·
                      refine ⟨1205460021511482640090975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1607280028681976853454633 1205460021511482640090975)
                      ·
                        rfl

theorem cell23_2347625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 8, 2].length) (baseStart_2347625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347625 prefixEnd_2347625 := by exact prefixLift 2347625
  have htrace : WordTrace (prefixWord ++ tailWord_2347625) baseStart_2347625 baseEnd_2347625 := by
    simpa [prefixWord, tailWord_2347625, baseEnd_2347625] using wordTrace_append hprefix tailTrace_2347625
  have hstable : (prefixWord ++ tailWord_2347625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347625).length < 2 ^ (prefixWord ++ tailWord_2347625).sum := by decide
  have hdescent : baseEnd_2347625 < baseStart_2347625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347648 : List Nat := [2, 1, 1, 2, 1, 5, 11]
def baseStart_2347648 : Nat := 118140960795 + 2347648 * 2 ^ 59
def prefixEnd_2347648 : Nat := 4983230072969 + 3 ^ 40 * 2347648 * 2
def baseEnd_2347648 : Nat := 14882368290944889507449

theorem tailTrace_2347648 : CollatzResearch.WordTrace tailWord_2347648 prefixEnd_2347648 14882368290944889507449 := by
  unfold tailWord_2347648
  simp only [CollatzResearch.WordTrace]
  refine ⟨42812878499439858601269799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57083837999253144801693065 42812878499439858601269799)
  ·
    refine ⟨64219317749159787901904699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42812878499439858601269799 64219317749159787901904699)
    ·
      refine ⟨96328976623739681852857049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64219317749159787901904699 96328976623739681852857049)
      ·
        refine ⟨72246732467804761389642787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96328976623739681852857049 72246732467804761389642787)
        ·
          refine ⟨108370098701707142084464181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72246732467804761389642787 108370098701707142084464181)
          ·
            refine ⟨10159696753285044570418517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108370098701707142084464181 10159696753285044570418517)
            ·
              refine ⟨14882368290944889507449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10159696753285044570418517 14882368290944889507449)
              ·
                rfl

theorem cell23_2347648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 11].length) (baseStart_2347648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347648 prefixEnd_2347648 := by exact prefixLift 2347648
  have htrace : WordTrace (prefixWord ++ tailWord_2347648) baseStart_2347648 baseEnd_2347648 := by
    simpa [prefixWord, tailWord_2347648, baseEnd_2347648] using wordTrace_append hprefix tailTrace_2347648
  have hstable : (prefixWord ++ tailWord_2347648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347648).length < 2 ^ (prefixWord ++ tailWord_2347648).sum := by decide
  have hdescent : baseEnd_2347648 < baseStart_2347648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347652 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_2347652 : Nat := 118140960795 + 2347652 * 2 ^ 59
def prefixEnd_2347652 : Nat := 4983230072969 + 3 ^ 40 * 2347652 * 2
def baseEnd_2347652 : Nat := 401824628496384678151117

theorem tailTrace_2347652 : CollatzResearch.WordTrace tailWord_2347652 prefixEnd_2347652 401824628496384678151117 := by
  unfold tailWord_2347652
  simp only [CollatzResearch.WordTrace]
  refine ⟨42812951445432612942842605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57083935260576817257123473 42812951445432612942842605)
  ·
    refine ⟨16054856792037229853565977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42812951445432612942842605 16054856792037229853565977)
    ·
      refine ⟨12041142594027922390174483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16054856792037229853565977 12041142594027922390174483)
      ·
        refine ⟨18061713891041883585261725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12041142594027922390174483 18061713891041883585261725)
        ·
          refine ⟨6773142709140706344473147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18061713891041883585261725 6773142709140706344473147)
          ·
            refine ⟨10159714063711059516709721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6773142709140706344473147 10159714063711059516709721)
            ·
              refine ⟨7619785547783294637532291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10159714063711059516709721 7619785547783294637532291)
              ·
                refine ⟨11429678321674941956298437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7619785547783294637532291 11429678321674941956298437)
                ·
                  refine ⟨2143064685314051616805957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11429678321674941956298437 2143064685314051616805957)
                  ·
                    refine ⟨401824628496384678151117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2143064685314051616805957 401824628496384678151117)
                    ·
                      rfl

theorem cell23_2347652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_2347652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2347652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2347652 prefixEnd_2347652 := by exact prefixLift 2347652
  have htrace : WordTrace (prefixWord ++ tailWord_2347652) baseStart_2347652 baseEnd_2347652 := by
    simpa [prefixWord, tailWord_2347652, baseEnd_2347652] using wordTrace_append hprefix tailTrace_2347652
  have hstable : (prefixWord ++ tailWord_2347652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347652).length < 2 ^ (prefixWord ++ tailWord_2347652).sum := by decide
  have hdescent : baseEnd_2347652 < baseStart_2347652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
