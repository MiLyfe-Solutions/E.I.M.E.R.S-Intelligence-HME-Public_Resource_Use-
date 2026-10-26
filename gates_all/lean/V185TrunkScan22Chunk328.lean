import V185TrunkScan22Chunk327

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2926809 : List Nat := [1, 2, 1, 2, 3, 1, 2, 6, 1, 3]
def baseStart_2926809 : Nat := 118140960795 + 2926809 * 2 ^ 59
def prefixEnd_2926809 : Nat := 4983230072969 + 3 ^ 40 * 2926809 * 2
def baseEnd_2926809 : Nat := 1001906533936763053351571

theorem tailTrace_2926809 : CollatzResearch.WordTrace tailWord_2926809 prefixEnd_2926809 1001906533936763053351571 := by
  unfold tailWord_2926809
  simp only [CollatzResearch.WordTrace]
  refine ⟨106749494053678327026487481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71166329369118884684324987 106749494053678327026487481)
  ·
    refine ⟨80062120540258745269865611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106749494053678327026487481 80062120540258745269865611)
    ·
      refine ⟨120093180810388117904798417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80062120540258745269865611 120093180810388117904798417)
      ·
        refine ⟨90069885607791088428598813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120093180810388117904798417 90069885607791088428598813)
        ·
          refine ⟨33776207102921658160724555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90069885607791088428598813 33776207102921658160724555)
          ·
            refine ⟨50664310654382487241086833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33776207102921658160724555 50664310654382487241086833)
            ·
              refine ⟨37998232990786865430815125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50664310654382487241086833 37998232990786865430815125)
              ·
                refine ⟨1781167171443134317069459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37998232990786865430815125 1781167171443134317069459)
                ·
                  refine ⟨2671750757164701475604189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781167171443134317069459 2671750757164701475604189)
                  ·
                    refine ⟨1001906533936763053351571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671750757164701475604189 1001906533936763053351571)
                    ·
                      rfl

theorem cell22_2926809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 3].length) (baseStart_2926809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926809 prefixEnd_2926809 := by exact prefixLift 2926809
  have htrace : WordTrace (prefixWord ++ tailWord_2926809) baseStart_2926809 baseEnd_2926809 := by
    simpa [prefixWord, tailWord_2926809, baseEnd_2926809] using wordTrace_append hprefix tailTrace_2926809
  have hstable : (prefixWord ++ tailWord_2926809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926809).length < 2 ^ (prefixWord ++ tailWord_2926809).sum := by decide
  have hdescent : baseEnd_2926809 < baseStart_2926809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926820 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2926820 : Nat := 118140960795 + 2926820 * 2 ^ 59
def prefixEnd_2926820 : Nat := 4983230072969 + 3 ^ 40 * 2926820 * 2
def baseEnd_2926820 : Nat := 1001910299461562691326537

theorem tailTrace_2926820 : CollatzResearch.WordTrace tailWord_2926820 prefixEnd_2926820 1001910299461562691326537 := by
  unfold tailWord_2926820
  simp only [CollatzResearch.WordTrace]
  refine ⟨53374947628319237952568957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71166596837758983936758609 53374947628319237952568957)
  ·
    refine ⟨20015605360619714232213359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53374947628319237952568957 20015605360619714232213359)
    ·
      refine ⟨30023408040929571348320039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20015605360619714232213359 30023408040929571348320039)
      ·
        refine ⟨45035112061394357022480059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30023408040929571348320039 45035112061394357022480059)
        ·
          refine ⟨67552668092091535533720089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45035112061394357022480059 67552668092091535533720089)
          ·
            refine ⟨50664501069068651650290067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67552668092091535533720089 50664501069068651650290067)
            ·
              refine ⟨75996751603602977475435101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50664501069068651650290067 75996751603602977475435101)
              ·
                refine ⟨28498781851351116553288163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75996751603602977475435101 28498781851351116553288163)
                ·
                  refine ⟨42748172777026674829932245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28498781851351116553288163 42748172777026674829932245)
                  ·
                    refine ⟨1001910299461562691326537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42748172777026674829932245 1001910299461562691326537)
                    ·
                      rfl

theorem cell22_2926820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2926820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926820 prefixEnd_2926820 := by exact prefixLift 2926820
  have htrace : WordTrace (prefixWord ++ tailWord_2926820) baseStart_2926820 baseEnd_2926820 := by
    simpa [prefixWord, tailWord_2926820, baseEnd_2926820] using wordTrace_append hprefix tailTrace_2926820
  have hstable : (prefixWord ++ tailWord_2926820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926820).length < 2 ^ (prefixWord ++ tailWord_2926820).sum := by decide
  have hdescent : baseEnd_2926820 < baseStart_2926820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926895 : List Nat := [1, 1, 2, 1, 2, 1, 4, 10]
def baseStart_2926895 : Nat := 118140960795 + 2926895 * 2 ^ 59
def prefixEnd_2926895 : Nat := 4983230072969 + 3 ^ 40 * 2926895 * 2
def baseEnd_2926895 : Nat := 111326219277143055077923

theorem tailTrace_2926895 : CollatzResearch.WordTrace tailWord_2926895 prefixEnd_2926895 111326219277143055077923 := by
  unfold tailWord_2926895
  simp only [CollatzResearch.WordTrace]
  refine ⟨106752630731366763714118139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71168420487577842476078759 106752630731366763714118139)
  ·
    refine ⟨160128946097050145571177209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106752630731366763714118139 160128946097050145571177209)
    ·
      refine ⟨120096709572787609178382907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160128946097050145571177209 120096709572787609178382907)
      ·
        refine ⟨180145064359181413767574361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120096709572787609178382907 180145064359181413767574361)
        ·
          refine ⟨135108798269386060325680771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180145064359181413767574361 135108798269386060325680771)
          ·
            refine ⟨202663197404079090488521157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135108798269386060325680771 202663197404079090488521157)
            ·
              refine ⟨37999349513264829466597717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202663197404079090488521157 37999349513264829466597717)
              ·
                refine ⟨111326219277143055077923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37999349513264829466597717 111326219277143055077923)
                ·
                  rfl

theorem cell22_2926895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 10].length) (baseStart_2926895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926895 prefixEnd_2926895 := by exact prefixLift 2926895
  have htrace : WordTrace (prefixWord ++ tailWord_2926895) baseStart_2926895 baseEnd_2926895 := by
    simpa [prefixWord, tailWord_2926895, baseEnd_2926895] using wordTrace_append hprefix tailTrace_2926895
  have hstable : (prefixWord ++ tailWord_2926895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926895).length < 2 ^ (prefixWord ++ tailWord_2926895).sum := by decide
  have hdescent : baseEnd_2926895 < baseStart_2926895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926933 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_2926933 : Nat := 118140960795 + 2926933 * 2 ^ 59
def prefixEnd_2926933 : Nat := 4983230072969 + 3 ^ 40 * 2926933 * 2
def baseEnd_2926933 : Nat := 1001948981670868063251191

theorem tailTrace_2926933 : CollatzResearch.WordTrace tailWord_2926933 prefixEnd_2926933 1001948981670868063251191 := by
  unfold tailWord_2926933
  simp only [CollatzResearch.WordTrace]
  refine ⟨106754016705229096204001453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71169344470152730802667635 106754016705229096204001453)
  ·
    refine ⟨40032756264460911076500545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106754016705229096204001453 40032756264460911076500545)
    ·
      refine ⟨30024567198345683307375409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40032756264460911076500545 30024567198345683307375409)
      ·
        refine ⟨22518425398759262480531557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30024567198345683307375409 22518425398759262480531557)
        ·
          refine ⟨4222204762267361715099667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22518425398759262480531557 4222204762267361715099667)
          ·
            refine ⟨6333307143401042572649501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222204762267361715099667 6333307143401042572649501)
            ·
              refine ⟨2374990178775390964743563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6333307143401042572649501 2374990178775390964743563)
              ·
                refine ⟨3562485268163086447115345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374990178775390964743563 3562485268163086447115345)
                ·
                  refine ⟨2671863951122314835336509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3562485268163086447115345 2671863951122314835336509)
                  ·
                    refine ⟨1001948981670868063251191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671863951122314835336509 1001948981670868063251191)
                    ·
                      rfl

theorem cell22_2926933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_2926933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926933 prefixEnd_2926933 := by exact prefixLift 2926933
  have htrace : WordTrace (prefixWord ++ tailWord_2926933) baseStart_2926933 baseEnd_2926933 := by
    simpa [prefixWord, tailWord_2926933, baseEnd_2926933] using wordTrace_append hprefix tailTrace_2926933
  have hstable : (prefixWord ++ tailWord_2926933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926933).length < 2 ^ (prefixWord ++ tailWord_2926933).sum := by decide
  have hdescent : baseEnd_2926933 < baseStart_2926933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926946 : List Nat := [3, 3, 2, 1, 1, 4, 2, 6]
def baseStart_2926946 : Nat := 118140960795 + 2926946 * 2 ^ 59
def prefixEnd_2926946 : Nat := 4983230072969 + 3 ^ 40 * 2926946 * 2
def baseEnd_2926946 : Nat := 111328159092948929186239

theorem tailTrace_2926946 : CollatzResearch.WordTrace tailWord_2926946 prefixEnd_2926946 111328159092948929186239 := by
  unfold tailWord_2926946
  simp only [CollatzResearch.WordTrace]
  refine ⟨26688622713545499856056173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71169660569454666282816461 26688622713545499856056173)
  ·
    refine ⟨10008233517579562446021065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26688622713545499856056173 10008233517579562446021065)
    ·
      refine ⟨7506175138184671834515799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10008233517579562446021065 7506175138184671834515799)
      ·
        refine ⟨11259262707277007751773699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7506175138184671834515799 11259262707277007751773699)
        ·
          refine ⟨16888894060915511627660549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11259262707277007751773699 16888894060915511627660549)
          ·
            refine ⟨3166667636421658430186353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16888894060915511627660549 3166667636421658430186353)
            ·
              refine ⟨2375000727316243822639765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3166667636421658430186353 2375000727316243822639765)
              ·
                refine ⟨111328159092948929186239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2375000727316243822639765 111328159092948929186239)
                ·
                  rfl

theorem cell22_2926946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_2926946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926946 prefixEnd_2926946 := by exact prefixLift 2926946
  have htrace : WordTrace (prefixWord ++ tailWord_2926946) baseStart_2926946 baseEnd_2926946 := by
    simpa [prefixWord, tailWord_2926946, baseEnd_2926946] using wordTrace_append hprefix tailTrace_2926946
  have hstable : (prefixWord ++ tailWord_2926946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926946).length < 2 ^ (prefixWord ++ tailWord_2926946).sum := by decide
  have hdescent : baseEnd_2926946 < baseStart_2926946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926957 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 9]
def baseStart_2926957 : Nat := 118140960795 + 2926957 * 2 ^ 59
def prefixEnd_2926957 : Nat := 4983230072969 + 3 ^ 40 * 2926957 * 2
def baseEnd_2926957 : Nat := 333985732453780000217039

theorem tailTrace_2926957 : CollatzResearch.WordTrace tailWord_2926957 prefixEnd_2926957 333985732453780000217039 := by
  unfold tailWord_2926957
  simp only [CollatzResearch.WordTrace]
  refine ⟨106754892057142148302875125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71169928038094765535250083 106754892057142148302875125)
  ·
    refine ⟨10008271130357076403394543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106754892057142148302875125 10008271130357076403394543)
    ·
      refine ⟨15012406695535614605091815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10008271130357076403394543 15012406695535614605091815)
      ·
        refine ⟨22518610043303421907637723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15012406695535614605091815 22518610043303421907637723)
        ·
          refine ⟨33777915064955132861456585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22518610043303421907637723 33777915064955132861456585)
          ·
            refine ⟨25333436298716349646092439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33777915064955132861456585 25333436298716349646092439)
            ·
              refine ⟨38000154448074524469138659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25333436298716349646092439 38000154448074524469138659)
              ·
                refine ⟨57000231672111786703707989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38000154448074524469138659 57000231672111786703707989)
                ·
                  refine ⟨333985732453780000217039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57000231672111786703707989 333985732453780000217039)
                  ·
                    rfl

theorem cell22_2926957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_2926957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926957 prefixEnd_2926957 := by exact prefixLift 2926957
  have htrace : WordTrace (prefixWord ++ tailWord_2926957) baseStart_2926957 baseEnd_2926957 := by
    simpa [prefixWord, tailWord_2926957, baseEnd_2926957] using wordTrace_append hprefix tailTrace_2926957
  have hstable : (prefixWord ++ tailWord_2926957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926957).length < 2 ^ (prefixWord ++ tailWord_2926957).sum := by decide
  have hdescent : baseEnd_2926957 < baseStart_2926957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2926972 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_2926972 : Nat := 118140960795 + 2926972 * 2 ^ 59
def prefixEnd_2926972 : Nat := 4983230072969 + 3 ^ 40 * 2926972 * 2
def baseEnd_2926972 : Nat := 1001962332167884961526071

theorem tailTrace_2926972 : CollatzResearch.WordTrace tailWord_2926972 prefixEnd_2926972 1001962332167884961526071 := by
  unfold tailWord_2926972
  simp only [CollatzResearch.WordTrace]
  refine ⟨53377719576043902932335585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71170292768058537243114113 53377719576043902932335585)
  ·
    refine ⟨40033289682032927199251689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53377719576043902932335585 40033289682032927199251689)
    ·
      refine ⟨30024967261524695399438767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40033289682032927199251689 30024967261524695399438767)
      ·
        refine ⟨45037450892287043099158151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30024967261524695399438767 45037450892287043099158151)
        ·
          refine ⟨67556176338430564648737227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45037450892287043099158151 67556176338430564648737227)
          ·
            refine ⟨101334264507645846973105841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67556176338430564648737227 101334264507645846973105841)
            ·
              refine ⟨76000698380734385229829381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101334264507645846973105841 76000698380734385229829381)
              ·
                refine ⟨14250130946387697230593009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76000698380734385229829381 14250130946387697230593009)
                ·
                  refine ⟨10687598209790772922944757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14250130946387697230593009 10687598209790772922944757)
                  ·
                    refine ⟨1001962332167884961526071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10687598209790772922944757 1001962332167884961526071)
                    ·
                      rfl

theorem cell22_2926972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_2926972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2926972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2926972 prefixEnd_2926972 := by exact prefixLift 2926972
  have htrace : WordTrace (prefixWord ++ tailWord_2926972) baseStart_2926972 baseEnd_2926972 := by
    simpa [prefixWord, tailWord_2926972, baseEnd_2926972] using wordTrace_append hprefix tailTrace_2926972
  have hstable : (prefixWord ++ tailWord_2926972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2926972).length < 2 ^ (prefixWord ++ tailWord_2926972).sum := by decide
  have hdescent : baseEnd_2926972 < baseStart_2926972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2926972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927032 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_2927032 : Nat := 118140960795 + 2927032 * 2 ^ 59
def prefixEnd_2927032 : Nat := 4983230072969 + 3 ^ 40 * 2927032 * 2
def baseEnd_2927032 : Nat := 1001982871394064805025887

theorem tailTrace_2927032 : CollatzResearch.WordTrace tailWord_2927032 prefixEnd_2927032 1001982871394064805025887 := by
  unfold tailWord_2927032
  simp only [CollatzResearch.WordTrace]
  refine ⟨53378813765935218055927675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71171751687913624074570233 53378813765935218055927675)
  ·
    refine ⟨80068220648902827083891513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53378813765935218055927675 80068220648902827083891513)
    ·
      refine ⟨60051165486677120312918635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80068220648902827083891513 60051165486677120312918635)
      ·
        refine ⟨90076748230015680469377953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60051165486677120312918635 90076748230015680469377953)
        ·
          refine ⟨67557561172511760352033465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90076748230015680469377953 67557561172511760352033465)
          ·
            refine ⟨50668170879383820264025099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67557561172511760352033465 50668170879383820264025099)
            ·
              refine ⟨76002256319075730396037649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50668170879383820264025099 76002256319075730396037649)
              ·
                refine ⟨57001692239306797797028237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76002256319075730396037649 57001692239306797797028237)
                ·
                  refine ⟨21375634589740049173885589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57001692239306797797028237 21375634589740049173885589)
                  ·
                    refine ⟨1001982871394064805025887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21375634589740049173885589 1001982871394064805025887)
                    ·
                      rfl

theorem cell22_2927032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_2927032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927032 prefixEnd_2927032 := by exact prefixLift 2927032
  have htrace : WordTrace (prefixWord ++ tailWord_2927032) baseStart_2927032 baseEnd_2927032 := by
    simpa [prefixWord, tailWord_2927032, baseEnd_2927032] using wordTrace_append hprefix tailTrace_2927032
  have hstable : (prefixWord ++ tailWord_2927032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927032).length < 2 ^ (prefixWord ++ tailWord_2927032).sum := by decide
  have hdescent : baseEnd_2927032 < baseStart_2927032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927034 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_2927034 : Nat := 118140960795 + 2927034 * 2 ^ 59
def prefixEnd_2927034 : Nat := 4983230072969 + 3 ^ 40 * 2927034 * 2
def baseEnd_2927034 : Nat := 1001983556034937466475881

theorem tailTrace_2927034 : CollatzResearch.WordTrace tailWord_2927034 prefixEnd_2927034 1001983556034937466475881 := by
  unfold tailWord_2927034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26689425119465797613357039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71171800318575460302285437 26689425119465797613357039)
  ·
    refine ⟨40034137679198696420035559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26689425119465797613357039 40034137679198696420035559)
    ·
      refine ⟨60051206518798044630053339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40034137679198696420035559 60051206518798044630053339)
      ·
        refine ⟨90076809778197066945080009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60051206518798044630053339 90076809778197066945080009)
        ·
          refine ⟨67557607333647800208810007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90076809778197066945080009 67557607333647800208810007)
          ·
            refine ⟨101336411000471700313215011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67557607333647800208810007 101336411000471700313215011)
            ·
              refine ⟨152004616500707550469822517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101336411000471700313215011 152004616500707550469822517)
              ·
                refine ⟨14250432796941332856545861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152004616500707550469822517 14250432796941332856545861)
                ·
                  refine ⟨2671956149426499910602349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14250432796941332856545861 2671956149426499910602349)
                  ·
                    refine ⟨1001983556034937466475881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2671956149426499910602349 1001983556034937466475881)
                    ·
                      rfl

theorem cell22_2927034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_2927034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927034 prefixEnd_2927034 := by exact prefixLift 2927034
  have htrace : WordTrace (prefixWord ++ tailWord_2927034) baseStart_2927034 baseEnd_2927034 := by
    simpa [prefixWord, tailWord_2927034, baseEnd_2927034] using wordTrace_append hprefix tailTrace_2927034
  have hstable : (prefixWord ++ tailWord_2927034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927034).length < 2 ^ (prefixWord ++ tailWord_2927034).sum := by decide
  have hdescent : baseEnd_2927034 < baseStart_2927034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927085 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_2927085 : Nat := 118140960795 + 2927085 * 2 ^ 59
def prefixEnd_2927085 : Nat := 4983230072969 + 3 ^ 40 * 2927085 * 2
def baseEnd_2927085 : Nat := 1002001014377190333450725

theorem tailTrace_2927085 : CollatzResearch.WordTrace tailWord_2927085 prefixEnd_2927085 1002001014377190333450725 := by
  unfold tailWord_2927085
  simp only [CollatzResearch.WordTrace]
  refine ⟨106759560600678426163534709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71173040400452284109023139 106759560600678426163534709)
  ·
    refine ⟨10008708806313602452831379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106759560600678426163534709 10008708806313602452831379)
    ·
      refine ⟨15013063209470403679247069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10008708806313602452831379 15013063209470403679247069)
      ·
        refine ⟨5629898703551401379717651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15013063209470403679247069 5629898703551401379717651)
        ·
          refine ⟨8444848055327102069576477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5629898703551401379717651 8444848055327102069576477)
          ·
            refine ⟨3166818020747663276091179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8444848055327102069576477 3166818020747663276091179)
            ·
              refine ⟨4750227031121494914136769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166818020747663276091179 4750227031121494914136769)
              ·
                refine ⟨3562670273341121185602577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4750227031121494914136769 3562670273341121185602577)
                ·
                  refine ⟨2672002705005840889201933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3562670273341121185602577 2672002705005840889201933)
                  ·
                    refine ⟨1002001014377190333450725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672002705005840889201933 1002001014377190333450725)
                    ·
                      rfl

theorem cell22_2927085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_2927085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927085 prefixEnd_2927085 := by exact prefixLift 2927085
  have htrace : WordTrace (prefixWord ++ tailWord_2927085) baseStart_2927085 baseEnd_2927085 := by
    simpa [prefixWord, tailWord_2927085, baseEnd_2927085] using wordTrace_append hprefix tailTrace_2927085
  have hstable : (prefixWord ++ tailWord_2927085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927085).length < 2 ^ (prefixWord ++ tailWord_2927085).sum := by decide
  have hdescent : baseEnd_2927085 < baseStart_2927085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927096 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 3, 3]
def baseStart_2927096 : Nat := 118140960795 + 2927096 * 2 ^ 59
def prefixEnd_2927096 : Nat := 4983230072969 + 3 ^ 40 * 2927096 * 2
def baseEnd_2927096 : Nat := 1002004779901989971425691

theorem tailTrace_2927096 : CollatzResearch.WordTrace tailWord_2927096 prefixEnd_2927096 1002004779901989971425691 := by
  unfold tailWord_2927096
  simp only [CollatzResearch.WordTrace]
  refine ⟨53379980901819287521092571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71173307869092383361456761 53379980901819287521092571)
  ·
    refine ⟨80069971352728931281638857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53379980901819287521092571 80069971352728931281638857)
    ·
      refine ⟨60052478514546698461229143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80069971352728931281638857 60052478514546698461229143)
      ·
        refine ⟨90078717771820047691843715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60052478514546698461229143 90078717771820047691843715)
        ·
          refine ⟨135118076657730071537765573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90078717771820047691843715 135118076657730071537765573)
          ·
            refine ⟨25334639373324388413331045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135118076657730071537765573 25334639373324388413331045)
            ·
              refine ⟨4750244882498322827499571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25334639373324388413331045 4750244882498322827499571)
              ·
                refine ⟨7125367323747484241249357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750244882498322827499571 7125367323747484241249357)
                ·
                  refine ⟨2672012746405306590468509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7125367323747484241249357 2672012746405306590468509)
                  ·
                    refine ⟨1002004779901989971425691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672012746405306590468509 1002004779901989971425691)
                    ·
                      rfl

theorem cell22_2927096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_2927096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927096 prefixEnd_2927096 := by exact prefixLift 2927096
  have htrace : WordTrace (prefixWord ++ tailWord_2927096) baseStart_2927096 baseEnd_2927096 := by
    simpa [prefixWord, tailWord_2927096, baseEnd_2927096] using wordTrace_append hprefix tailTrace_2927096
  have hstable : (prefixWord ++ tailWord_2927096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927096).length < 2 ^ (prefixWord ++ tailWord_2927096).sum := by decide
  have hdescent : baseEnd_2927096 < baseStart_2927096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927109 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 5]
def baseStart_2927109 : Nat := 118140960795 + 2927109 * 2 ^ 59
def prefixEnd_2927109 : Nat := 4983230072969 + 3 ^ 40 * 2927109 * 2
def baseEnd_2927109 : Nat := 334003076689220756950217

theorem tailTrace_2927109 : CollatzResearch.WordTrace tailWord_2927109 prefixEnd_2927109 334003076689220756950217 := by
  unfold tailWord_2927109
  simp only [CollatzResearch.WordTrace]
  refine ⟨106760435952591478262408381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71173623968394318841605587 106760435952591478262408381)
  ·
    refine ⟨40035163482221804348403143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106760435952591478262408381 40035163482221804348403143)
    ·
      refine ⟨60052745223332706522604715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40035163482221804348403143 60052745223332706522604715)
      ·
        refine ⟨90079117834999059783907073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60052745223332706522604715 90079117834999059783907073)
        ·
          refine ⟨67559338376249294837930305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90079117834999059783907073 67559338376249294837930305)
          ·
            refine ⟨50669503782186971128447729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67559338376249294837930305 50669503782186971128447729)
            ·
              refine ⟨38002127836640228346335797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50669503782186971128447729 38002127836640228346335797)
              ·
                refine ⟨3562699484685021407468981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38002127836640228346335797 3562699484685021407468981)
                ·
                  refine ⟨334003076689220756950217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3562699484685021407468981 334003076689220756950217)
                  ·
                    rfl

theorem cell22_2927109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_2927109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927109 prefixEnd_2927109 := by exact prefixLift 2927109
  have htrace : WordTrace (prefixWord ++ tailWord_2927109) baseStart_2927109 baseEnd_2927109 := by
    simpa [prefixWord, tailWord_2927109, baseEnd_2927109] using wordTrace_append hprefix tailTrace_2927109
  have hstable : (prefixWord ++ tailWord_2927109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927109).length < 2 ^ (prefixWord ++ tailWord_2927109).sum := by decide
  have hdescent : baseEnd_2927109 < baseStart_2927109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927173 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_2927173 : Nat := 118140960795 + 2927173 * 2 ^ 59
def prefixEnd_2927173 : Nat := 4983230072969 + 3 ^ 40 * 2927173 * 2
def baseEnd_2927173 : Nat := 1002031138575587437250455

theorem tailTrace_2927173 : CollatzResearch.WordTrace tailWord_2927173 prefixEnd_2927173 1002031138575587437250455 := by
  unfold tailWord_2927173
  simp only [CollatzResearch.WordTrace]
  refine ⟨106762770224359617192738173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71175180149573078128492115 106762770224359617192738173)
  ·
    refine ⟨40036038834134856447276815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106762770224359617192738173 40036038834134856447276815)
    ·
      refine ⟨60054058251202284670915223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40036038834134856447276815 60054058251202284670915223)
      ·
        refine ⟨90081087376803427006372835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60054058251202284670915223 90081087376803427006372835)
        ·
          refine ⟨135121631065205140509559253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90081087376803427006372835 135121631065205140509559253)
          ·
            refine ⟨3166913228090745480692795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 135121631065205140509559253 3166913228090745480692795)
            ·
              refine ⟨4750369842136118221039193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166913228090745480692795 4750369842136118221039193)
              ·
                refine ⟨3562777381602088665779395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4750369842136118221039193 3562777381602088665779395)
                ·
                  refine ⟨5344166072403132998669093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3562777381602088665779395 5344166072403132998669093)
                  ·
                    refine ⟨1002031138575587437250455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5344166072403132998669093 1002031138575587437250455)
                    ·
                      rfl

theorem cell22_2927173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_2927173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927173 prefixEnd_2927173 := by exact prefixLift 2927173
  have htrace : WordTrace (prefixWord ++ tailWord_2927173) baseStart_2927173 baseEnd_2927173 := by
    simpa [prefixWord, tailWord_2927173, baseEnd_2927173] using wordTrace_append hprefix tailTrace_2927173
  have hstable : (prefixWord ++ tailWord_2927173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927173).length < 2 ^ (prefixWord ++ tailWord_2927173).sum := by decide
  have hdescent : baseEnd_2927173 < baseStart_2927173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927186 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2927186 : Nat := 118140960795 + 2927186 * 2 ^ 59
def prefixEnd_2927186 : Nat := 4983230072969 + 3 ^ 40 * 2927186 * 2
def baseEnd_2927186 : Nat := 1002035588741259736675415

theorem tailTrace_2927186 : CollatzResearch.WordTrace tailWord_2927186 prefixEnd_2927186 1002035588741259736675415 := by
  unfold tailWord_2927186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26690811093328130103240353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71175496248875013608640941 26690811093328130103240353)
  ·
    refine ⟨20018108319996097577430265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26690811093328130103240353 20018108319996097577430265)
    ·
      refine ⟨15013581239997073183072699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20018108319996097577430265 15013581239997073183072699)
      ·
        refine ⟨22520371859995609774609049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15013581239997073183072699 22520371859995609774609049)
        ·
          refine ⟨16890278894996707330956787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22520371859995609774609049 16890278894996707330956787)
          ·
            refine ⟨25335418342495060996435181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16890278894996707330956787 25335418342495060996435181)
            ·
              refine ⟨9500781878435647873663193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25335418342495060996435181 9500781878435647873663193)
              ·
                refine ⟨7125586408826735905247395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9500781878435647873663193 7125586408826735905247395)
                ·
                  refine ⟨10688379613240103857871093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7125586408826735905247395 10688379613240103857871093)
                  ·
                    refine ⟨1002035588741259736675415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10688379613240103857871093 1002035588741259736675415)
                    ·
                      rfl

theorem cell22_2927186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2927186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927186 prefixEnd_2927186 := by exact prefixLift 2927186
  have htrace : WordTrace (prefixWord ++ tailWord_2927186) baseStart_2927186 baseEnd_2927186 := by
    simpa [prefixWord, tailWord_2927186, baseEnd_2927186] using wordTrace_append hprefix tailTrace_2927186
  have hstable : (prefixWord ++ tailWord_2927186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927186).length < 2 ^ (prefixWord ++ tailWord_2927186).sum := by decide
  have hdescent : baseEnd_2927186 < baseStart_2927186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927198 : List Nat := [4, 4, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2927198 : Nat := 118140960795 + 2927198 * 2 ^ 59
def prefixEnd_2927198 : Nat := 4983230072969 + 3 ^ 40 * 2927198 * 2
def baseEnd_2927198 : Nat := 1002039696586495705375379

theorem tailTrace_2927198 : CollatzResearch.WordTrace tailWord_2927198 prefixEnd_2927198 1002039696586495705375379 := by
  unfold tailWord_2927198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13345460256158630807799781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71175788032846030974932165 13345460256158630807799781)
  ·
    refine ⟨2502273798029743276462459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13345460256158630807799781 2502273798029743276462459)
    ·
      refine ⟨3753410697044614914693689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502273798029743276462459 3753410697044614914693689)
      ·
        refine ⟨2815058022783461186020267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3753410697044614914693689 2815058022783461186020267)
        ·
          refine ⟨4222587034175191779030401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815058022783461186020267 4222587034175191779030401)
          ·
            refine ⟨3166940275631393834272801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4222587034175191779030401 3166940275631393834272801)
            ·
              refine ⟨2375205206723545375704601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3166940275631393834272801 2375205206723545375704601)
              ·
                refine ⟨1781403905042659031778451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375205206723545375704601 1781403905042659031778451)
                ·
                  refine ⟨2672105857563988547667677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781403905042659031778451 2672105857563988547667677)
                  ·
                    refine ⟨1002039696586495705375379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672105857563988547667677 1002039696586495705375379)
                    ·
                      rfl

theorem cell22_2927198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2927198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927198 prefixEnd_2927198 := by exact prefixLift 2927198
  have htrace : WordTrace (prefixWord ++ tailWord_2927198) baseStart_2927198 baseEnd_2927198 := by
    simpa [prefixWord, tailWord_2927198, baseEnd_2927198] using wordTrace_append hprefix tailTrace_2927198
  have hstable : (prefixWord ++ tailWord_2927198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927198).length < 2 ^ (prefixWord ++ tailWord_2927198).sum := by decide
  have hdescent : baseEnd_2927198 < baseStart_2927198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927201 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_2927201 : Nat := 118140960795 + 2927201 * 2 ^ 59
def prefixEnd_2927201 : Nat := 4983230072969 + 3 ^ 40 * 2927201 * 2
def baseEnd_2927201 : Nat := 1002040723547804697550369

theorem tailTrace_2927201 : CollatzResearch.WordTrace tailWord_2927201 prefixEnd_2927201 1002040723547804697550369 := by
  unfold tailWord_2927201
  simp only [CollatzResearch.WordTrace]
  refine ⟨106763791468258177974757457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71175860978838785316504971 106763791468258177974757457)
  ·
    refine ⟨80072843601193633481068093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106763791468258177974757457 80072843601193633481068093)
    ·
      refine ⟨30027316350447612555400535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80072843601193633481068093 30027316350447612555400535)
      ·
        refine ⟨45040974525671418833100803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30027316350447612555400535 45040974525671418833100803)
        ·
          refine ⟨67561461788507128249651205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45040974525671418833100803 67561461788507128249651205)
          ·
            refine ⟨12667774085345086546809601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67561461788507128249651205 12667774085345086546809601)
            ·
              refine ⟨9500830564008814910107201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12667774085345086546809601 9500830564008814910107201)
              ·
                refine ⟨7125622923006611182580401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9500830564008814910107201 7125622923006611182580401)
                ·
                  refine ⟨5344217192254958386935301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7125622923006611182580401 5344217192254958386935301)
                  ·
                    refine ⟨1002040723547804697550369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5344217192254958386935301 1002040723547804697550369)
                    ·
                      rfl

theorem cell22_2927201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_2927201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927201 prefixEnd_2927201 := by exact prefixLift 2927201
  have htrace : WordTrace (prefixWord ++ tailWord_2927201) baseStart_2927201 baseEnd_2927201 := by
    simpa [prefixWord, tailWord_2927201, baseEnd_2927201] using wordTrace_append hprefix tailTrace_2927201
  have hstable : (prefixWord ++ tailWord_2927201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927201).length < 2 ^ (prefixWord ++ tailWord_2927201).sum := by decide
  have hdescent : baseEnd_2927201 < baseStart_2927201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927203 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 2, 3]
def baseStart_2927203 : Nat := 118140960795 + 2927203 * 2 ^ 59
def prefixEnd_2927203 : Nat := 4983230072969 + 3 ^ 40 * 2927203 * 2
def baseEnd_2927203 : Nat := 1002041408188677359000363

theorem tailTrace_2927203 : CollatzResearch.WordTrace tailWord_2927203 prefixEnd_2927203 1002041408188677359000363 := by
  unfold tailWord_2927203
  simp only [CollatzResearch.WordTrace]
  refine ⟨106763864414250932316330263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71175909609500621544220175 106763864414250932316330263)
  ·
    refine ⟨160145796621376398474495395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106763864414250932316330263 160145796621376398474495395)
    ·
      refine ⟨240218694932064597711743093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160145796621376398474495395 240218694932064597711743093)
      ·
        refine ⟨22520502649881056035475915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240218694932064597711743093 22520502649881056035475915)
        ·
          refine ⟨33780753974821584053213873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22520502649881056035475915 33780753974821584053213873)
          ·
            refine ⟨25335565481116188039910405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33780753974821584053213873 25335565481116188039910405)
            ·
              refine ⟨4750418527709285257483201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25335565481116188039910405 4750418527709285257483201)
              ·
                refine ⟨3562813895781963943112401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4750418527709285257483201 3562813895781963943112401)
                ·
                  refine ⟨2672110421836472957334301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3562813895781963943112401 2672110421836472957334301)
                  ·
                    refine ⟨1002041408188677359000363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672110421836472957334301 1002041408188677359000363)
                    ·
                      rfl

theorem cell22_2927203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 3].length) (baseStart_2927203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927203 prefixEnd_2927203 := by exact prefixLift 2927203
  have htrace : WordTrace (prefixWord ++ tailWord_2927203) baseStart_2927203 baseEnd_2927203 := by
    simpa [prefixWord, tailWord_2927203, baseEnd_2927203] using wordTrace_append hprefix tailTrace_2927203
  have hstable : (prefixWord ++ tailWord_2927203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927203).length < 2 ^ (prefixWord ++ tailWord_2927203).sum := by decide
  have hdescent : baseEnd_2927203 < baseStart_2927203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927265 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 3, 3]
def baseStart_2927265 : Nat := 118140960795 + 2927265 * 2 ^ 59
def prefixEnd_2927265 : Nat := 4983230072969 + 3 ^ 40 * 2927265 * 2
def baseEnd_2927265 : Nat := 1002062632055729863950173

theorem tailTrace_2927265 : CollatzResearch.WordTrace tailWord_2927265 prefixEnd_2927265 1002062632055729863950173 := by
  unfold tailWord_2927265
  simp only [CollatzResearch.WordTrace]
  refine ⟨106766125740026316905087249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71177417160017544603391499 106766125740026316905087249)
  ·
    refine ⟨80074594305019737678815437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106766125740026316905087249 80074594305019737678815437)
    ·
      refine ⟨30027972864382401629555789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80074594305019737678815437 30027972864382401629555789)
      ·
        refine ⟨11260489824143400611083421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30027972864382401629555789 11260489824143400611083421)
        ·
          refine ⟨4222683684053775229156283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11260489824143400611083421 4222683684053775229156283)
          ·
            refine ⟨6334025526080662843734425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222683684053775229156283 6334025526080662843734425)
            ·
              refine ⟨4750519144560497132800819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6334025526080662843734425 4750519144560497132800819)
              ·
                refine ⟨7125778716840745699201229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750519144560497132800819 7125778716840745699201229)
                ·
                  refine ⟨2672167018815279637200461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7125778716840745699201229 2672167018815279637200461)
                  ·
                    refine ⟨1002062632055729863950173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672167018815279637200461 1002062632055729863950173)
                    ·
                      rfl

theorem cell22_2927265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_2927265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927265 prefixEnd_2927265 := by exact prefixLift 2927265
  have htrace : WordTrace (prefixWord ++ tailWord_2927265) baseStart_2927265 baseEnd_2927265 := by
    simpa [prefixWord, tailWord_2927265, baseEnd_2927265] using wordTrace_append hprefix tailTrace_2927265
  have hstable : (prefixWord ++ tailWord_2927265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927265).length < 2 ^ (prefixWord ++ tailWord_2927265).sum := by decide
  have hdescent : baseEnd_2927265 < baseStart_2927265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927381 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2927381 : Nat := 118140960795 + 2927381 * 2 ^ 59
def prefixEnd_2927381 : Nat := 4983230072969 + 3 ^ 40 * 2927381 * 2
def baseEnd_2927381 : Nat := 1002102341226344228049817

theorem tailTrace_2927381 : CollatzResearch.WordTrace tailWord_2927381 prefixEnd_2927381 1002102341226344228049817 := by
  unfold tailWord_2927381
  simp only [CollatzResearch.WordTrace]
  refine ⟨106770356607606068716309997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71180237738404045810873331 106770356607606068716309997)
  ·
    refine ⟨40038883727852275768616249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106770356607606068716309997 40038883727852275768616249)
    ·
      refine ⟨30029162795889206826462187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40038883727852275768616249 30029162795889206826462187)
      ·
        refine ⟨45043744193833810239693281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30029162795889206826462187 45043744193833810239693281)
        ·
          refine ⟨33782808145375357679769961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45043744193833810239693281 33782808145375357679769961)
          ·
            refine ⟨25337106109031518259827471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33782808145375357679769961 25337106109031518259827471)
            ·
              refine ⟨38005659163547277389741207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25337106109031518259827471 38005659163547277389741207)
              ·
                refine ⟨57008488745320916084611811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38005659163547277389741207 57008488745320916084611811)
                ·
                  refine ⟨85512733117981374126917717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57008488745320916084611811 85512733117981374126917717)
                  ·
                    refine ⟨1002102341226344228049817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85512733117981374126917717 1002102341226344228049817)
                    ·
                      rfl

theorem cell22_2927381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2927381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927381 prefixEnd_2927381 := by exact prefixLift 2927381
  have htrace : WordTrace (prefixWord ++ tailWord_2927381) baseStart_2927381 baseEnd_2927381 := by
    simpa [prefixWord, tailWord_2927381, baseEnd_2927381] using wordTrace_append hprefix tailTrace_2927381
  have hstable : (prefixWord ++ tailWord_2927381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927381).length < 2 ^ (prefixWord ++ tailWord_2927381).sum := by decide
  have hdescent : baseEnd_2927381 < baseStart_2927381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927400 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2927400 : Nat := 118140960795 + 2927400 * 2 ^ 59
def prefixEnd_2927400 : Nat := 4983230072969 + 3 ^ 40 * 2927400 * 2
def baseEnd_2927400 : Nat := 1002108845314634511824759

theorem tailTrace_2927400 : CollatzResearch.WordTrace tailWord_2927400 prefixEnd_2927400 1002108845314634511824759 := by
  unfold tailWord_2927400
  simp only [CollatzResearch.WordTrace]
  refine ⟨53385524797268617480625827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71180699729691489974167769 53385524797268617480625827)
  ·
    refine ⟨80078287195902926220938741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53385524797268617480625827 80078287195902926220938741)
    ·
      refine ⟨7507339424615899333213007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80078287195902926220938741 7507339424615899333213007)
      ·
        refine ⟨11261009136923848999819511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7507339424615899333213007 11261009136923848999819511)
        ·
          refine ⟨16891513705385773499729267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11261009136923848999819511 16891513705385773499729267)
          ·
            refine ⟨25337270558078660249593901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16891513705385773499729267 25337270558078660249593901)
            ·
              refine ⟨9501476459279497593597713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25337270558078660249593901 9501476459279497593597713)
              ·
                refine ⟨7126107344459623195198285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9501476459279497593597713 7126107344459623195198285)
                ·
                  refine ⟨2672290254172358698199357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7126107344459623195198285 2672290254172358698199357)
                  ·
                    refine ⟨1002108845314634511824759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672290254172358698199357 1002108845314634511824759)
                    ·
                      rfl

theorem cell22_2927400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2927400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927400 prefixEnd_2927400 := by exact prefixLift 2927400
  have htrace : WordTrace (prefixWord ++ tailWord_2927400) baseStart_2927400 baseEnd_2927400 := by
    simpa [prefixWord, tailWord_2927400, baseEnd_2927400] using wordTrace_append hprefix tailTrace_2927400
  have hstable : (prefixWord ++ tailWord_2927400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927400).length < 2 ^ (prefixWord ++ tailWord_2927400).sum := by decide
  have hdescent : baseEnd_2927400 < baseStart_2927400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927402 : List Nat := [3, 1, 4, 3, 1, 1, 3, 6]
def baseStart_2927402 : Nat := 118140960795 + 2927402 * 2 ^ 59
def prefixEnd_2927402 : Nat := 4983230072969 + 3 ^ 40 * 2927402 * 2
def baseEnd_2927402 : Nat := 111345503328389685919417

theorem tailTrace_2927402 : CollatzResearch.WordTrace tailWord_2927402 prefixEnd_2927402 111345503328389685919417 := by
  unfold tailWord_2927402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26692780635132497325706115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71180748360353326201882973 26692780635132497325706115)
  ·
    refine ⟨40039170952698745988559173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26692780635132497325706115 40039170952698745988559173)
    ·
      refine ⟨7507344553631014872854845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40039170952698745988559173 7507344553631014872854845)
      ·
        refine ⟨2815254207611630577320567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7507344553631014872854845 2815254207611630577320567)
        ·
          refine ⟨4222881311417445865980851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815254207611630577320567 4222881311417445865980851)
          ·
            refine ⟨6334321967126168798971277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222881311417445865980851 6334321967126168798971277)
            ·
              refine ⟨2375370737672313299614229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6334321967126168798971277 2375370737672313299614229)
              ·
                refine ⟨111345503328389685919417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2375370737672313299614229 111345503328389685919417)
                ·
                  rfl

theorem cell22_2927402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_2927402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927402 prefixEnd_2927402 := by exact prefixLift 2927402
  have htrace : WordTrace (prefixWord ++ tailWord_2927402) baseStart_2927402 baseEnd_2927402 := by
    simpa [prefixWord, tailWord_2927402, baseEnd_2927402] using wordTrace_append hprefix tailTrace_2927402
  have hstable : (prefixWord ++ tailWord_2927402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927402).length < 2 ^ (prefixWord ++ tailWord_2927402).sum := by decide
  have hdescent : baseEnd_2927402 < baseStart_2927402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927460 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_2927460 : Nat := 118140960795 + 2927460 * 2 ^ 59
def prefixEnd_2927460 : Nat := 4983230072969 + 3 ^ 40 * 2927460 * 2
def baseEnd_2927460 : Nat := 1002129384540814355324575

theorem tailTrace_2927460 : CollatzResearch.WordTrace tailWord_2927460 prefixEnd_2927460 1002129384540814355324575 := by
  unfold tailWord_2927460
  simp only [CollatzResearch.WordTrace]
  refine ⟨53386618987159932604217917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71182158649546576805623889 53386618987159932604217917)
  ·
    refine ⟨20019982120184974726581719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53386618987159932604217917 20019982120184974726581719)
    ·
      refine ⟨30029973180277462089872579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20019982120184974726581719 30029973180277462089872579)
      ·
        refine ⟨45044959770416193134808869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30029973180277462089872579 45044959770416193134808869)
        ·
          refine ⟨8445929956953036212776663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45044959770416193134808869 8445929956953036212776663)
          ·
            refine ⟨12668894935429554319164995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8445929956953036212776663 12668894935429554319164995)
            ·
              refine ⟨19003342403144331478747493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12668894935429554319164995 19003342403144331478747493)
              ·
                refine ⟨3563126700589562152265155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19003342403144331478747493 3563126700589562152265155)
                ·
                  refine ⟨5344690050884343228397733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563126700589562152265155 5344690050884343228397733)
                  ·
                    refine ⟨1002129384540814355324575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5344690050884343228397733 1002129384540814355324575)
                    ·
                      rfl

theorem cell22_2927460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_2927460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927460 prefixEnd_2927460 := by exact prefixLift 2927460
  have htrace : WordTrace (prefixWord ++ tailWord_2927460) baseStart_2927460 baseEnd_2927460 := by
    simpa [prefixWord, tailWord_2927460, baseEnd_2927460] using wordTrace_append hprefix tailTrace_2927460
  have hstable : (prefixWord ++ tailWord_2927460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927460).length < 2 ^ (prefixWord ++ tailWord_2927460).sum := by decide
  have hdescent : baseEnd_2927460 < baseStart_2927460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927475 : List Nat := [1, 1, 1, 2, 2, 1, 7, 3, 4]
def baseStart_2927475 : Nat := 118140960795 + 2927475 * 2 ^ 59
def prefixEnd_2927475 : Nat := 4983230072969 + 3 ^ 40 * 2927475 * 2
def baseEnd_2927475 : Nat := 334044839782453105399843

theorem tailTrace_2927475 : CollatzResearch.WordTrace tailWord_2927475 prefixEnd_2927475 334044839782453105399843 := by
  unfold tailWord_2927475
  simp only [CollatzResearch.WordTrace]
  refine ⟨106773785069265522770231879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71182523379510348513487919 106773785069265522770231879)
  ·
    refine ⟨160160677603898284155347819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106773785069265522770231879 160160677603898284155347819)
    ·
      refine ⟨240241016405847426233021729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160160677603898284155347819 240241016405847426233021729)
      ·
        refine ⟨180180762304385569674766297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240241016405847426233021729 180180762304385569674766297)
        ·
          refine ⟨135135571728289177256074723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180180762304385569674766297 135135571728289177256074723)
          ·
            refine ⟨202703357592433765884112085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135135571728289177256074723 202703357592433765884112085)
            ·
              refine ⟨4750859943572666387908877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 202703357592433765884112085 4750859943572666387908877)
              ·
                refine ⟨1781572478839749895465829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4750859943572666387908877 1781572478839749895465829)
                ·
                  refine ⟨334044839782453105399843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781572478839749895465829 334044839782453105399843)
                  ·
                    rfl

theorem cell22_2927475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 4].length) (baseStart_2927475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927475 prefixEnd_2927475 := by exact prefixLift 2927475
  have htrace : WordTrace (prefixWord ++ tailWord_2927475) baseStart_2927475 baseEnd_2927475 := by
    simpa [prefixWord, tailWord_2927475, baseEnd_2927475] using wordTrace_append hprefix tailTrace_2927475
  have hstable : (prefixWord ++ tailWord_2927475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927475).length < 2 ^ (prefixWord ++ tailWord_2927475).sum := by decide
  have hdescent : baseEnd_2927475 < baseStart_2927475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927522 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2927522 : Nat := 118140960795 + 2927522 * 2 ^ 59
def prefixEnd_2927522 : Nat := 4983230072969 + 3 ^ 40 * 2927522 * 2
def baseEnd_2927522 : Nat := 1002150608407866860274385

theorem tailTrace_2927522 : CollatzResearch.WordTrace tailWord_2927522 prefixEnd_2927522 1002150608407866860274385 := by
  unfold tailWord_2927522
  simp only [CollatzResearch.WordTrace]
  refine ⟨26693874825023812449298205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71183666200063499864795213 26693874825023812449298205)
  ·
    refine ⟨10010203059383929668486827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26693874825023812449298205 10010203059383929668486827)
    ·
      refine ⟨15015304589075894502730241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10010203059383929668486827 15015304589075894502730241)
      ·
        refine ⟨11261478441806920877047681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15015304589075894502730241 11261478441806920877047681)
        ·
          refine ⟨8446108831355190657785761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11261478441806920877047681 8446108831355190657785761)
          ·
            refine ⟨6334581623516392993339321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8446108831355190657785761 6334581623516392993339321)
            ·
              refine ⟨4750936217637294745004491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6334581623516392993339321 4750936217637294745004491)
              ·
                refine ⟨7126404326455942117506737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750936217637294745004491 7126404326455942117506737)
                ·
                  refine ⟨5344803244841956588130053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7126404326455942117506737 5344803244841956588130053)
                  ·
                    refine ⟨1002150608407866860274385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5344803244841956588130053 1002150608407866860274385)
                    ·
                      rfl

theorem cell22_2927522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2927522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927522 prefixEnd_2927522 := by exact prefixLift 2927522
  have htrace : WordTrace (prefixWord ++ tailWord_2927522) baseStart_2927522 baseEnd_2927522 := by
    simpa [prefixWord, tailWord_2927522, baseEnd_2927522] using wordTrace_append hprefix tailTrace_2927522
  have hstable : (prefixWord ++ tailWord_2927522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927522).length < 2 ^ (prefixWord ++ tailWord_2927522).sum := by decide
  have hdescent : baseEnd_2927522 < baseStart_2927522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927558 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2927558 : Nat := 118140960795 + 2927558 * 2 ^ 59
def prefixEnd_2927558 : Nat := 4983230072969 + 3 ^ 40 * 2927558 * 2
def baseEnd_2927558 : Nat := 1002162931943574766374275

theorem tailTrace_2927558 : CollatzResearch.WordTrace tailWord_2927558 prefixEnd_2927558 1002162931943574766374275 := by
  unfold tailWord_2927558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3336775385248900873296979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71184541551976551963668885 3336775385248900873296979)
  ·
    refine ⟨5005163077873351309945469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3336775385248900873296979 5005163077873351309945469)
    ·
      refine ⟨1876936154202506741229551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5005163077873351309945469 1876936154202506741229551)
      ·
        refine ⟨2815404231303760111844327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876936154202506741229551 2815404231303760111844327)
        ·
          refine ⟨4223106346955640167766491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815404231303760111844327 4223106346955640167766491)
          ·
            refine ⟨6334659520433460251649737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223106346955640167766491 6334659520433460251649737)
            ·
              refine ⟨4750994640325095188737303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6334659520433460251649737 4750994640325095188737303)
              ·
                refine ⟨7126491960487642783105955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750994640325095188737303 7126491960487642783105955)
                ·
                  refine ⟨10689737940731464174658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126491960487642783105955 10689737940731464174658933)
                  ·
                    refine ⟨1002162931943574766374275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10689737940731464174658933 1002162931943574766374275)
                    ·
                      rfl

theorem cell22_2927558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2927558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927558 prefixEnd_2927558 := by exact prefixLift 2927558
  have htrace : WordTrace (prefixWord ++ tailWord_2927558) baseStart_2927558 baseEnd_2927558 := by
    simpa [prefixWord, tailWord_2927558, baseEnd_2927558] using wordTrace_append hprefix tailTrace_2927558
  have hstable : (prefixWord ++ tailWord_2927558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927558).length < 2 ^ (prefixWord ++ tailWord_2927558).sum := by decide
  have hdescent : baseEnd_2927558 < baseStart_2927558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927563 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 1, 7]
def baseStart_2927563 : Nat := 118140960795 + 2927563 * 2 ^ 59
def prefixEnd_2927563 : Nat := 4983230072969 + 3 ^ 40 * 2927563 * 2
def baseEnd_2927563 : Nat := 1002164643545756419999259

theorem tailTrace_2927563 : CollatzResearch.WordTrace tailWord_2927563 prefixEnd_2927563 1002164643545756419999259 := by
  unfold tailWord_2927563
  simp only [CollatzResearch.WordTrace]
  refine ⟨106776994692946713799435343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71184663128631142532956895 106776994692946713799435343)
  ·
    refine ⟨160165492039420070699153015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106776994692946713799435343 160165492039420070699153015)
    ·
      refine ⟨240248238059130106048729523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160165492039420070699153015 240248238059130106048729523)
      ·
        refine ⟨360372357088695159073094285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240248238059130106048729523 360372357088695159073094285)
        ·
          refine ⟨135139633908260684652410357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360372357088695159073094285 135139633908260684652410357)
          ·
            refine ⟨12669340678899439186163471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135139633908260684652410357 12669340678899439186163471)
            ·
              refine ⟨19004011018349158779245207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12669340678899439186163471 19004011018349158779245207)
              ·
                refine ⟨28506016527523738168867811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19004011018349158779245207 28506016527523738168867811)
                ·
                  refine ⟨42759024791285607253301717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28506016527523738168867811 42759024791285607253301717)
                  ·
                    refine ⟨1002164643545756419999259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42759024791285607253301717 1002164643545756419999259)
                    ·
                      rfl

theorem cell22_2927563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_2927563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927563 prefixEnd_2927563 := by exact prefixLift 2927563
  have htrace : WordTrace (prefixWord ++ tailWord_2927563) baseStart_2927563 baseEnd_2927563 := by
    simpa [prefixWord, tailWord_2927563, baseEnd_2927563] using wordTrace_append hprefix tailTrace_2927563
  have hstable : (prefixWord ++ tailWord_2927563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927563).length < 2 ^ (prefixWord ++ tailWord_2927563).sum := by decide
  have hdescent : baseEnd_2927563 < baseStart_2927563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927586 : List Nat := [3, 3, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2927586 : Nat := 118140960795 + 2927586 * 2 ^ 59
def prefixEnd_2927586 : Nat := 4983230072969 + 3 ^ 40 * 2927586 * 2
def baseEnd_2927586 : Nat := 1002172516915792026674189

theorem tailTrace_2927586 : CollatzResearch.WordTrace tailWord_2927586 prefixEnd_2927586 1002172516915792026674189 := by
  unfold tailWord_2927586
  simp only [CollatzResearch.WordTrace]
  refine ⟨26694458392965847181880653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71185222381242259151681741 26694458392965847181880653)
  ·
    refine ⟨10010421897362192693205245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26694458392965847181880653 10010421897362192693205245)
    ·
      refine ⟨3753908211510822259951967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10010421897362192693205245 3753908211510822259951967)
      ·
        refine ⟨5630862317266233389927951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3753908211510822259951967 5630862317266233389927951)
        ·
          refine ⟨8446293475899350084891927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5630862317266233389927951 8446293475899350084891927)
          ·
            refine ⟨12669440213849025127337891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8446293475899350084891927 12669440213849025127337891)
            ·
              refine ⟨19004160320773537691006837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12669440213849025127337891 19004160320773537691006837)
              ·
                refine ⟨1781640030072519158531891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19004160320773537691006837 1781640030072519158531891)
                ·
                  refine ⟨2672460045108778737797837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781640030072519158531891 2672460045108778737797837)
                  ·
                    refine ⟨1002172516915792026674189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672460045108778737797837 1002172516915792026674189)
                    ·
                      rfl

theorem cell22_2927586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2927586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927586 prefixEnd_2927586 := by exact prefixLift 2927586
  have htrace : WordTrace (prefixWord ++ tailWord_2927586) baseStart_2927586 baseEnd_2927586 := by
    simpa [prefixWord, tailWord_2927586, baseEnd_2927586] using wordTrace_append hprefix tailTrace_2927586
  have hstable : (prefixWord ++ tailWord_2927586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927586).length < 2 ^ (prefixWord ++ tailWord_2927586).sum := by decide
  have hdescent : baseEnd_2927586 < baseStart_2927586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927640 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_2927640 : Nat := 118140960795 + 2927640 * 2 ^ 59
def prefixEnd_2927640 : Nat := 4983230072969 + 3 ^ 40 * 2927640 * 2
def baseEnd_2927640 : Nat := 1002191002219353885824023

theorem tailTrace_2927640 : CollatzResearch.WordTrace tailWord_2927640 prefixEnd_2927640 1002191002219353885824023 := by
  unfold tailWord_2927640
  simp only [CollatzResearch.WordTrace]
  refine ⟨53389901556833877974994187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71186535409111837299992249 53389901556833877974994187)
  ·
    refine ⟨80084852335250816962491281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53389901556833877974994187 80084852335250816962491281)
    ·
      refine ⟨60063639251438112721868461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80084852335250816962491281 60063639251438112721868461)
      ·
        refine ⟨22523864719289292270700673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60063639251438112721868461 22523864719289292270700673)
        ·
          refine ⟨16892898539466969203025505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22523864719289292270700673 16892898539466969203025505)
          ·
            refine ⟨12669673904600226902269129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16892898539466969203025505 12669673904600226902269129)
            ·
              refine ⟨9502255428450170176701847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12669673904600226902269129 9502255428450170176701847)
              ·
                refine ⟨14253383142675255265052771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9502255428450170176701847 14253383142675255265052771)
                ·
                  refine ⟨21380074714012882897579157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14253383142675255265052771 21380074714012882897579157)
                  ·
                    refine ⟨1002191002219353885824023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21380074714012882897579157 1002191002219353885824023)
                    ·
                      rfl

theorem cell22_2927640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_2927640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927640 prefixEnd_2927640 := by exact prefixLift 2927640
  have htrace : WordTrace (prefixWord ++ tailWord_2927640) baseStart_2927640 baseEnd_2927640 := by
    simpa [prefixWord, tailWord_2927640, baseEnd_2927640] using wordTrace_append hprefix tailTrace_2927640
  have hstable : (prefixWord ++ tailWord_2927640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927640).length < 2 ^ (prefixWord ++ tailWord_2927640).sum := by decide
  have hdescent : baseEnd_2927640 < baseStart_2927640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927676 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_2927676 : Nat := 118140960795 + 2927676 * 2 ^ 59
def prefixEnd_2927676 : Nat := 4983230072969 + 3 ^ 40 * 2927676 * 2
def baseEnd_2927676 : Nat := 1002203325755061791923913

theorem tailTrace_2927676 : CollatzResearch.WordTrace tailWord_2927676 prefixEnd_2927676 1002203325755061791923913 := by
  unfold tailWord_2927676
  simp only [CollatzResearch.WordTrace]
  refine ⟨53390558070768667049149441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71187410761024889398865921 53390558070768667049149441)
  ·
    refine ⟨40042918553076500286862081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53390558070768667049149441 40042918553076500286862081)
    ·
      refine ⟨30032188914807375215146561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40042918553076500286862081 30032188914807375215146561)
      ·
        refine ⟨22524141686105531411359921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30032188914807375215146561 22524141686105531411359921)
        ·
          refine ⟨16893106264579148558519941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22524141686105531411359921 16893106264579148558519941)
          ·
            refine ⟨3167457424608590354722489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16893106264579148558519941 3167457424608590354722489)
            ·
              refine ⟨2375593068456442766041867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3167457424608590354722489 2375593068456442766041867)
              ·
                refine ⟨3563389602684664149062801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375593068456442766041867 3563389602684664149062801)
                ·
                  refine ⟨2672542202013498111797101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3563389602684664149062801 2672542202013498111797101)
                  ·
                    refine ⟨1002203325755061791923913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672542202013498111797101 1002203325755061791923913)
                    ·
                      rfl

theorem cell22_2927676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_2927676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927676 prefixEnd_2927676 := by exact prefixLift 2927676
  have htrace : WordTrace (prefixWord ++ tailWord_2927676) baseStart_2927676 baseEnd_2927676 := by
    simpa [prefixWord, tailWord_2927676, baseEnd_2927676] using wordTrace_append hprefix tailTrace_2927676
  have hstable : (prefixWord ++ tailWord_2927676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927676).length < 2 ^ (prefixWord ++ tailWord_2927676).sum := by decide
  have hdescent : baseEnd_2927676 < baseStart_2927676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927700 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 9]
def baseStart_2927700 : Nat := 118140960795 + 2927700 * 2 ^ 59
def prefixEnd_2927700 : Nat := 4983230072969 + 3 ^ 40 * 2927700 * 2
def baseEnd_2927700 : Nat := 334070513815177909774613

theorem tailTrace_2927700 : CollatzResearch.WordTrace tailWord_2927700 prefixEnd_2927700 334070513815177909774613 := by
  unfold tailWord_2927700
  simp only [CollatzResearch.WordTrace]
  refine ⟨53390995746725193098586277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71187994328966924131448369 53390995746725193098586277)
  ·
    refine ⟨10010811702510973705984927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53390995746725193098586277 10010811702510973705984927)
    ·
      refine ⟨15016217553766460558977391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10010811702510973705984927 15016217553766460558977391)
      ·
        refine ⟨22524326330649690838466087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15016217553766460558977391 22524326330649690838466087)
        ·
          refine ⟨33786489495974536257699131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22524326330649690838466087 33786489495974536257699131)
          ·
            refine ⟨50679734243961804386548697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33786489495974536257699131 50679734243961804386548697)
            ·
              refine ⟨38009800682971353289911523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50679734243961804386548697 38009800682971353289911523)
              ·
                refine ⟨57014701024457029934867285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38009800682971353289911523 57014701024457029934867285)
                ·
                  refine ⟨334070513815177909774613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57014701024457029934867285 334070513815177909774613)
                  ·
                    rfl

theorem cell22_2927700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_2927700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927700 prefixEnd_2927700 := by exact prefixLift 2927700
  have htrace : WordTrace (prefixWord ++ tailWord_2927700) baseStart_2927700 baseEnd_2927700 := by
    simpa [prefixWord, tailWord_2927700, baseEnd_2927700] using wordTrace_append hprefix tailTrace_2927700
  have hstable : (prefixWord ++ tailWord_2927700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927700).length < 2 ^ (prefixWord ++ tailWord_2927700).sum := by decide
  have hdescent : baseEnd_2927700 < baseStart_2927700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927704 : List Nat := [2, 1, 2, 2, 1, 3, 2, 5, 1, 3]
def baseStart_2927704 : Nat := 118140960795 + 2927704 * 2 ^ 59
def prefixEnd_2927704 : Nat := 4983230072969 + 3 ^ 40 * 2927704 * 2
def baseEnd_2927704 : Nat := 1002212910727279052223827

theorem tailTrace_2927704 : CollatzResearch.WordTrace tailWord_2927704 prefixEnd_2927704 1002212910727279052223827 := by
  unfold tailWord_2927704
  simp only [CollatzResearch.WordTrace]
  refine ⟨53391068692717947440159083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71188091590290596586878777 53391068692717947440159083)
  ·
    refine ⟨80086603039076921160238625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53391068692717947440159083 80086603039076921160238625)
    ·
      refine ⟨60064952279307690870178969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80086603039076921160238625 60064952279307690870178969)
      ·
        refine ⟨45048714209480768152634227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60064952279307690870178969 45048714209480768152634227)
        ·
          refine ⟨67573071314221152228951341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45048714209480768152634227 67573071314221152228951341)
          ·
            refine ⟨25339901742832932085856753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67573071314221152228951341 25339901742832932085856753)
            ·
              refine ⟨19004926307124699064392565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25339901742832932085856753 19004926307124699064392565)
              ·
                refine ⟨1781711841292940537286803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19004926307124699064392565 1781711841292940537286803)
                ·
                  refine ⟨2672567761939410805930205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781711841292940537286803 2672567761939410805930205)
                  ·
                    refine ⟨1002212910727279052223827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672567761939410805930205 1002212910727279052223827)
                    ·
                      rfl

theorem cell22_2927704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_2927704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927704 prefixEnd_2927704 := by exact prefixLift 2927704
  have htrace : WordTrace (prefixWord ++ tailWord_2927704) baseStart_2927704 baseEnd_2927704 := by
    simpa [prefixWord, tailWord_2927704, baseEnd_2927704] using wordTrace_append hprefix tailTrace_2927704
  have hstable : (prefixWord ++ tailWord_2927704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927704).length < 2 ^ (prefixWord ++ tailWord_2927704).sum := by decide
  have hdescent : baseEnd_2927704 < baseStart_2927704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927715 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 2, 5]
def baseStart_2927715 : Nat := 118140960795 + 2927715 * 2 ^ 59
def prefixEnd_2927715 : Nat := 4983230072969 + 3 ^ 40 * 2927715 * 2
def baseEnd_2927715 : Nat := 1002216676252078690198793

theorem tailTrace_2927715 : CollatzResearch.WordTrace tailWord_2927715 prefixEnd_2927715 1002216676252078690198793 := by
  unfold tailWord_2927715
  simp only [CollatzResearch.WordTrace]
  refine ⟨106782538588396043758968599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71188359058930695839312399 106782538588396043758968599)
  ·
    refine ⟨160173807882594065638452899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106782538588396043758968599 160173807882594065638452899)
    ·
      refine ⟨240260711823891098457679349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160173807882594065638452899 240260711823891098457679349)
      ·
        refine ⟨22524441733489790480407439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240260711823891098457679349 22524441733489790480407439)
        ·
          refine ⟨33786662600234685720611159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22524441733489790480407439 33786662600234685720611159)
          ·
            refine ⟨50679993900352028580916739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33786662600234685720611159 50679993900352028580916739)
            ·
              refine ⟨76019990850528042871375109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50679993900352028580916739 76019990850528042871375109)
              ·
                refine ⟨14253748284474008038382833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76019990850528042871375109 14253748284474008038382833)
                ·
                  refine ⟨10690311213355506028787125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14253748284474008038382833 10690311213355506028787125)
                  ·
                    refine ⟨1002216676252078690198793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10690311213355506028787125 1002216676252078690198793)
                    ·
                      rfl

theorem cell22_2927715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_2927715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927715 prefixEnd_2927715 := by exact prefixLift 2927715
  have htrace : WordTrace (prefixWord ++ tailWord_2927715) baseStart_2927715 baseEnd_2927715 := by
    simpa [prefixWord, tailWord_2927715, baseEnd_2927715] using wordTrace_append hprefix tailTrace_2927715
  have hstable : (prefixWord ++ tailWord_2927715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927715).length < 2 ^ (prefixWord ++ tailWord_2927715).sum := by decide
  have hdescent : baseEnd_2927715 < baseStart_2927715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927717 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 5]
def baseStart_2927717 : Nat := 118140960795 + 2927717 * 2 ^ 59
def prefixEnd_2927717 : Nat := 4983230072969 + 3 ^ 40 * 2927717 * 2
def baseEnd_2927717 : Nat := 334072453630983783882929

theorem tailTrace_2927717 : CollatzResearch.WordTrace tailWord_2927717 prefixEnd_2927717 334072453630983783882929 := by
  unfold tailWord_2927717
  simp only [CollatzResearch.WordTrace]
  refine ⟨106782611534388798100541405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71188407689592532067027603 106782611534388798100541405)
  ·
    refine ⟨40043479325395799287703027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106782611534388798100541405 40043479325395799287703027)
    ·
      refine ⟨60065218988093698931554541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40043479325395799287703027 60065218988093698931554541)
      ·
        refine ⟨22524457120535137099332953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60065218988093698931554541 22524457120535137099332953)
        ·
          refine ⟨16893342840401352824499715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22524457120535137099332953 16893342840401352824499715)
          ·
            refine ⟨25340014260602029236749573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16893342840401352824499715 25340014260602029236749573)
            ·
              refine ⟨4751252673862880481890545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25340014260602029236749573 4751252673862880481890545)
              ·
                refine ⟨3563439505397160361417909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4751252673862880481890545 3563439505397160361417909)
                ·
                  refine ⟨334072453630983783882929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3563439505397160361417909 334072453630983783882929)
                  ·
                    rfl

theorem cell22_2927717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_2927717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927717 prefixEnd_2927717 := by exact prefixLift 2927717
  have htrace : WordTrace (prefixWord ++ tailWord_2927717) baseStart_2927717 baseEnd_2927717 := by
    simpa [prefixWord, tailWord_2927717, baseEnd_2927717] using wordTrace_append hprefix tailTrace_2927717
  have hstable : (prefixWord ++ tailWord_2927717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927717).length < 2 ^ (prefixWord ++ tailWord_2927717).sum := by decide
  have hdescent : baseEnd_2927717 < baseStart_2927717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927721 : List Nat := [1, 2, 1, 1, 1, 6, 4, 2, 1, 3]
def baseStart_2927721 : Nat := 118140960795 + 2927721 * 2 ^ 59
def prefixEnd_2927721 : Nat := 4983230072969 + 3 ^ 40 * 2927721 * 2
def baseEnd_2927721 : Nat := 1002218730174696674548775

theorem tailTrace_2927721 : CollatzResearch.WordTrace tailWord_2927721 prefixEnd_2927721 1002218730174696674548775 := by
  unfold tailWord_2927721
  simp only [CollatzResearch.WordTrace]
  refine ⟨106782757426374306783687017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71188504950916204522458011 106782757426374306783687017)
  ·
    refine ⟨80087068069780730087765263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106782757426374306783687017 80087068069780730087765263)
    ·
      refine ⟨120130602104671095131647895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80087068069780730087765263 120130602104671095131647895)
      ·
        refine ⟨180195903157006642697471843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120130602104671095131647895 180195903157006642697471843)
        ·
          refine ⟨270293854735509964046207765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180195903157006642697471843 270293854735509964046207765)
          ·
            refine ⟨12670024440727029564665989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 270293854735509964046207765 12670024440727029564665989)
            ·
              refine ⟨2375629582636318043374873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12670024440727029564665989 2375629582636318043374873)
              ·
                refine ⟨1781722186977238532531155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375629582636318043374873 1781722186977238532531155)
                ·
                  refine ⟨2672583280465857798796733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781722186977238532531155 2672583280465857798796733)
                  ·
                    refine ⟨1002218730174696674548775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672583280465857798796733 1002218730174696674548775)
                    ·
                      rfl

theorem cell22_2927721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 3].length) (baseStart_2927721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927721 prefixEnd_2927721 := by exact prefixLift 2927721
  have htrace : WordTrace (prefixWord ++ tailWord_2927721) baseStart_2927721 baseEnd_2927721 := by
    simpa [prefixWord, tailWord_2927721, baseEnd_2927721] using wordTrace_append hprefix tailTrace_2927721
  have hstable : (prefixWord ++ tailWord_2927721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927721).length < 2 ^ (prefixWord ++ tailWord_2927721).sum := by decide
  have hdescent : baseEnd_2927721 < baseStart_2927721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927747 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 1, 4]
def baseStart_2927747 : Nat := 118140960795 + 2927747 * 2 ^ 59
def prefixEnd_2927747 : Nat := 4983230072969 + 3 ^ 40 * 2927747 * 2
def baseEnd_2927747 : Nat := 1002227630506041273398695

theorem tailTrace_2927747 : CollatzResearch.WordTrace tailWord_2927747 prefixEnd_2927747 1002227630506041273398695 := by
  unfold tailWord_2927747
  simp only [CollatzResearch.WordTrace]
  refine ⟨106783705724280113224133495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71189137149520075482755663 106783705724280113224133495)
  ·
    refine ⟨160175558586420169836200243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106783705724280113224133495 160175558586420169836200243)
    ·
      refine ⟨240263337879630254754300365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160175558586420169836200243 240263337879630254754300365)
      ·
        refine ⟨90098751704861345532862637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240263337879630254754300365 90098751704861345532862637)
        ·
          refine ⟨33787031889323004574823489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90098751704861345532862637 33787031889323004574823489)
          ·
            refine ⟨25340273916992253431117617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33787031889323004574823489 25340273916992253431117617)
            ·
              refine ⟨19005205437744190073338213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25340273916992253431117617 19005205437744190073338213)
              ·
                refine ⟨3563476019577035638750915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19005205437744190073338213 3563476019577035638750915)
                ·
                  refine ⟨5345214029365553458126373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563476019577035638750915 5345214029365553458126373)
                  ·
                    refine ⟨1002227630506041273398695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5345214029365553458126373 1002227630506041273398695)
                    ·
                      rfl

theorem cell22_2927747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 4].length) (baseStart_2927747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927747 prefixEnd_2927747 := by exact prefixLift 2927747
  have htrace : WordTrace (prefixWord ++ tailWord_2927747) baseStart_2927747 baseEnd_2927747 := by
    simpa [prefixWord, tailWord_2927747, baseEnd_2927747] using wordTrace_append hprefix tailTrace_2927747
  have hstable : (prefixWord ++ tailWord_2927747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927747).length < 2 ^ (prefixWord ++ tailWord_2927747).sum := by decide
  have hdescent : baseEnd_2927747 < baseStart_2927747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927760 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_2927760 : Nat := 118140960795 + 2927760 * 2 ^ 59
def prefixEnd_2927760 : Nat := 4983230072969 + 3 ^ 40 * 2927760 * 2
def baseEnd_2927760 : Nat := 1002232080671713572823655

theorem tailTrace_2927760 : CollatzResearch.WordTrace tailWord_2927760 prefixEnd_2927760 1002232080671713572823655 := by
  unfold tailWord_2927760
  simp only [CollatzResearch.WordTrace]
  refine ⟨53392089936616508222178367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71189453248822010962904489 53392089936616508222178367)
  ·
    refine ⟨80088134904924762333267551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53392089936616508222178367 80088134904924762333267551)
    ·
      refine ⟨120132202357387143499901327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80088134904924762333267551 120132202357387143499901327)
      ·
        refine ⟨180198303536080715249851991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120132202357387143499901327 180198303536080715249851991)
        ·
          refine ⟨270297455304121072874777987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180198303536080715249851991 270297455304121072874777987)
          ·
            refine ⟨405446182956181609312166981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270297455304121072874777987 405446182956181609312166981)
            ·
              refine ⟨76021159304284051746031309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405446182956181609312166981 76021159304284051746031309)
              ·
                refine ⟨28507934739106519404761741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76021159304284051746031309 28507934739106519404761741)
                ·
                  refine ⟨10690475527164944776785653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28507934739106519404761741 10690475527164944776785653)
                  ·
                    refine ⟨1002232080671713572823655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10690475527164944776785653 1002232080671713572823655)
                    ·
                      rfl

theorem cell22_2927760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_2927760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927760 prefixEnd_2927760 := by exact prefixLift 2927760
  have htrace : WordTrace (prefixWord ++ tailWord_2927760) baseStart_2927760 baseEnd_2927760 := by
    simpa [prefixWord, tailWord_2927760, baseEnd_2927760] using wordTrace_append hprefix tailTrace_2927760
  have hstable : (prefixWord ++ tailWord_2927760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927760).length < 2 ^ (prefixWord ++ tailWord_2927760).sum := by decide
  have hdescent : baseEnd_2927760 < baseStart_2927760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927794 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_2927794 : Nat := 118140960795 + 2927794 * 2 ^ 59
def prefixEnd_2927794 : Nat := 4983230072969 + 3 ^ 40 * 2927794 * 2
def baseEnd_2927794 : Nat := 1002243719566548817473551

theorem tailTrace_2927794 : CollatzResearch.WordTrace tailWord_2927794 prefixEnd_2927794 1002243719566548817473551 := by
  unfold tailWord_2927794
  simp only [CollatzResearch.WordTrace]
  refine ⟨26696354988777460062773609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71190279970073226834062957 26696354988777460062773609)
  ·
    refine ⟨20022266241583095047080207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26696354988777460062773609 20022266241583095047080207)
    ·
      refine ⟨30033399362374642570620311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20022266241583095047080207 30033399362374642570620311)
      ·
        refine ⟨45050099043561963855930467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30033399362374642570620311 45050099043561963855930467)
        ·
          refine ⟨67575148565342945783895701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45050099043561963855930467 67575148565342945783895701)
          ·
            refine ⟨3167585089000450583620111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67575148565342945783895701 3167585089000450583620111)
            ·
              refine ⟨4751377633500675875430167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167585089000450583620111 4751377633500675875430167)
              ·
                refine ⟨7127066450251013813145251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751377633500675875430167 7127066450251013813145251)
                ·
                  refine ⟨10690599675376520719717877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7127066450251013813145251 10690599675376520719717877)
                  ·
                    refine ⟨1002243719566548817473551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10690599675376520719717877 1002243719566548817473551)
                    ·
                      rfl

theorem cell22_2927794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_2927794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927794 prefixEnd_2927794 := by exact prefixLift 2927794
  have htrace : WordTrace (prefixWord ++ tailWord_2927794) baseStart_2927794 baseEnd_2927794 := by
    simpa [prefixWord, tailWord_2927794, baseEnd_2927794] using wordTrace_append hprefix tailTrace_2927794
  have hstable : (prefixWord ++ tailWord_2927794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927794).length < 2 ^ (prefixWord ++ tailWord_2927794).sum := by decide
  have hdescent : baseEnd_2927794 < baseStart_2927794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927807 : List Nat := [1, 1, 2, 2, 2, 2, 6, 6]
def baseStart_2927807 : Nat := 118140960795 + 2927807 * 2 ^ 59
def prefixEnd_2927807 : Nat := 4983230072969 + 3 ^ 40 * 2927807 * 2
def baseEnd_2927807 : Nat := 111360907748024568544279

theorem tailTrace_2927807 : CollatzResearch.WordTrace tailWord_2927807 prefixEnd_2927807 111360907748024568544279 := by
  unfold tailWord_2927807
  simp only [CollatzResearch.WordTrace]
  refine ⟨106785894104062743471317675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71190596069375162314211783 106785894104062743471317675)
  ·
    refine ⟨160178841156094115206976513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106785894104062743471317675 160178841156094115206976513)
    ·
      refine ⟨120134130867070586405232385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160178841156094115206976513 120134130867070586405232385)
      ·
        refine ⟨90100598150302939803924289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120134130867070586405232385 90100598150302939803924289)
        ·
          refine ⟨67575448612727204852943217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90100598150302939803924289 67575448612727204852943217)
          ·
            refine ⟨50681586459545403639707413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67575448612727204852943217 50681586459545403639707413)
            ·
              refine ⟨2375699365291190795611285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50681586459545403639707413 2375699365291190795611285)
              ·
                refine ⟨111360907748024568544279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2375699365291190795611285 111360907748024568544279)
                ·
                  rfl

theorem cell22_2927807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 6].length) (baseStart_2927807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927807 prefixEnd_2927807 := by exact prefixLift 2927807
  have htrace : WordTrace (prefixWord ++ tailWord_2927807) baseStart_2927807 baseEnd_2927807 := by
    simpa [prefixWord, tailWord_2927807, baseEnd_2927807] using wordTrace_append hprefix tailTrace_2927807
  have hstable : (prefixWord ++ tailWord_2927807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927807).length < 2 ^ (prefixWord ++ tailWord_2927807).sum := by decide
  have hdescent : baseEnd_2927807 < baseStart_2927807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927809 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2927809 : Nat := 118140960795 + 2927809 * 2 ^ 59
def prefixEnd_2927809 : Nat := 4983230072969 + 3 ^ 40 * 2927809 * 2
def baseEnd_2927809 : Nat := 1002248854373093778348505

theorem tailTrace_2927809 : CollatzResearch.WordTrace tailWord_2927809 prefixEnd_2927809 1002248854373093778348505 := by
  unfold tailWord_2927809
  simp only [CollatzResearch.WordTrace]
  refine ⟨106785967050055497812890481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71190644700036998541926987 106785967050055497812890481)
  ·
    refine ⟨80089475287541623359667861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106785967050055497812890481 80089475287541623359667861)
    ·
      refine ⟨3754194154103513594984431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80089475287541623359667861 3754194154103513594984431)
      ·
        refine ⟨5631291231155270392476647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754194154103513594984431 5631291231155270392476647)
        ·
          refine ⟨8446936846732905588714971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631291231155270392476647 8446936846732905588714971)
          ·
            refine ⟨12670405270099358383072457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8446936846732905588714971 12670405270099358383072457)
            ·
              refine ⟨9502803952574518787304343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12670405270099358383072457 9502803952574518787304343)
              ·
                refine ⟨14254205928861778180956515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9502803952574518787304343 14254205928861778180956515)
                ·
                  refine ⟨21381308893292667271434773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14254205928861778180956515 21381308893292667271434773)
                  ·
                    refine ⟨1002248854373093778348505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21381308893292667271434773 1002248854373093778348505)
                    ·
                      rfl

theorem cell22_2927809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2927809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927809 prefixEnd_2927809 := by exact prefixLift 2927809
  have htrace : WordTrace (prefixWord ++ tailWord_2927809) baseStart_2927809 baseEnd_2927809 := by
    simpa [prefixWord, tailWord_2927809, baseEnd_2927809] using wordTrace_append hprefix tailTrace_2927809
  have hstable : (prefixWord ++ tailWord_2927809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927809).length < 2 ^ (prefixWord ++ tailWord_2927809).sum := by decide
  have hdescent : baseEnd_2927809 < baseStart_2927809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927830 : List Nat := [5, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2927830 : Nat := 118140960795 + 2927830 * 2 ^ 59
def prefixEnd_2927830 : Nat := 4983230072969 + 3 ^ 40 * 2927830 * 2
def baseEnd_2927830 : Nat := 334085347700752241191147

theorem tailTrace_2927830 : CollatzResearch.WordTrace tailWord_2927830 prefixEnd_2927830 334085347700752241191147 := by
  unfold tailWord_2927830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674170811436213649962809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71191155321986278932936629 6674170811436213649962809)
  ·
    refine ⟨5005628108577160237472107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6674170811436213649962809 5005628108577160237472107)
    ·
      refine ⟨7508442162865740356208161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5005628108577160237472107 7508442162865740356208161)
      ·
        refine ⟨5631331622149305267156121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7508442162865740356208161 5631331622149305267156121)
        ·
          refine ⟨4223498716611978950367091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5631331622149305267156121 4223498716611978950367091)
          ·
            refine ⟨6335248074917968425550637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223498716611978950367091 6335248074917968425550637)
            ·
              refine ⟨2375718028094238159581489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6335248074917968425550637 2375718028094238159581489)
              ·
                refine ⟨1781788521070678619686117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375718028094238159581489 1781788521070678619686117)
                ·
                  refine ⟨334085347700752241191147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781788521070678619686117 334085347700752241191147)
                  ·
                    rfl

theorem cell22_2927830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2927830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927830 prefixEnd_2927830 := by exact prefixLift 2927830
  have htrace : WordTrace (prefixWord ++ tailWord_2927830) baseStart_2927830 baseEnd_2927830 := by
    simpa [prefixWord, tailWord_2927830, baseEnd_2927830] using wordTrace_append hprefix tailTrace_2927830
  have hstable : (prefixWord ++ tailWord_2927830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927830).length < 2 ^ (prefixWord ++ tailWord_2927830).sum := by decide
  have hdescent : baseEnd_2927830 < baseStart_2927830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927835 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 11]
def baseStart_2927835 : Nat := 118140960795 + 2927835 * 2 ^ 59
def prefixEnd_2927835 : Nat := 4983230072969 + 3 ^ 40 * 2927835 * 2
def baseEnd_2927835 : Nat := 334085918234812792399475

theorem tailTrace_2927835 : CollatzResearch.WordTrace tailWord_2927835 prefixEnd_2927835 334085918234812792399475 := by
  unfold tailWord_2927835
  simp only [CollatzResearch.WordTrace]
  refine ⟨106786915347961304253336959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71191276898640869502224639 106786915347961304253336959)
  ·
    refine ⟨160180373021941956380005439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106786915347961304253336959 160180373021941956380005439)
    ·
      refine ⟨240270559532912934570008159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160180373021941956380005439 240270559532912934570008159)
      ·
        refine ⟨360405839299369401855012239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240270559532912934570008159 360405839299369401855012239)
        ·
          refine ⟨540608758949054102782518359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360405839299369401855012239 540608758949054102782518359)
          ·
            refine ⟨810913138423581154173777539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540608758949054102782518359 810913138423581154173777539)
            ·
              refine ⟨1216369707635371731260666309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810913138423581154173777539 1216369707635371731260666309)
              ·
                refine ⟨228069320181632199611374933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1216369707635371731260666309 228069320181632199611374933)
                ·
                  refine ⟨334085918234812792399475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 228069320181632199611374933 334085918234812792399475)
                  ·
                    rfl

theorem cell22_2927835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 11].length) (baseStart_2927835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927835 prefixEnd_2927835 := by exact prefixLift 2927835
  have htrace : WordTrace (prefixWord ++ tailWord_2927835) baseStart_2927835 baseEnd_2927835 := by
    simpa [prefixWord, tailWord_2927835, baseEnd_2927835] using wordTrace_append hprefix tailTrace_2927835
  have hstable : (prefixWord ++ tailWord_2927835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927835).length < 2 ^ (prefixWord ++ tailWord_2927835).sum := by decide
  have hdescent : baseEnd_2927835 < baseStart_2927835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927839 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 3, 3]
def baseStart_2927839 : Nat := 118140960795 + 2927839 * 2 ^ 59
def prefixEnd_2927839 : Nat := 4983230072969 + 3 ^ 40 * 2927839 * 2
def baseEnd_2927839 : Nat := 1002259123986183700098413

theorem tailTrace_2927839 : CollatzResearch.WordTrace tailWord_2927839 prefixEnd_2927839 1002259123986183700098413 := by
  unfold tailWord_2927839
  simp only [CollatzResearch.WordTrace]
  refine ⟨106787061239946812936482571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71191374159964541957655047 106787061239946812936482571)
  ·
    refine ⟨160180591859920219404723857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106787061239946812936482571 160180591859920219404723857)
    ·
      refine ⟨120135443894940164553542893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160180591859920219404723857 120135443894940164553542893)
      ·
        refine ⟨45050791460602561707578585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120135443894940164553542893 45050791460602561707578585)
        ·
          refine ⟨33788093595451921280683939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45050791460602561707578585 33788093595451921280683939)
          ·
            refine ⟨50682140393177881921025909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33788093595451921280683939 50682140393177881921025909)
            ·
              refine ⟨4751450661860426430096179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50682140393177881921025909 4751450661860426430096179)
              ·
                refine ⟨7127175992790639645144269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751450661860426430096179 7127175992790639645144269)
                ·
                  refine ⟨2672690997296489866929101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7127175992790639645144269 2672690997296489866929101)
                  ·
                    refine ⟨1002259123986183700098413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672690997296489866929101 1002259123986183700098413)
                    ·
                      rfl

theorem cell22_2927839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_2927839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927839 prefixEnd_2927839 := by exact prefixLift 2927839
  have htrace : WordTrace (prefixWord ++ tailWord_2927839) baseStart_2927839 baseEnd_2927839 := by
    simpa [prefixWord, tailWord_2927839, baseEnd_2927839] using wordTrace_append hprefix tailTrace_2927839
  have hstable : (prefixWord ++ tailWord_2927839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927839).length < 2 ^ (prefixWord ++ tailWord_2927839).sum := by decide
  have hdescent : baseEnd_2927839 < baseStart_2927839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927845 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_2927845 : Nat := 118140960795 + 2927845 * 2 ^ 59
def prefixEnd_2927845 : Nat := 4983230072969 + 3 ^ 40 * 2927845 * 2
def baseEnd_2927845 : Nat := 1002261177908801684448395

theorem tailTrace_2927845 : CollatzResearch.WordTrace tailWord_2927845 prefixEnd_2927845 1002261177908801684448395 := by
  unfold tailWord_2927845
  simp only [CollatzResearch.WordTrace]
  refine ⟨106787280077925075961200989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71191520051950050640800659 106787280077925075961200989)
  ·
    refine ⟨40045230029221903485450371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106787280077925075961200989 40045230029221903485450371)
    ·
      refine ⟨60067845043832855228175557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40045230029221903485450371 60067845043832855228175557)
      ·
        refine ⟨11262720945718660355282917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60067845043832855228175557 11262720945718660355282917)
        ·
          refine ⟨2111760177322248816615547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11262720945718660355282917 2111760177322248816615547)
          ·
            refine ⟨3167640265983373224923321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111760177322248816615547 3167640265983373224923321)
            ·
              refine ⟨2375730199487529918692491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3167640265983373224923321 2375730199487529918692491)
              ·
                refine ⟨3563595299231294878038737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375730199487529918692491 3563595299231294878038737)
                ·
                  refine ⟨2672696474423471158529053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3563595299231294878038737 2672696474423471158529053)
                  ·
                    refine ⟨1002261177908801684448395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672696474423471158529053 1002261177908801684448395)
                    ·
                      rfl

theorem cell22_2927845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_2927845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927845 prefixEnd_2927845 := by exact prefixLift 2927845
  have htrace : WordTrace (prefixWord ++ tailWord_2927845) baseStart_2927845 baseEnd_2927845 := by
    simpa [prefixWord, tailWord_2927845, baseEnd_2927845] using wordTrace_append hprefix tailTrace_2927845
  have hstable : (prefixWord ++ tailWord_2927845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927845).length < 2 ^ (prefixWord ++ tailWord_2927845).sum := by decide
  have hdescent : baseEnd_2927845 < baseStart_2927845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927860 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2927860 : Nat := 118140960795 + 2927860 * 2 ^ 59
def prefixEnd_2927860 : Nat := 4983230072969 + 3 ^ 40 * 2927860 * 2
def baseEnd_2927860 : Nat := 1002266312715346645323349

theorem tailTrace_2927860 : CollatzResearch.WordTrace tailWord_2927860 prefixEnd_2927860 1002266312715346645323349 := by
  unfold tailWord_2927860
  simp only [CollatzResearch.WordTrace]
  refine ⟨53393913586435366761498517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71191884781913822348664689 53393913586435366761498517)
  ·
    refine ⟨2502839699364157816945243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53393913586435366761498517 2502839699364157816945243)
    ·
      refine ⟨3754259549046236725417865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502839699364157816945243 3754259549046236725417865)
      ·
        refine ⟨2815694661784677544063399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3754259549046236725417865 2815694661784677544063399)
        ·
          refine ⟨4223541992677016316095099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815694661784677544063399 4223541992677016316095099)
          ·
            refine ⟨6335312989015524474142649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223541992677016316095099 6335312989015524474142649)
            ·
              refine ⟨4751484741761643355606987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335312989015524474142649 4751484741761643355606987)
              ·
                refine ⟨7127227112642465033410481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751484741761643355606987 7127227112642465033410481)
                ·
                  refine ⟨5345420334481848775057861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7127227112642465033410481 5345420334481848775057861)
                  ·
                    refine ⟨1002266312715346645323349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5345420334481848775057861 1002266312715346645323349)
                    ·
                      rfl

theorem cell22_2927860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2927860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927860 prefixEnd_2927860 := by exact prefixLift 2927860
  have htrace : WordTrace (prefixWord ++ tailWord_2927860) baseStart_2927860 baseEnd_2927860 := by
    simpa [prefixWord, tailWord_2927860, baseEnd_2927860] using wordTrace_append hprefix tailTrace_2927860
  have hstable : (prefixWord ++ tailWord_2927860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927860).length < 2 ^ (prefixWord ++ tailWord_2927860).sum := by decide
  have hdescent : baseEnd_2927860 < baseStart_2927860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927914 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_2927914 : Nat := 118140960795 + 2927914 * 2 ^ 59
def prefixEnd_2927914 : Nat := 4983230072969 + 3 ^ 40 * 2927914 * 2
def baseEnd_2927914 : Nat := 334094932672969501491061

theorem tailTrace_2927914 : CollatzResearch.WordTrace tailWord_2927914 prefixEnd_2927914 334094932672969501491061 := by
  unfold tailWord_2927914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26697449178668775186365699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71193197809783400496975197 26697449178668775186365699)
  ·
    refine ⟨40046173768003162779548549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26697449178668775186365699 40046173768003162779548549)
    ·
      refine ⟨7508657581500593021165353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40046173768003162779548549 7508657581500593021165353)
      ·
        refine ⟨5631493186125444765874015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7508657581500593021165353 5631493186125444765874015)
        ·
          refine ⟨8447239779188167148811023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631493186125444765874015 8447239779188167148811023)
          ·
            refine ⟨12670859668782250723216535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8447239779188167148811023 12670859668782250723216535)
            ·
              refine ⟨19006289503173376084824803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12670859668782250723216535 19006289503173376084824803)
              ·
                refine ⟨28509434254760064127237205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19006289503173376084824803 28509434254760064127237205)
                ·
                  refine ⟨334094932672969501491061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28509434254760064127237205 334094932672969501491061)
                  ·
                    rfl

theorem cell22_2927914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_2927914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927914 prefixEnd_2927914 := by exact prefixLift 2927914
  have htrace : WordTrace (prefixWord ++ tailWord_2927914) baseStart_2927914 baseEnd_2927914 := by
    simpa [prefixWord, tailWord_2927914, baseEnd_2927914] using wordTrace_append hprefix tailTrace_2927914
  have hstable : (prefixWord ++ tailWord_2927914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927914).length < 2 ^ (prefixWord ++ tailWord_2927914).sum := by decide
  have hdescent : baseEnd_2927914 < baseStart_2927914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927933 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_2927933 : Nat := 118140960795 + 2927933 * 2 ^ 59
def prefixEnd_2927933 : Nat := 4983230072969 + 3 ^ 40 * 2927933 * 2
def baseEnd_2927933 : Nat := 1002291302107198788248125

theorem tailTrace_2927933 : CollatzResearch.WordTrace tailWord_2927933 prefixEnd_2927933 1002291302107198788248125 := by
  unfold tailWord_2927933
  simp only [CollatzResearch.WordTrace]
  refine ⟨106790489701606266990404453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71193659801070844660269635 106790489701606266990404453)
  ·
    refine ⟨20023216819051175060700835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106790489701606266990404453 20023216819051175060700835)
    ·
      refine ⟨30034825228576762591051253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20023216819051175060700835 30034825228576762591051253)
      ·
        refine ⟨2815764865179071492911055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30034825228576762591051253 2815764865179071492911055)
        ·
          refine ⟨4223647297768607239366583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815764865179071492911055 4223647297768607239366583)
          ·
            refine ⟨6335470946652910859049875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223647297768607239366583 6335470946652910859049875)
            ·
              refine ⟨9503206419979366288574813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335470946652910859049875 9503206419979366288574813)
              ·
                refine ⟨3563702407492262358215555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9503206419979366288574813 3563702407492262358215555)
                ·
                  refine ⟨5345553611238393537323333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563702407492262358215555 5345553611238393537323333)
                  ·
                    refine ⟨1002291302107198788248125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5345553611238393537323333 1002291302107198788248125)
                    ·
                      rfl

theorem cell22_2927933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_2927933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927933 prefixEnd_2927933 := by exact prefixLift 2927933
  have htrace : WordTrace (prefixWord ++ tailWord_2927933) baseStart_2927933 baseEnd_2927933 := by
    simpa [prefixWord, tailWord_2927933, baseEnd_2927933] using wordTrace_append hprefix tailTrace_2927933
  have hstable : (prefixWord ++ tailWord_2927933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927933).length < 2 ^ (prefixWord ++ tailWord_2927933).sum := by decide
  have hdescent : baseEnd_2927933 < baseStart_2927933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2927982 : List Nat := [4, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_2927982 : Nat := 118140960795 + 2927982 * 2 ^ 59
def prefixEnd_2927982 : Nat := 4983230072969 + 3 ^ 40 * 2927982 * 2
def baseEnd_2927982 : Nat := 334102691936192997924325

theorem tailTrace_2927982 : CollatzResearch.WordTrace tailWord_2927982 prefixEnd_2927982 334102691936192997924325 := by
  unfold tailWord_2927982
  simp only [CollatzResearch.WordTrace]
  refine ⟨13349034609803593544867275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71194851252285832239292133 13349034609803593544867275)
  ·
    refine ⟨20023551914705390317300913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13349034609803593544867275 20023551914705390317300913)
    ·
      refine ⟨15017663936029042737975685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20023551914705390317300913 15017663936029042737975685)
      ·
        refine ⟨2815811988005445513370441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15017663936029042737975685 2815811988005445513370441)
        ·
          refine ⟨2111858991004084135027831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2815811988005445513370441 2111858991004084135027831)
          ·
            refine ⟨3167788486506126202541747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111858991004084135027831 3167788486506126202541747)
            ·
              refine ⟨4751682729759189303812621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167788486506126202541747 4751682729759189303812621)
              ·
                refine ⟨1781881023659695988929733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4751682729759189303812621 1781881023659695988929733)
                ·
                  refine ⟨334102691936192997924325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781881023659695988929733 334102691936192997924325)
                  ·
                    rfl

theorem cell22_2927982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_2927982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2927982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2927982 prefixEnd_2927982 := by exact prefixLift 2927982
  have htrace : WordTrace (prefixWord ++ tailWord_2927982) baseStart_2927982 baseEnd_2927982 := by
    simpa [prefixWord, tailWord_2927982, baseEnd_2927982] using wordTrace_append hprefix tailTrace_2927982
  have hstable : (prefixWord ++ tailWord_2927982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2927982).length < 2 ^ (prefixWord ++ tailWord_2927982).sum := by decide
  have hdescent : baseEnd_2927982 < baseStart_2927982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2927982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928004 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 7]
def baseStart_2928004 : Nat := 118140960795 + 2928004 * 2 ^ 59
def prefixEnd_2928004 : Nat := 4983230072969 + 3 ^ 40 * 2928004 * 2
def baseEnd_2928004 : Nat := 334105202286059423240969

theorem tailTrace_2928004 : CollatzResearch.WordTrace tailWord_2928004 prefixEnd_2928004 334105202286059423240969 := by
  unfold tailWord_2928004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53396539642174523058119533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71195386189566030744159377 53396539642174523058119533)
  ·
    refine ⟨20023702365815446146794825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53396539642174523058119533 20023702365815446146794825)
    ·
      refine ⟨15017776774361584610096119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20023702365815446146794825 15017776774361584610096119)
      ·
        refine ⟨22526665161542376915144179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15017776774361584610096119 22526665161542376915144179)
        ·
          refine ⟨33789997742313565372716269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22526665161542376915144179 33789997742313565372716269)
          ·
            refine ⟨12671249153367587014768601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33789997742313565372716269 12671249153367587014768601)
            ·
              refine ⟨9503436865025690261076451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12671249153367587014768601 9503436865025690261076451)
              ·
                refine ⟨14255155297538535391614677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9503436865025690261076451 14255155297538535391614677)
                ·
                  refine ⟨334105202286059423240969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14255155297538535391614677 334105202286059423240969)
                  ·
                    rfl

theorem cell22_2928004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_2928004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928004 prefixEnd_2928004 := by exact prefixLift 2928004
  have htrace : WordTrace (prefixWord ++ tailWord_2928004) baseStart_2928004 baseEnd_2928004 := by
    simpa [prefixWord, tailWord_2928004, baseEnd_2928004] using wordTrace_append hprefix tailTrace_2928004
  have hstable : (prefixWord ++ tailWord_2928004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928004).length < 2 ^ (prefixWord ++ tailWord_2928004).sum := by decide
  have hdescent : baseEnd_2928004 < baseStart_2928004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928008 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 3, 3]
def baseStart_2928008 : Nat := 118140960795 + 2928008 * 2 ^ 59
def prefixEnd_2928008 : Nat := 4983230072969 + 3 ^ 40 * 2928008 * 2
def baseEnd_2928008 : Nat := 1002316976139923592622895

theorem tailTrace_2928008 : CollatzResearch.WordTrace tailWord_2928008 prefixEnd_2928008 1002316976139923592622895 := by
  unfold tailWord_2928008
  simp only [CollatzResearch.WordTrace]
  refine ⟨53396612588167277399692339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71195483450889703199589785 53396612588167277399692339)
  ·
    refine ⟨80094918882250916099538509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53396612588167277399692339 80094918882250916099538509)
    ·
      refine ⟨30035594580844093537326941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80094918882250916099538509 30035594580844093537326941)
      ·
        refine ⟨11263347967816535076497603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30035594580844093537326941 11263347967816535076497603)
        ·
          refine ⟨16895021951724802614746405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11263347967816535076497603 16895021951724802614746405)
          ·
            refine ⟨3167816615948400490264951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16895021951724802614746405 3167816615948400490264951)
            ·
              refine ⟨4751724923922600735397427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167816615948400490264951 4751724923922600735397427)
              ·
                refine ⟨7127587385883901103096141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751724923922600735397427 7127587385883901103096141)
                ·
                  refine ⟨2672845269706462913661053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7127587385883901103096141 2672845269706462913661053)
                  ·
                    refine ⟨1002316976139923592622895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672845269706462913661053 1002316976139923592622895)
                    ·
                      rfl

theorem cell22_2928008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_2928008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928008 prefixEnd_2928008 := by exact prefixLift 2928008
  have htrace : WordTrace (prefixWord ++ tailWord_2928008) baseStart_2928008 baseEnd_2928008 := by
    simpa [prefixWord, tailWord_2928008, baseEnd_2928008] using wordTrace_append hprefix tailTrace_2928008
  have hstable : (prefixWord ++ tailWord_2928008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928008).length < 2 ^ (prefixWord ++ tailWord_2928008).sum := by decide
  have hdescent : baseEnd_2928008 < baseStart_2928008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928021 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 5]
def baseStart_2928021 : Nat := 118140960795 + 2928021 * 2 ^ 59
def prefixEnd_2928021 : Nat := 4983230072969 + 3 ^ 40 * 2928021 * 2
def baseEnd_2928021 : Nat := 334107142101865297349285

theorem tailTrace_2928021 : CollatzResearch.WordTrace tailWord_2928021 prefixEnd_2928021 334107142101865297349285 := by
  unfold tailWord_2928021
  simp only [CollatzResearch.WordTrace]
  refine ⟨106793699325287458019607917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71195799550191638679738611 106793699325287458019607917)
  ·
    refine ⟨40047637246982796757352969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106793699325287458019607917 40047637246982796757352969)
    ·
      refine ⟨30035727935237097568014727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40047637246982796757352969 30035727935237097568014727)
      ·
        refine ⟨45053591902855646352022091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30035727935237097568014727 45053591902855646352022091)
        ·
          refine ⟨67580387854283469528033137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45053591902855646352022091 67580387854283469528033137)
          ·
            refine ⟨50685290890712602146024853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67580387854283469528033137 50685290890712602146024853)
            ·
              refine ⟨2375873010502153225594915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50685290890712602146024853 2375873010502153225594915)
              ·
                refine ⟨3563809515753229838392373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375873010502153225594915 3563809515753229838392373)
                ·
                  refine ⟨334107142101865297349285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3563809515753229838392373 334107142101865297349285)
                  ·
                    rfl

theorem cell22_2928021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_2928021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928021 prefixEnd_2928021 := by exact prefixLift 2928021
  have htrace : WordTrace (prefixWord ++ tailWord_2928021) baseStart_2928021 baseEnd_2928021 := by
    simpa [prefixWord, tailWord_2928021, baseEnd_2928021] using wordTrace_append hprefix tailTrace_2928021
  have hstable : (prefixWord ++ tailWord_2928021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928021).length < 2 ^ (prefixWord ++ tailWord_2928021).sum := by decide
  have hdescent : baseEnd_2928021 < baseStart_2928021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928079 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 4, 4]
def baseStart_2928079 : Nat := 118140960795 + 2928079 * 2 ^ 59
def prefixEnd_2928079 : Nat := 4983230072969 + 3 ^ 40 * 2928079 * 2
def baseEnd_2928079 : Nat := 1002341280890903074097677

theorem tailTrace_2928079 : CollatzResearch.WordTrace tailWord_2928079 prefixEnd_2928079 1002341280890903074097677 := by
  unfold tailWord_2928079
  simp only [CollatzResearch.WordTrace]
  refine ⟨106795814759077333925219291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71197209839384889283479527 106795814759077333925219291)
  ·
    refine ⟨160193722138616000887828937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106795814759077333925219291 160193722138616000887828937)
    ·
      refine ⟨120145291603962000665871703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160193722138616000887828937 120145291603962000665871703)
      ·
        refine ⟨180217937405943000998807555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120145291603962000665871703 180217937405943000998807555)
        ·
          refine ⟨270326906108914501498211333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180217937405943000998807555 270326906108914501498211333)
          ·
            refine ⟨50686294895421469030914625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270326906108914501498211333 50686294895421469030914625)
            ·
              refine ⟨38014721171566101773185969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50686294895421469030914625 38014721171566101773185969)
              ·
                refine ⟨28511040878674576329889477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38014721171566101773185969 28511040878674576329889477)
                ·
                  refine ⟨5345820164751483061854277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28511040878674576329889477 5345820164751483061854277)
                  ·
                    refine ⟨1002341280890903074097677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5345820164751483061854277 1002341280890903074097677)
                    ·
                      rfl

theorem cell22_2928079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_2928079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928079 prefixEnd_2928079 := by exact prefixLift 2928079
  have htrace : WordTrace (prefixWord ++ tailWord_2928079) baseStart_2928079 baseEnd_2928079 := by
    simpa [prefixWord, tailWord_2928079, baseEnd_2928079] using wordTrace_append hprefix tailTrace_2928079
  have hstable : (prefixWord ++ tailWord_2928079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928079).length < 2 ^ (prefixWord ++ tailWord_2928079).sum := by decide
  have hdescent : baseEnd_2928079 < baseStart_2928079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928124 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_2928124 : Nat := 118140960795 + 2928124 * 2 ^ 59
def prefixEnd_2928124 : Nat := 4983230072969 + 3 ^ 40 * 2928124 * 2
def baseEnd_2928124 : Nat := 1002356685310537956722539

theorem tailTrace_2928124 : CollatzResearch.WordTrace tailWord_2928124 prefixEnd_2928124 1002356685310537956722539 := by
  unfold tailWord_2928124
  simp only [CollatzResearch.WordTrace]
  refine ⟨53398728021957153305303713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71198304029276204407071617 53398728021957153305303713)
  ·
    refine ⟨40049046016467864978977785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53398728021957153305303713 40049046016467864978977785)
    ·
      refine ⟨30036784512350898734233339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40049046016467864978977785 30036784512350898734233339)
      ·
        refine ⟨45055176768526348101350009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30036784512350898734233339 45055176768526348101350009)
        ·
          refine ⟨33791382576394761076012507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45055176768526348101350009 33791382576394761076012507)
          ·
            refine ⟨50687073864592141614018761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33791382576394761076012507 50687073864592141614018761)
            ·
              refine ⟨38015305398444106210514071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50687073864592141614018761 38015305398444106210514071)
              ·
                refine ⟨57022958097666159315771107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38015305398444106210514071 57022958097666159315771107)
                ·
                  refine ⟨85534437146499238973656661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57022958097666159315771107 85534437146499238973656661)
                  ·
                    refine ⟨1002356685310537956722539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85534437146499238973656661 1002356685310537956722539)
                    ·
                      rfl

theorem cell22_2928124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_2928124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928124 prefixEnd_2928124 := by exact prefixLift 2928124
  have htrace : WordTrace (prefixWord ++ tailWord_2928124) baseStart_2928124 baseEnd_2928124 := by
    simpa [prefixWord, tailWord_2928124, baseEnd_2928124] using wordTrace_append hprefix tailTrace_2928124
  have hstable : (prefixWord ++ tailWord_2928124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928124).length < 2 ^ (prefixWord ++ tailWord_2928124).sum := by decide
  have hdescent : baseEnd_2928124 < baseStart_2928124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928132 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_2928132 : Nat := 118140960795 + 2928132 * 2 ^ 59
def prefixEnd_2928132 : Nat := 4983230072969 + 3 ^ 40 * 2928132 * 2
def baseEnd_2928132 : Nat := 1002359423874028602522515

theorem tailTrace_2928132 : CollatzResearch.WordTrace tailWord_2928132 prefixEnd_2928132 1002359423874028602522515 := by
  unfold tailWord_2928132
  simp only [CollatzResearch.WordTrace]
  refine ⟨53398873913942661988449325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71198498551923549317932433 53398873913942661988449325)
  ·
    refine ⟨20024577717728498245668497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53398873913942661988449325 20024577717728498245668497)
    ·
      refine ⟨15018433288296373684251373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20024577717728498245668497 15018433288296373684251373)
      ·
        refine ⟨5631912483111140131594265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15018433288296373684251373 5631912483111140131594265)
        ·
          refine ⟨4223934362333355098695699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5631912483111140131594265 4223934362333355098695699)
          ·
            refine ⟨6335901543500032648043549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223934362333355098695699 6335901543500032648043549)
            ·
              refine ⟨2375963078812512243016331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6335901543500032648043549 2375963078812512243016331)
              ·
                refine ⟨3563944618218768364524497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375963078812512243016331 3563944618218768364524497)
                ·
                  refine ⟨2672958463664076273393373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3563944618218768364524497 2672958463664076273393373)
                  ·
                    refine ⟨1002359423874028602522515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672958463664076273393373 1002359423874028602522515)
                    ·
                      rfl

theorem cell22_2928132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_2928132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928132 prefixEnd_2928132 := by exact prefixLift 2928132
  have htrace : WordTrace (prefixWord ++ tailWord_2928132) baseStart_2928132 baseEnd_2928132 := by
    simpa [prefixWord, tailWord_2928132, baseEnd_2928132] using wordTrace_append hprefix tailTrace_2928132
  have hstable : (prefixWord ++ tailWord_2928132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928132).length < 2 ^ (prefixWord ++ tailWord_2928132).sum := by decide
  have hdescent : baseEnd_2928132 < baseStart_2928132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928186 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_2928186 : Nat := 118140960795 + 2928186 * 2 ^ 59
def prefixEnd_2928186 : Nat := 4983230072969 + 3 ^ 40 * 2928186 * 2
def baseEnd_2928186 : Nat := 1002377909177590461672349

theorem tailTrace_2928186 : CollatzResearch.WordTrace tailWord_2928186 prefixEnd_2928186 1002377909177590461672349 := by
  unfold tailWord_2928186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26699929342422422799841103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71199811579793127466242941 26699929342422422799841103)
  ·
    refine ⟨40049894013633634199761655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26699929342422422799841103 40049894013633634199761655)
    ·
      refine ⟨60074841020450451299642483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40049894013633634199761655 60074841020450451299642483)
      ·
        refine ⟨90112261530675676949463725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60074841020450451299642483 90112261530675676949463725)
        ·
          refine ⟨33792098074003378856048897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90112261530675676949463725 33792098074003378856048897)
          ·
            refine ⟨25344073555502534142036673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33792098074003378856048897 25344073555502534142036673)
            ·
              refine ⟨19008055166626900606527505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25344073555502534142036673 19008055166626900606527505)
              ·
                refine ⟨14256041374970175454895629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19008055166626900606527505 14256041374970175454895629)
                ·
                  refine ⟨5346015515613815795585861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14256041374970175454895629 5346015515613815795585861)
                  ·
                    refine ⟨1002377909177590461672349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5346015515613815795585861 1002377909177590461672349)
                    ·
                      rfl

theorem cell22_2928186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_2928186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928186 prefixEnd_2928186 := by exact prefixLift 2928186
  have htrace : WordTrace (prefixWord ++ tailWord_2928186) baseStart_2928186 baseEnd_2928186 := by
    simpa [prefixWord, tailWord_2928186, baseEnd_2928186] using wordTrace_append hprefix tailTrace_2928186
  have hstable : (prefixWord ++ tailWord_2928186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928186).length < 2 ^ (prefixWord ++ tailWord_2928186).sum := by decide
  have hdescent : baseEnd_2928186 < baseStart_2928186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928233 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 2, 3]
def baseStart_2928233 : Nat := 118140960795 + 2928233 * 2 ^ 59
def prefixEnd_2928233 : Nat := 4983230072969 + 3 ^ 40 * 2928233 * 2
def baseEnd_2928233 : Nat := 1002393998238098005747205

theorem tailTrace_2928233 : CollatzResearch.WordTrace tailWord_2928233 prefixEnd_2928233 1002393998238098005747205 := by
  unfold tailWord_2928233
  simp only [CollatzResearch.WordTrace]
  refine ⟨106801431600519418226325353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71200954400346278817550235 106801431600519418226325353)
  ·
    refine ⟨80101073700389563669744015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106801431600519418226325353 80101073700389563669744015)
    ·
      refine ⟨120151610550584345504616023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80101073700389563669744015 120151610550584345504616023)
      ·
        refine ⟨180227415825876518256924035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120151610550584345504616023 180227415825876518256924035)
        ·
          refine ⟨270341123738814777385386053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180227415825876518256924035 270341123738814777385386053)
          ·
            refine ⟨50688960701027770759759885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270341123738814777385386053 50688960701027770759759885)
            ·
              refine ⟨19008360262885414034909957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50688960701027770759759885 19008360262885414034909957)
              ·
                refine ⟨3564067549291015131545617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19008360262885414034909957 3564067549291015131545617)
                ·
                  refine ⟨2673050661968261348659213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3564067549291015131545617 2673050661968261348659213)
                  ·
                    refine ⟨1002393998238098005747205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673050661968261348659213 1002393998238098005747205)
                    ·
                      rfl

theorem cell22_2928233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_2928233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928233 prefixEnd_2928233 := by exact prefixLift 2928233
  have htrace : WordTrace (prefixWord ++ tailWord_2928233) baseStart_2928233 baseEnd_2928233 := by
    simpa [prefixWord, tailWord_2928233, baseEnd_2928233] using wordTrace_append hprefix tailTrace_2928233
  have hstable : (prefixWord ++ tailWord_2928233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928233).length < 2 ^ (prefixWord ++ tailWord_2928233).sum := by decide
  have hdescent : baseEnd_2928233 < baseStart_2928233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928263 : List Nat := [1, 1, 4, 2, 1, 4, 3, 6]
def baseStart_2928263 : Nat := 118140960795 + 2928263 * 2 ^ 59
def prefixEnd_2928263 : Nat := 4983230072969 + 3 ^ 40 * 2928263 * 2
def baseEnd_2928263 : Nat := 111378251983465325277457

theorem tailTrace_2928263 : CollatzResearch.WordTrace tailWord_2928263 prefixEnd_2928263 111378251983465325277457 := by
  unfold tailWord_2928263
  simp only [CollatzResearch.WordTrace]
  refine ⟨106802525790410733349917443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71201683860273822233278295 106802525790410733349917443)
  ·
    refine ⟨160203788685616100024876165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106802525790410733349917443 160203788685616100024876165)
    ·
      refine ⟨30038210378553018754664281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160203788685616100024876165 30038210378553018754664281)
      ·
        refine ⟨22528657783914764065998211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30038210378553018754664281 22528657783914764065998211)
        ·
          refine ⟨33792986675872146098997317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22528657783914764065998211 33792986675872146098997317)
          ·
            refine ⟨6336185001726027393561997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33792986675872146098997317 6336185001726027393561997)
            ·
              refine ⟨2376069375647260272585749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6336185001726027393561997 2376069375647260272585749)
              ·
                refine ⟨111378251983465325277457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2376069375647260272585749 111378251983465325277457)
                ·
                  rfl

theorem cell22_2928263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 6].length) (baseStart_2928263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928263 prefixEnd_2928263 := by exact prefixLift 2928263
  have htrace : WordTrace (prefixWord ++ tailWord_2928263) baseStart_2928263 baseEnd_2928263 := by
    simpa [prefixWord, tailWord_2928263, baseEnd_2928263] using wordTrace_append hprefix tailTrace_2928263
  have hstable : (prefixWord ++ tailWord_2928263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928263).length < 2 ^ (prefixWord ++ tailWord_2928263).sum := by decide
  have hdescent : baseEnd_2928263 < baseStart_2928263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928284 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_2928284 : Nat := 118140960795 + 2928284 * 2 ^ 59
def prefixEnd_2928284 : Nat := 4983230072969 + 3 ^ 40 * 2928284 * 2
def baseEnd_2928284 : Nat := 1002411456580350872722049

theorem tailTrace_2928284 : CollatzResearch.WordTrace tailWord_2928284 prefixEnd_2928284 1002411456580350872722049 := by
  unfold tailWord_2928284
  simp only [CollatzResearch.WordTrace]
  refine ⟨53401645861667326968215953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71202194482223102624287937 53401645861667326968215953)
  ·
    refine ⟨40051234396250495226161965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53401645861667326968215953 40051234396250495226161965)
    ·
      refine ⟨15019212898593935709810737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40051234396250495226161965 15019212898593935709810737)
      ·
        refine ⟨11264409673945451782358053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15019212898593935709810737 11264409673945451782358053)
        ·
          refine ⟨2112076813864772209192135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11264409673945451782358053 2112076813864772209192135)
          ·
            refine ⟨3168115220797158313788203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112076813864772209192135 3168115220797158313788203)
            ·
              refine ⟨4752172831195737470682305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168115220797158313788203 4752172831195737470682305)
              ·
                refine ⟨3564129623396803103011729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4752172831195737470682305 3564129623396803103011729)
                ·
                  refine ⟨2673097217547602327258797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3564129623396803103011729 2673097217547602327258797)
                  ·
                    refine ⟨1002411456580350872722049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673097217547602327258797 1002411456580350872722049)
                    ·
                      rfl

theorem cell22_2928284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_2928284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928284 prefixEnd_2928284 := by exact prefixLift 2928284
  have htrace : WordTrace (prefixWord ++ tailWord_2928284) baseStart_2928284 baseEnd_2928284 := by
    simpa [prefixWord, tailWord_2928284, baseEnd_2928284] using wordTrace_append hprefix tailTrace_2928284
  have hstable : (prefixWord ++ tailWord_2928284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928284).length < 2 ^ (prefixWord ++ tailWord_2928284).sum := by decide
  have hdescent : baseEnd_2928284 < baseStart_2928284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928291 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 7]
def baseStart_2928291 : Nat := 118140960795 + 2928291 * 2 ^ 59
def prefixEnd_2928291 : Nat := 4983230072969 + 3 ^ 40 * 2928291 * 2
def baseEnd_2928291 : Nat := 334137950941135062599009

theorem tailTrace_2928291 : CollatzResearch.WordTrace tailWord_2928291 prefixEnd_2928291 334137950941135062599009 := by
  unfold tailWord_2928291
  simp only [CollatzResearch.WordTrace]
  refine ⟨106803547034309294131936727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71202364689539529421291151 106803547034309294131936727)
  ·
    refine ⟨160205320551463941197905091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106803547034309294131936727 160205320551463941197905091)
    ·
      refine ⟨240307980827195911796857637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160205320551463941197905091 240307980827195911796857637)
      ·
        refine ⟨45057746405099233461910807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240307980827195911796857637 45057746405099233461910807)
        ·
          refine ⟨67586619607648850192866211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45057746405099233461910807 67586619607648850192866211)
          ·
            refine ⟨101379929411473275289299317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67586619607648850192866211 101379929411473275289299317)
            ·
              refine ⟨9504368382325619558371811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101379929411473275289299317 9504368382325619558371811)
              ·
                refine ⟨14256552573488429337557717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9504368382325619558371811 14256552573488429337557717)
                ·
                  refine ⟨334137950941135062599009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14256552573488429337557717 334137950941135062599009)
                  ·
                    rfl

theorem cell22_2928291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 7].length) (baseStart_2928291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928291 prefixEnd_2928291 := by exact prefixLift 2928291
  have htrace : WordTrace (prefixWord ++ tailWord_2928291) baseStart_2928291 baseEnd_2928291 := by
    simpa [prefixWord, tailWord_2928291, baseEnd_2928291] using wordTrace_append hprefix tailTrace_2928291
  have hstable : (prefixWord ++ tailWord_2928291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928291).length < 2 ^ (prefixWord ++ tailWord_2928291).sum := by decide
  have hdescent : baseEnd_2928291 < baseStart_2928291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928359 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 5]
def baseStart_2928359 : Nat := 118140960795 + 2928359 * 2 ^ 59
def prefixEnd_2928359 : Nat := 4983230072969 + 3 ^ 40 * 2928359 * 2
def baseEnd_2928359 : Nat := 334145710204358559032273

theorem tailTrace_2928359 : CollatzResearch.WordTrace tailWord_2928359 prefixEnd_2928359 334145710204358559032273 := by
  unfold tailWord_2928359
  simp only [CollatzResearch.WordTrace]
  refine ⟨106806027198062941745412131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71204018132041961163608087 106806027198062941745412131)
  ·
    refine ⟨160209040797094412618118197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106806027198062941745412131 160209040797094412618118197)
    ·
      refine ⟨15019597574727601182948581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160209040797094412618118197 15019597574727601182948581)
      ·
        refine ⟨2816174545261425221802859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15019597574727601182948581 2816174545261425221802859)
        ·
          refine ⟨4224261817892137832704289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816174545261425221802859 4224261817892137832704289)
          ·
            refine ⟨3168196363419103374528217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4224261817892137832704289 3168196363419103374528217)
            ·
              refine ⟨2376147272564327530896163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168196363419103374528217 2376147272564327530896163)
              ·
                refine ⟨3564220908846491296344245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376147272564327530896163 3564220908846491296344245)
                ·
                  refine ⟨334145710204358559032273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3564220908846491296344245 334145710204358559032273)
                  ·
                    rfl

theorem cell22_2928359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 5].length) (baseStart_2928359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928359 prefixEnd_2928359 := by exact prefixLift 2928359
  have htrace : WordTrace (prefixWord ++ tailWord_2928359) baseStart_2928359 baseEnd_2928359 := by
    simpa [prefixWord, tailWord_2928359, baseEnd_2928359] using wordTrace_append hprefix tailTrace_2928359
  have hstable : (prefixWord ++ tailWord_2928359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928359).length < 2 ^ (prefixWord ++ tailWord_2928359).sum := by decide
  have hdescent : baseEnd_2928359 < baseStart_2928359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928368 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 6, 3]
def baseStart_2928368 : Nat := 118140960795 + 2928368 * 2 ^ 59
def prefixEnd_2928368 : Nat := 4983230072969 + 3 ^ 40 * 2928368 * 2
def baseEnd_2928368 : Nat := 1002440211497002653621791

theorem tailTrace_2928368 : CollatzResearch.WordTrace tailWord_2928368 prefixEnd_2928368 1002440211497002653621791 := by
  unfold tailWord_2928368
  simp only [CollatzResearch.WordTrace]
  refine ⟨53403177727515168141244879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71204236970020224188326505 53403177727515168141244879)
  ·
    refine ⟨80104766591272752211867319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53403177727515168141244879 80104766591272752211867319)
    ·
      refine ⟨120157149886909128317800979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80104766591272752211867319 120157149886909128317800979)
      ·
        refine ⟨180235724830363692476701469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120157149886909128317800979 180235724830363692476701469)
        ·
          refine ⟨67588396811386384678763051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180235724830363692476701469 67588396811386384678763051)
          ·
            refine ⟨101382595217079577018144577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67588396811386384678763051 101382595217079577018144577)
            ·
              refine ⟨76036946412809682763608433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101382595217079577018144577 76036946412809682763608433)
              ·
                refine ⟨57027709809607262072706325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76036946412809682763608433 57027709809607262072706325)
                ·
                  refine ⟨2673173897325340409658109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57027709809607262072706325 2673173897325340409658109)
                  ·
                    refine ⟨1002440211497002653621791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673173897325340409658109 1002440211497002653621791)
                    ·
                      rfl

theorem cell22_2928368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_2928368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928368 prefixEnd_2928368 := by exact prefixLift 2928368
  have htrace : WordTrace (prefixWord ++ tailWord_2928368) baseStart_2928368 baseEnd_2928368 := by
    simpa [prefixWord, tailWord_2928368, baseEnd_2928368] using wordTrace_append hprefix tailTrace_2928368
  have hstable : (prefixWord ++ tailWord_2928368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928368).length < 2 ^ (prefixWord ++ tailWord_2928368).sum := by decide
  have hdescent : baseEnd_2928368 < baseStart_2928368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928383 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 2, 4]
def baseStart_2928383 : Nat := 118140960795 + 2928383 * 2 ^ 59
def prefixEnd_2928383 : Nat := 4983230072969 + 3 ^ 40 * 2928383 * 2
def baseEnd_2928383 : Nat := 1002445346303547614496745

theorem tailTrace_2928383 : CollatzResearch.WordTrace tailWord_2928383 prefixEnd_2928383 1002445346303547614496745 := by
  unfold tailWord_2928383
  simp only [CollatzResearch.WordTrace]
  refine ⟨106806902549975993844285803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71204601699983995896190535 106806902549975993844285803)
  ·
    refine ⟨160210353824963990766428705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106806902549975993844285803 160210353824963990766428705)
    ·
      refine ⟨120157765368722993074821529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160210353824963990766428705 120157765368722993074821529)
      ·
        refine ⟨90118324026542244806116147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120157765368722993074821529 90118324026542244806116147)
        ·
          refine ⟨135177486039813367209174221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90118324026542244806116147 135177486039813367209174221)
          ·
            refine ⟨50691557264930012703440333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135177486039813367209174221 50691557264930012703440333)
            ·
              refine ⟨19009333974348754763790125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50691557264930012703440333 19009333974348754763790125)
              ·
                refine ⟨7128500240380783036421297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19009333974348754763790125 7128500240380783036421297)
                ·
                  refine ⟨5346375180285587277315973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7128500240380783036421297 5346375180285587277315973)
                  ·
                    refine ⟨1002445346303547614496745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5346375180285587277315973 1002445346303547614496745)
                    ·
                      rfl

theorem cell22_2928383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_2928383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928383 prefixEnd_2928383 := by exact prefixLift 2928383
  have htrace : WordTrace (prefixWord ++ tailWord_2928383) baseStart_2928383 baseEnd_2928383 := by
    simpa [prefixWord, tailWord_2928383, baseEnd_2928383] using wordTrace_append hprefix tailTrace_2928383
  have hstable : (prefixWord ++ tailWord_2928383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928383).length < 2 ^ (prefixWord ++ tailWord_2928383).sum := by decide
  have hdescent : baseEnd_2928383 < baseStart_2928383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928397 : List Nat := [1, 7, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2928397 : Nat := 118140960795 + 2928397 * 2 ^ 59
def prefixEnd_2928397 : Nat := 4983230072969 + 3 ^ 40 * 2928397 * 2
def baseEnd_2928397 : Nat := 1002450138789656244646703

theorem tailTrace_2928397 : CollatzResearch.WordTrace tailWord_2928397 prefixEnd_2928397 1002450138789656244646703 := by
  unfold tailWord_2928397
  simp only [CollatzResearch.WordTrace]
  refine ⟨106807413171925274235295445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71204942114616849490196963 106807413171925274235295445)
  ·
    refine ⟨2503298746216998614889737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 106807413171925274235295445 2503298746216998614889737)
    ·
      refine ⟨1877474059662748961167303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2503298746216998614889737 1877474059662748961167303)
      ·
        refine ⟨2816211089494123441750955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877474059662748961167303 2816211089494123441750955)
        ·
          refine ⟨4224316634241185162626433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816211089494123441750955 4224316634241185162626433)
          ·
            refine ⟨3168237475680888871969825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4224316634241185162626433 3168237475680888871969825)
            ·
              refine ⟨2376178106760666653977369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168237475680888871969825 2376178106760666653977369)
              ·
                refine ⟨1782133580070499990483027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376178106760666653977369 1782133580070499990483027)
                ·
                  refine ⟨2673200370105749985724541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782133580070499990483027 2673200370105749985724541)
                  ·
                    refine ⟨1002450138789656244646703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673200370105749985724541 1002450138789656244646703)
                    ·
                      rfl

theorem cell22_2928397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2928397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928397 prefixEnd_2928397 := by exact prefixLift 2928397
  have htrace : WordTrace (prefixWord ++ tailWord_2928397) baseStart_2928397 baseEnd_2928397 := by
    simpa [prefixWord, tailWord_2928397, baseEnd_2928397] using wordTrace_append hprefix tailTrace_2928397
  have hstable : (prefixWord ++ tailWord_2928397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928397).length < 2 ^ (prefixWord ++ tailWord_2928397).sum := by decide
  have hdescent : baseEnd_2928397 < baseStart_2928397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928458 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_2928458 : Nat := 118140960795 + 2928458 * 2 ^ 59
def prefixEnd_2928458 : Nat := 4983230072969 + 3 ^ 40 * 2928458 * 2
def baseEnd_2928458 : Nat := 1002471020336272418871515

theorem tailTrace_2928458 : CollatzResearch.WordTrace tailWord_2928458 prefixEnd_2928458 1002471020336272418871515 := by
  unfold tailWord_2928458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26702409506176070413316507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71206425349802854435510685 26702409506176070413316507)
  ·
    refine ⟨40053614259264105619974761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26702409506176070413316507 40053614259264105619974761)
    ·
      refine ⟨30040210694448079214981071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40053614259264105619974761 30040210694448079214981071)
      ·
        refine ⟨45060316041672118822471607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30040210694448079214981071 45060316041672118822471607)
        ·
          refine ⟨67590474062508178233707411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45060316041672118822471607 67590474062508178233707411)
          ·
            refine ⟨101385711093762267350561117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67590474062508178233707411 101385711093762267350561117)
            ·
              refine ⟨38019641660160850256460419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101385711093762267350561117 38019641660160850256460419)
              ·
                refine ⟨57029462490241275384690629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38019641660160850256460419 57029462490241275384690629)
                ·
                  refine ⟨10693024216920239134629493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57029462490241275384690629 10693024216920239134629493)
                  ·
                    refine ⟨1002471020336272418871515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10693024216920239134629493 1002471020336272418871515)
                    ·
                      rfl

theorem cell22_2928458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_2928458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928458 prefixEnd_2928458 := by exact prefixLift 2928458
  have htrace : WordTrace (prefixWord ++ tailWord_2928458) baseStart_2928458 baseEnd_2928458 := by
    simpa [prefixWord, tailWord_2928458, baseEnd_2928458] using wordTrace_append hprefix tailTrace_2928458
  have hstable : (prefixWord ++ tailWord_2928458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928458).length < 2 ^ (prefixWord ++ tailWord_2928458).sum := by decide
  have hdescent : baseEnd_2928458 < baseStart_2928458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928460 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 7]
def baseStart_2928460 : Nat := 118140960795 + 2928460 * 2 ^ 59
def prefixEnd_2928460 : Nat := 4983230072969 + 3 ^ 40 * 2928460 * 2
def baseEnd_2928460 : Nat := 334157234992381693440503

theorem tailTrace_2928460 : CollatzResearch.WordTrace tailWord_2928460 prefixEnd_2928460 334157234992381693440503 := by
  unfold tailWord_2928460
  simp only [CollatzResearch.WordTrace]
  refine ⟨53404855485348517997419417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71206473980464690663225889 53404855485348517997419417)
  ·
    refine ⟨40053641614011388498064563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53404855485348517997419417 40053641614011388498064563)
    ·
      refine ⟨60080462421017082747096845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40053641614011388498064563 60080462421017082747096845)
      ·
        refine ⟨22530173407881406030161317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60080462421017082747096845 22530173407881406030161317)
        ·
          refine ⟨4224407513977763630655247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22530173407881406030161317 4224407513977763630655247)
          ·
            refine ⟨6336611270966645445982871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224407513977763630655247 6336611270966645445982871)
            ·
              refine ⟨9504916906449968168974307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6336611270966645445982871 9504916906449968168974307)
              ·
                refine ⟨14257375359674952253461461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9504916906449968168974307 14257375359674952253461461)
                ·
                  refine ⟨334157234992381693440503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14257375359674952253461461 334157234992381693440503)
                  ·
                    rfl

theorem cell22_2928460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_2928460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928460 prefixEnd_2928460 := by exact prefixLift 2928460
  have htrace : WordTrace (prefixWord ++ tailWord_2928460) baseStart_2928460 baseEnd_2928460 := by
    simpa [prefixWord, tailWord_2928460, baseEnd_2928460] using wordTrace_append hprefix tailTrace_2928460
  have hstable : (prefixWord ++ tailWord_2928460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928460).length < 2 ^ (prefixWord ++ tailWord_2928460).sum := by decide
  have hdescent : baseEnd_2928460 < baseStart_2928460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928715 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 2, 6]
def baseStart_2928715 : Nat := 118140960795 + 2928715 * 2 ^ 59
def prefixEnd_2928715 : Nat := 4983230072969 + 3 ^ 40 * 2928715 * 2
def baseEnd_2928715 : Nat := 1002558996688409415195727

theorem tailTrace_2928715 : CollatzResearch.WordTrace tailWord_2928715 prefixEnd_2928715 1002558996688409415195727 := by
  unfold tailWord_2928715
  simp only [CollatzResearch.WordTrace]
  refine ⟨106819011584773214545371599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71212674389848809696914399 106819011584773214545371599)
  ·
    refine ⟨160228517377159821818057399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106819011584773214545371599 160228517377159821818057399)
    ·
      refine ⟨240342776065739732727086099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160228517377159821818057399 240342776065739732727086099)
      ·
        refine ⟨360514164098609599090629149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240342776065739732727086099 360514164098609599090629149)
        ·
          refine ⟨135192811536978599658985931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360514164098609599090629149 135192811536978599658985931)
          ·
            refine ⟨202789217305467899488478897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135192811536978599658985931 202789217305467899488478897)
            ·
              refine ⟨152091912979100924616359173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202789217305467899488478897 152091912979100924616359173)
              ·
                refine ⟨28517233683581423365567345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152091912979100924616359173 28517233683581423365567345)
                ·
                  refine ⟨21387925262686067524175509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28517233683581423365567345 21387925262686067524175509)
                  ·
                    refine ⟨1002558996688409415195727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21387925262686067524175509 1002558996688409415195727)
                    ·
                      rfl

theorem cell22_2928715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_2928715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928715 prefixEnd_2928715 := by exact prefixLift 2928715
  have htrace : WordTrace (prefixWord ++ tailWord_2928715) baseStart_2928715 baseEnd_2928715 := by
    simpa [prefixWord, tailWord_2928715, baseEnd_2928715] using wordTrace_append hprefix tailTrace_2928715
  have hstable : (prefixWord ++ tailWord_2928715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928715).length < 2 ^ (prefixWord ++ tailWord_2928715).sum := by decide
  have hdescent : baseEnd_2928715 < baseStart_2928715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928751 : List Nat := [1, 1, 2, 1, 3, 5, 1, 4, 1, 3]
def baseStart_2928751 : Nat := 118140960795 + 2928751 * 2 ^ 59
def prefixEnd_2928751 : Nat := 4983230072969 + 3 ^ 40 * 2928751 * 2
def baseEnd_2928751 : Nat := 1002571320224117321295617

theorem tailTrace_2928751 : CollatzResearch.WordTrace tailWord_2928751 prefixEnd_2928751 1002571320224117321295617 := by
  unfold tailWord_2928751
  simp only [CollatzResearch.WordTrace]
  refine ⟨106820324612642792693682107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71213549741761861795788071 106820324612642792693682107)
  ·
    refine ⟨160230486918964189040523161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106820324612642792693682107 160230486918964189040523161)
    ·
      refine ⟨120172865189223141780392371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160230486918964189040523161 120172865189223141780392371)
      ·
        refine ⟨180259297783834712670588557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120172865189223141780392371 180259297783834712670588557)
        ·
          refine ⟨67597236668938017251470709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180259297783834712670588557 67597236668938017251470709)
          ·
            refine ⟨6337240937712939117325379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67597236668938017251470709 6337240937712939117325379)
            ·
              refine ⟨9505861406569408675988069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337240937712939117325379 9505861406569408675988069)
              ·
                refine ⟨1782349013731764126747763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9505861406569408675988069 1782349013731764126747763)
                ·
                  refine ⟨2673523520597646190121645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782349013731764126747763 2673523520597646190121645)
                  ·
                    refine ⟨1002571320224117321295617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673523520597646190121645 1002571320224117321295617)
                    ·
                      rfl

theorem cell22_2928751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 3].length) (baseStart_2928751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928751 prefixEnd_2928751 := by exact prefixLift 2928751
  have htrace : WordTrace (prefixWord ++ tailWord_2928751) baseStart_2928751 baseEnd_2928751 := by
    simpa [prefixWord, tailWord_2928751, baseEnd_2928751] using wordTrace_append hprefix tailTrace_2928751
  have hstable : (prefixWord ++ tailWord_2928751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928751).length < 2 ^ (prefixWord ++ tailWord_2928751).sum := by decide
  have hdescent : baseEnd_2928751 < baseStart_2928751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928777 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_2928777 : Nat := 118140960795 + 2928777 * 2 ^ 59
def prefixEnd_2928777 : Nat := 4983230072969 + 3 ^ 40 * 2928777 * 2
def baseEnd_2928777 : Nat := 1002580220555461920145537

theorem tailTrace_2928777 : CollatzResearch.WordTrace tailWord_2928777 prefixEnd_2928777 1002580220555461920145537 := by
  unfold tailWord_2928777
  simp only [CollatzResearch.WordTrace]
  refine ⟨106821272910548599134128585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71214181940365732756085723 106821272910548599134128585)
  ·
    refine ⟨80115954682911449350596439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106821272910548599134128585 80115954682911449350596439)
    ·
      refine ⟨120173932024367174025894659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80115954682911449350596439 120173932024367174025894659)
      ·
        refine ⟨180260898036550761038841989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120173932024367174025894659 180260898036550761038841989)
        ·
          refine ⟨33798918381853267694782873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180260898036550761038841989 33798918381853267694782873)
          ·
            refine ⟨25349188786389950771087155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33798918381853267694782873 25349188786389950771087155)
            ·
              refine ⟨38023783179584926156630733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25349188786389950771087155 38023783179584926156630733)
              ·
                refine ⟨14258918692344347308736525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38023783179584926156630733 14258918692344347308736525)
                ·
                  refine ⟨5347094509629130240776197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14258918692344347308736525 5347094509629130240776197)
                  ·
                    refine ⟨1002580220555461920145537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5347094509629130240776197 1002580220555461920145537)
                    ·
                      rfl

theorem cell22_2928777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_2928777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928777 prefixEnd_2928777 := by exact prefixLift 2928777
  have htrace : WordTrace (prefixWord ++ tailWord_2928777) baseStart_2928777 baseEnd_2928777 := by
    simpa [prefixWord, tailWord_2928777, baseEnd_2928777] using wordTrace_append hprefix tailTrace_2928777
  have hstable : (prefixWord ++ tailWord_2928777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928777).length < 2 ^ (prefixWord ++ tailWord_2928777).sum := by decide
  have hdescent : baseEnd_2928777 < baseStart_2928777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928798 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2928798 : Nat := 118140960795 + 2928798 * 2 ^ 59
def prefixEnd_2928798 : Nat := 4983230072969 + 3 ^ 40 * 2928798 * 2
def baseEnd_2928798 : Nat := 334195803094874955123491

theorem tailTrace_2928798 : CollatzResearch.WordTrace tailWord_2928798 prefixEnd_2928798 334195803094874955123491 := by
  unfold tailWord_2928798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13352754855434064965080381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71214692562315013147095365 13352754855434064965080381)
  ·
    refine ⟨5007283070787774361905143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13352754855434064965080381 5007283070787774361905143)
    ·
      refine ⟨7510924606181661542857715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5007283070787774361905143 7510924606181661542857715)
      ·
        refine ⟨11266386909272492314286573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7510924606181661542857715 11266386909272492314286573)
        ·
          refine ⟨4224895090977184617857465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11266386909272492314286573 4224895090977184617857465)
          ·
            refine ⟨3168671318232888463393099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4224895090977184617857465 3168671318232888463393099)
            ·
              refine ⟨4753006977349332695089649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168671318232888463393099 4753006977349332695089649)
              ·
                refine ⟨3564755233011999521317237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4753006977349332695089649 3564755233011999521317237)
                ·
                  refine ⟨334195803094874955123491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3564755233011999521317237 334195803094874955123491)
                  ·
                    rfl

theorem cell22_2928798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2928798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928798 prefixEnd_2928798 := by exact prefixLift 2928798
  have htrace : WordTrace (prefixWord ++ tailWord_2928798) baseStart_2928798 baseEnd_2928798 := by
    simpa [prefixWord, tailWord_2928798, baseEnd_2928798] using wordTrace_append hprefix tailTrace_2928798
  have hstable : (prefixWord ++ tailWord_2928798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928798).length < 2 ^ (prefixWord ++ tailWord_2928798).sum := by decide
  have hdescent : baseEnd_2928798 < baseStart_2928798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928860 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 6]
def baseStart_2928860 : Nat := 118140960795 + 2928860 * 2 ^ 59
def prefixEnd_2928860 : Nat := 4983230072969 + 3 ^ 40 * 2928860 * 2
def baseEnd_2928860 : Nat := 334202877717225790106761

theorem tailTrace_2928860 : CollatzResearch.WordTrace tailWord_2928860 prefixEnd_2928860 334202877717225790106761 := by
  unfold tailWord_2928860
  simp only [CollatzResearch.WordTrace]
  refine ⟨53412150084623952154700017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71216200112831936206266689 53412150084623952154700017)
  ·
    refine ⟨40059112563467964116025013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53412150084623952154700017 40059112563467964116025013)
    ·
      refine ⟨3755541802825121635877345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40059112563467964116025013 3755541802825121635877345)
      ·
        refine ⟨2816656352118841226908009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3755541802825121635877345 2816656352118841226908009)
        ·
          refine ⟨2112492264089130920181007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2816656352118841226908009 2112492264089130920181007)
          ·
            refine ⟨3168738396133696380271511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112492264089130920181007 3168738396133696380271511)
            ·
              refine ⟨4753107594200544570407267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168738396133696380271511 4753107594200544570407267)
              ·
                refine ⟨7129661391300816855610901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753107594200544570407267 7129661391300816855610901)
                ·
                  refine ⟨334202877717225790106761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7129661391300816855610901 334202877717225790106761)
                  ·
                    rfl

theorem cell22_2928860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_2928860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928860 prefixEnd_2928860 := by exact prefixLift 2928860
  have htrace : WordTrace (prefixWord ++ tailWord_2928860) baseStart_2928860 baseEnd_2928860 := by
    simpa [prefixWord, tailWord_2928860, baseEnd_2928860] using wordTrace_append hprefix tailTrace_2928860
  have hstable : (prefixWord ++ tailWord_2928860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928860).length < 2 ^ (prefixWord ++ tailWord_2928860).sum := by decide
  have hdescent : baseEnd_2928860 < baseStart_2928860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928886 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_2928886 : Nat := 118140960795 + 2928886 * 2 ^ 59
def prefixEnd_2928886 : Nat := 4983230072969 + 3 ^ 40 * 2928886 * 2
def baseEnd_2928886 : Nat := 1002617533483021969170203

theorem tailTrace_2928886 : CollatzResearch.WordTrace tailWord_2928886 prefixEnd_2928886 1002617533483021969170203 := by
  unfold tailWord_2928886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676578029197106921865407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71216832311435807166564341 6676578029197106921865407)
  ·
    refine ⟨10014867043795660382798111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6676578029197106921865407 10014867043795660382798111)
    ·
      refine ⟨15022300565693490574197167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10014867043795660382798111 15022300565693490574197167)
      ·
        refine ⟨22533450848540235861295751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15022300565693490574197167 22533450848540235861295751)
        ·
          refine ⟨33800176272810353791943627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22533450848540235861295751 33800176272810353791943627)
          ·
            refine ⟨50700264409215530687915441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33800176272810353791943627 50700264409215530687915441)
            ·
              refine ⟨38025198306911648015936581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50700264409215530687915441 38025198306911648015936581)
              ·
                refine ⟨7129724682545934002988109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38025198306911648015936581 7129724682545934002988109)
                ·
                  refine ⟨2673646755954725251120541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7129724682545934002988109 2673646755954725251120541)
                  ·
                    refine ⟨1002617533483021969170203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673646755954725251120541 1002617533483021969170203)
                    ·
                      rfl

theorem cell22_2928886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_2928886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928886 prefixEnd_2928886 := by exact prefixLift 2928886
  have htrace : WordTrace (prefixWord ++ tailWord_2928886) baseStart_2928886 baseEnd_2928886 := by
    simpa [prefixWord, tailWord_2928886, baseEnd_2928886] using wordTrace_append hprefix tailTrace_2928886
  have hstable : (prefixWord ++ tailWord_2928886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928886).length < 2 ^ (prefixWord ++ tailWord_2928886).sum := by decide
  have hdescent : baseEnd_2928886 < baseStart_2928886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928929 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_2928929 : Nat := 118140960795 + 2928929 * 2 ^ 59
def prefixEnd_2928929 : Nat := 4983230072969 + 3 ^ 40 * 2928929 * 2
def baseEnd_2928929 : Nat := 1002632253261784190345071

theorem tailTrace_2928929 : CollatzResearch.WordTrace tailWord_2928929 prefixEnd_2928929 1002632253261784190345071 := by
  unfold tailWord_2928929
  simp only [CollatzResearch.WordTrace]
  refine ⟨106826816805997929093661841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71217877870665286062441227 106826816805997929093661841)
  ·
    refine ⟨80120112604498446820246381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106826816805997929093661841 80120112604498446820246381)
    ·
      refine ⟨30045042226686917557592393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80120112604498446820246381 30045042226686917557592393)
      ·
        refine ⟨22533781670015188168194295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30045042226686917557592393 22533781670015188168194295)
        ·
          refine ⟨33800672505022782252291443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22533781670015188168194295 33800672505022782252291443)
          ·
            refine ⟨50701008757534173378437165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33800672505022782252291443 50701008757534173378437165)
            ·
              refine ⟨19012878284075315016913937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50701008757534173378437165 19012878284075315016913937)
              ·
                refine ⟨14259658713056486262685453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19012878284075315016913937 14259658713056486262685453)
                ·
                  refine ⟨5347372017396182348507045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14259658713056486262685453 5347372017396182348507045)
                  ·
                    refine ⟨1002632253261784190345071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5347372017396182348507045 1002632253261784190345071)
                    ·
                      rfl

theorem cell22_2928929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_2928929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928929 prefixEnd_2928929 := by exact prefixLift 2928929
  have htrace : WordTrace (prefixWord ++ tailWord_2928929) baseStart_2928929 baseEnd_2928929 := by
    simpa [prefixWord, tailWord_2928929, baseEnd_2928929] using wordTrace_append hprefix tailTrace_2928929
  have hstable : (prefixWord ++ tailWord_2928929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928929).length < 2 ^ (prefixWord ++ tailWord_2928929).sum := by decide
  have hdescent : baseEnd_2928929 < baseStart_2928929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928959 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 1, 5]
def baseStart_2928959 : Nat := 118140960795 + 2928959 * 2 ^ 59
def prefixEnd_2928959 : Nat := 4983230072969 + 3 ^ 40 * 2928959 * 2
def baseEnd_2928959 : Nat := 1002642522874874112094979

theorem tailTrace_2928959 : CollatzResearch.WordTrace tailWord_2928959 prefixEnd_2928959 1002642522874874112094979 := by
  unfold tailWord_2928959
  simp only [CollatzResearch.WordTrace]
  refine ⟨106827910995889244217253931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71218607330592829478169287 106827910995889244217253931)
  ·
    refine ⟨160241866493833866325880897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106827910995889244217253931 160241866493833866325880897)
    ·
      refine ⟨120181399870375399744410673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160241866493833866325880897 120181399870375399744410673)
      ·
        refine ⟨90136049902781549808308005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120181399870375399744410673 90136049902781549808308005)
        ·
          refine ⟨16900509356771540589057751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90136049902781549808308005 16900509356771540589057751)
          ·
            refine ⟨25350764035157310883586627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16900509356771540589057751 25350764035157310883586627)
            ·
              refine ⟨38026146052735966325379941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25350764035157310883586627 38026146052735966325379941)
              ·
                refine ⟨7129902384887993686008739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38026146052735966325379941 7129902384887993686008739)
                ·
                  refine ⟨10694853577331990529013109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7129902384887993686008739 10694853577331990529013109)
                  ·
                    refine ⟨1002642522874874112094979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10694853577331990529013109 1002642522874874112094979)
                    ·
                      rfl

theorem cell22_2928959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_2928959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928959 prefixEnd_2928959 := by exact prefixLift 2928959
  have htrace : WordTrace (prefixWord ++ tailWord_2928959) baseStart_2928959 baseEnd_2928959 := by
    simpa [prefixWord, tailWord_2928959, baseEnd_2928959] using wordTrace_append hprefix tailTrace_2928959
  have hstable : (prefixWord ++ tailWord_2928959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928959).length < 2 ^ (prefixWord ++ tailWord_2928959).sum := by decide
  have hdescent : baseEnd_2928959 < baseStart_2928959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928976 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 4, 3]
def baseStart_2928976 : Nat := 118140960795 + 2928976 * 2 ^ 59
def prefixEnd_2928976 : Nat := 4983230072969 + 3 ^ 40 * 2928976 * 2
def baseEnd_2928976 : Nat := 1002648342322291734419927

theorem tailTrace_2928976 : CollatzResearch.WordTrace tailWord_2928976 prefixEnd_2928976 1002648342322291734419927 := by
  unfold tailWord_2928976
  simp only [CollatzResearch.WordTrace]
  refine ⟨53414265518413828060311391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71219020691218437413748521 53414265518413828060311391)
  ·
    refine ⟨80121398277620742090467087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53414265518413828060311391 80121398277620742090467087)
    ·
      refine ⟨120182097416431113135700631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80121398277620742090467087 120182097416431113135700631)
      ·
        refine ⟨180273146124646669703550947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120182097416431113135700631 180273146124646669703550947)
        ·
          refine ⟨270409719186970004555326421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180273146124646669703550947 270409719186970004555326421)
          ·
            refine ⟨6337727793444609481765463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 270409719186970004555326421 6337727793444609481765463)
            ·
              refine ⟨9506591690166914222648195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337727793444609481765463 9506591690166914222648195)
              ·
                refine ⟨14259887535250371333972293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9506591690166914222648195 14259887535250371333972293)
                ·
                  refine ⟨2673728912859444625119805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14259887535250371333972293 2673728912859444625119805)
                  ·
                    refine ⟨1002648342322291734419927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673728912859444625119805 1002648342322291734419927)
                    ·
                      rfl

theorem cell22_2928976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_2928976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2928976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2928976 prefixEnd_2928976 := by exact prefixLift 2928976
  have htrace : WordTrace (prefixWord ++ tailWord_2928976) baseStart_2928976 baseEnd_2928976 := by
    simpa [prefixWord, tailWord_2928976, baseEnd_2928976] using wordTrace_append hprefix tailTrace_2928976
  have hstable : (prefixWord ++ tailWord_2928976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928976).length < 2 ^ (prefixWord ++ tailWord_2928976).sum := by decide
  have hdescent : baseEnd_2928976 < baseStart_2928976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929044 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2929044 : Nat := 118140960795 + 2929044 * 2 ^ 59
def prefixEnd_2929044 : Nat := 4983230072969 + 3 ^ 40 * 2929044 * 2
def baseEnd_2929044 : Nat := 1002671620111962223719719

theorem tailTrace_2929044 : CollatzResearch.WordTrace tailWord_2929044 prefixEnd_2929044 1002671620111962223719719 := by
  unfold tailWord_2929044
  simp only [CollatzResearch.WordTrace]
  refine ⟨53415505600290651867049093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71220674133720869156065457 53415505600290651867049093)
  ·
    refine ⟨10015407300054497225071705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53415505600290651867049093 10015407300054497225071705)
    ·
      refine ⟨7511555475040872918803779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10015407300054497225071705 7511555475040872918803779)
      ·
        refine ⟨11267333212561309378205669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7511555475040872918803779 11267333212561309378205669)
        ·
          refine ⟨2112624977355245508413563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11267333212561309378205669 2112624977355245508413563)
          ·
            refine ⟨3168937466032868262620345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112624977355245508413563 3168937466032868262620345)
            ·
              refine ⟨2376703099524651196965259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168937466032868262620345 2376703099524651196965259)
              ·
                refine ⟨3565054649286976795447889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376703099524651196965259 3565054649286976795447889)
                ·
                  refine ⟨2673790986965232596585917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3565054649286976795447889 2673790986965232596585917)
                  ·
                    refine ⟨1002671620111962223719719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673790986965232596585917 1002671620111962223719719)
                    ·
                      rfl

theorem cell22_2929044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2929044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929044 prefixEnd_2929044 := by exact prefixLift 2929044
  have htrace : WordTrace (prefixWord ++ tailWord_2929044) baseStart_2929044 baseEnd_2929044 := by
    simpa [prefixWord, tailWord_2929044, baseEnd_2929044] using wordTrace_append hprefix tailTrace_2929044
  have hstable : (prefixWord ++ tailWord_2929044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929044).length < 2 ^ (prefixWord ++ tailWord_2929044).sum := by decide
  have hdescent : baseEnd_2929044 < baseStart_2929044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929049 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_2929049 : Nat := 118140960795 + 2929049 * 2 ^ 59
def prefixEnd_2929049 : Nat := 4983230072969 + 3 ^ 40 * 2929049 * 2
def baseEnd_2929049 : Nat := 1002673331714143877344703

theorem tailTrace_2929049 : CollatzResearch.WordTrace tailWord_2929049 prefixEnd_2929049 1002673331714143877344703 := by
  unfold tailWord_2929049
  simp only [CollatzResearch.WordTrace]
  refine ⟨106831193565563189588030201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71220795710375459725353467 106831193565563189588030201)
  ·
    refine ⟨80123395174172392191022651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106831193565563189588030201 80123395174172392191022651)
    ·
      refine ⟨120185092761258588286533977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80123395174172392191022651 120185092761258588286533977)
      ·
        refine ⟨90138819570943941214900483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120185092761258588286533977 90138819570943941214900483)
        ·
          refine ⟨135208229356415911822350725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90138819570943941214900483 135208229356415911822350725)
          ·
            refine ⟨25351543004327983466690761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135208229356415911822350725 25351543004327983466690761)
            ·
              refine ⟨19013657253245987600018071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25351543004327983466690761 19013657253245987600018071)
              ·
                refine ⟨28520485879868981400027107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19013657253245987600018071 28520485879868981400027107)
                ·
                  refine ⟨42780728819803472100040661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28520485879868981400027107 42780728819803472100040661)
                  ·
                    refine ⟨1002673331714143877344703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42780728819803472100040661 1002673331714143877344703)
                    ·
                      rfl

theorem cell22_2929049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_2929049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929049 prefixEnd_2929049 := by exact prefixLift 2929049
  have htrace : WordTrace (prefixWord ++ tailWord_2929049) baseStart_2929049 baseEnd_2929049 := by
    simpa [prefixWord, tailWord_2929049, baseEnd_2929049] using wordTrace_append hprefix tailTrace_2929049
  have hstable : (prefixWord ++ tailWord_2929049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929049).length < 2 ^ (prefixWord ++ tailWord_2929049).sum := by decide
  have hdescent : baseEnd_2929049 < baseStart_2929049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929111 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 8, 3]
def baseStart_2929111 : Nat := 118140960795 + 2929111 * 2 ^ 59
def prefixEnd_2929111 : Nat := 4983230072969 + 3 ^ 40 * 2929111 * 2
def baseEnd_2929111 : Nat := 1002694555581196382294513

theorem tailTrace_2929111 : CollatzResearch.WordTrace tailWord_2929111 prefixEnd_2929111 1002694555581196382294513 := by
  unfold tailWord_2929111
  simp only [CollatzResearch.WordTrace]
  refine ⟨106833454891338574176787187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71222303260892382784524791 106833454891338574176787187)
  ·
    refine ⟨160250182337007861265180781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106833454891338574176787187 160250182337007861265180781)
    ·
      refine ⟨60093818376377947974442793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160250182337007861265180781 60093818376377947974442793)
      ·
        refine ⟨45070363782283460980832095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60093818376377947974442793 45070363782283460980832095)
        ·
          refine ⟨67605545673425191471248143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45070363782283460980832095 67605545673425191471248143)
          ·
            refine ⟨101408318510137787206872215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67605545673425191471248143 101408318510137787206872215)
            ·
              refine ⟨152112477765206680810308323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101408318510137787206872215 152112477765206680810308323)
              ·
                refine ⟨228168716647810021215462485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152112477765206680810308323 228168716647810021215462485)
                ·
                  refine ⟨2673852148216523686118701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 228168716647810021215462485 2673852148216523686118701)
                  ·
                    refine ⟨1002694555581196382294513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673852148216523686118701 1002694555581196382294513)
                    ·
                      rfl

theorem cell22_2929111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_2929111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929111 prefixEnd_2929111 := by exact prefixLift 2929111
  have htrace : WordTrace (prefixWord ++ tailWord_2929111) baseStart_2929111 baseEnd_2929111 := by
    simpa [prefixWord, tailWord_2929111, baseEnd_2929111] using wordTrace_append hprefix tailTrace_2929111
  have hstable : (prefixWord ++ tailWord_2929111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929111).length < 2 ^ (prefixWord ++ tailWord_2929111).sum := by decide
  have hdescent : baseEnd_2929111 < baseStart_2929111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929130 : List Nat := [3, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_2929130 : Nat := 118140960795 + 2929130 * 2 ^ 59
def prefixEnd_2929130 : Nat := 4983230072969 + 3 ^ 40 * 2929130 * 2
def baseEnd_2929130 : Nat := 334233686556495555356485

theorem tailTrace_2929130 : CollatzResearch.WordTrace tailWord_2929130 prefixEnd_2929130 334233686556495555356485 := by
  unfold tailWord_2929130
  simp only [CollatzResearch.WordTrace]
  refine ⟨26708536969567435105432211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71222765252179826947819229 26708536969567435105432211)
  ·
    refine ⟨40062805454351152658148317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26708536969567435105432211 40062805454351152658148317)
    ·
      refine ⟨15023552045381682246805619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40062805454351152658148317 15023552045381682246805619)
      ·
        refine ⟨22535328068072523370208429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15023552045381682246805619 22535328068072523370208429)
        ·
          refine ⟨8450748025527196263828161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22535328068072523370208429 8450748025527196263828161)
          ·
            refine ⟨6338061019145397197871121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8450748025527196263828161 6338061019145397197871121)
            ·
              refine ⟨4753545764359047898403341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6338061019145397197871121 4753545764359047898403341)
              ·
                refine ⟨1782579661634642961901253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4753545764359047898403341 1782579661634642961901253)
                ·
                  refine ⟨334233686556495555356485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1782579661634642961901253 334233686556495555356485)
                  ·
                    rfl

theorem cell22_2929130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_2929130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929130 prefixEnd_2929130 := by exact prefixLift 2929130
  have htrace : WordTrace (prefixWord ++ tailWord_2929130) baseStart_2929130 baseEnd_2929130 := by
    simpa [prefixWord, tailWord_2929130, baseEnd_2929130] using wordTrace_append hprefix tailTrace_2929130
  have hstable : (prefixWord ++ tailWord_2929130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929130).length < 2 ^ (prefixWord ++ tailWord_2929130).sum := by decide
  have hdescent : baseEnd_2929130 < baseStart_2929130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929173 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_2929173 : Nat := 118140960795 + 2929173 * 2 ^ 59
def prefixEnd_2929173 : Nat := 4983230072969 + 3 ^ 40 * 2929173 * 2
def baseEnd_2929173 : Nat := 1002715779448248887244323

theorem tailTrace_2929173 : CollatzResearch.WordTrace tailWord_2929173 prefixEnd_2929173 1002715779448248887244323 := by
  unfold tailWord_2929173
  simp only [CollatzResearch.WordTrace]
  refine ⟨106835716217113958765544173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71223810811409305843696115 106835716217113958765544173)
  ·
    refine ⟨40063393581417734537079065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106835716217113958765544173 40063393581417734537079065)
    ·
      refine ⟨30047545186063300902809299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40063393581417734537079065 30047545186063300902809299)
      ·
        refine ⟨45071317779094951354213949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30047545186063300902809299 45071317779094951354213949)
        ·
          refine ⟨16901744167160606757830231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45071317779094951354213949 16901744167160606757830231)
          ·
            refine ⟨25352616250740910136745347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16901744167160606757830231 25352616250740910136745347)
            ·
              refine ⟨38028924376111365205118021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25352616250740910136745347 38028924376111365205118021)
              ·
                refine ⟨7130423320520880975959629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38028924376111365205118021 7130423320520880975959629)
                ·
                  refine ⟨2673908745195330365984861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7130423320520880975959629 2673908745195330365984861)
                  ·
                    refine ⟨1002715779448248887244323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673908745195330365984861 1002715779448248887244323)
                    ·
                      rfl

theorem cell22_2929173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_2929173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929173 prefixEnd_2929173 := by exact prefixLift 2929173
  have htrace : WordTrace (prefixWord ++ tailWord_2929173) baseStart_2929173 baseEnd_2929173 := by
    simpa [prefixWord, tailWord_2929173, baseEnd_2929173] using wordTrace_append hprefix tailTrace_2929173
  have hstable : (prefixWord ++ tailWord_2929173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929173).length < 2 ^ (prefixWord ++ tailWord_2929173).sum := by decide
  have hdescent : baseEnd_2929173 < baseStart_2929173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929201 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_2929201 : Nat := 118140960795 + 2929201 * 2 ^ 59
def prefixEnd_2929201 : Nat := 4983230072969 + 3 ^ 40 * 2929201 * 2
def baseEnd_2929201 : Nat := 1002725364420466147544237

theorem tailTrace_2929201 : CollatzResearch.WordTrace tailWord_2929201 prefixEnd_2929201 1002725364420466147544237 := by
  unfold tailWord_2929201
  simp only [CollatzResearch.WordTrace]
  refine ⟨106836737461012519547563457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71224491640675013031708971 106836737461012519547563457)
  ·
    refine ⟨80127553095759389660672593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106836737461012519547563457 80127553095759389660672593)
    ·
      refine ⟨60095664821819542245504445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80127553095759389660672593 60095664821819542245504445)
      ·
        refine ⟨22535874308182328342064167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60095664821819542245504445 22535874308182328342064167)
        ·
          refine ⟨33803811462273492513096251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22535874308182328342064167 33803811462273492513096251)
          ·
            refine ⟨50705717193410238769644377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33803811462273492513096251 50705717193410238769644377)
            ·
              refine ⟨38029287895057679077233283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50705717193410238769644377 38029287895057679077233283)
              ·
                refine ⟨57043931842586518615849925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38029287895057679077233283 57043931842586518615849925)
                ·
                  refine ⟨10695737220484972240471861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57043931842586518615849925 10695737220484972240471861)
                  ·
                    refine ⟨1002725364420466147544237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10695737220484972240471861 1002725364420466147544237)
                    ·
                      rfl

theorem cell22_2929201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_2929201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929201 prefixEnd_2929201 := by exact prefixLift 2929201
  have htrace : WordTrace (prefixWord ++ tailWord_2929201) baseStart_2929201 baseEnd_2929201 := by
    simpa [prefixWord, tailWord_2929201, baseEnd_2929201] using wordTrace_append hprefix tailTrace_2929201
  have hstable : (prefixWord ++ tailWord_2929201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929201).length < 2 ^ (prefixWord ++ tailWord_2929201).sum := by decide
  have hdescent : baseEnd_2929201 < baseStart_2929201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929207 : List Nat := [1, 1, 3, 1, 2, 3, 5, 2, 1, 3]
def baseStart_2929207 : Nat := 118140960795 + 2929207 * 2 ^ 59
def prefixEnd_2929207 : Nat := 4983230072969 + 3 ^ 40 * 2929207 * 2
def baseEnd_2929207 : Nat := 1002727418343084131894219

theorem tailTrace_2929207 : CollatzResearch.WordTrace tailWord_2929207 prefixEnd_2929207 1002727418343084131894219 := by
  unfold tailWord_2929207
  simp only [CollatzResearch.WordTrace]
  refine ⟨106836956298990782572281875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71224637532660521714854583 106836956298990782572281875)
  ·
    refine ⟨160255434448486173858422813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106836956298990782572281875 160255434448486173858422813)
    ·
      refine ⟨60095787918182315196908555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160255434448486173858422813 60095787918182315196908555)
      ·
        refine ⟨90143681877273472795362833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60095787918182315196908555 90143681877273472795362833)
        ·
          refine ⟨67607761407955104596522125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90143681877273472795362833 67607761407955104596522125)
          ·
            refine ⟨25352910527983164223695797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67607761407955104596522125 25352910527983164223695797)
            ·
              refine ⟨2376835361998421645971481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25352910527983164223695797 2376835361998421645971481)
              ·
                refine ⟨1782626521498816234478611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376835361998421645971481 1782626521498816234478611)
                ·
                  refine ⟨2673939782248224351717917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782626521498816234478611 2673939782248224351717917)
                  ·
                    refine ⟨1002727418343084131894219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673939782248224351717917 1002727418343084131894219)
                    ·
                      rfl

theorem cell22_2929207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_2929207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929207 prefixEnd_2929207 := by exact prefixLift 2929207
  have htrace : WordTrace (prefixWord ++ tailWord_2929207) baseStart_2929207 baseEnd_2929207 := by
    simpa [prefixWord, tailWord_2929207, baseEnd_2929207] using wordTrace_append hprefix tailTrace_2929207
  have hstable : (prefixWord ++ tailWord_2929207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929207).length < 2 ^ (prefixWord ++ tailWord_2929207).sum := by decide
  have hdescent : baseEnd_2929207 < baseStart_2929207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929231 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 6]
def baseStart_2929231 : Nat := 118140960795 + 2929231 * 2 ^ 59
def prefixEnd_2929231 : Nat := 4983230072969 + 3 ^ 40 * 2929231 * 2
def baseEnd_2929231 : Nat := 334245211344518689764715

theorem tailTrace_2929231 : CollatzResearch.WordTrace tailWord_2929231 prefixEnd_2929231 334245211344518689764715 := by
  unfold tailWord_2929231
  simp only [CollatzResearch.WordTrace]
  refine ⟨106837831650903834671155547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71225221100602556447437031 106837831650903834671155547)
  ·
    refine ⟨160256747476355752006733321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106837831650903834671155547 160256747476355752006733321)
    ·
      refine ⟨120192560607266814005049991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160256747476355752006733321 120192560607266814005049991)
      ·
        refine ⟨180288840910900221007574987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120192560607266814005049991 180288840910900221007574987)
        ·
          refine ⟨270433261366350331511362481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180288840910900221007574987 270433261366350331511362481)
          ·
            refine ⟨202824946024762748633521861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270433261366350331511362481 202824946024762748633521861)
            ·
              refine ⟨38029677379643015368785349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202824946024762748633521861 38029677379643015368785349)
              ·
                refine ⟨7130564508683065381647253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38029677379643015368785349 7130564508683065381647253)
                ·
                  refine ⟨334245211344518689764715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7130564508683065381647253 334245211344518689764715)
                  ·
                    rfl

theorem cell22_2929231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 6].length) (baseStart_2929231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929231 prefixEnd_2929231 := by exact prefixLift 2929231
  have htrace : WordTrace (prefixWord ++ tailWord_2929231) baseStart_2929231 baseEnd_2929231 := by
    simpa [prefixWord, tailWord_2929231, baseEnd_2929231] using wordTrace_append hprefix tailTrace_2929231
  have hstable : (prefixWord ++ tailWord_2929231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929231).length < 2 ^ (prefixWord ++ tailWord_2929231).sum := by decide
  have hdescent : baseEnd_2929231 < baseStart_2929231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929233 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_2929233 : Nat := 118140960795 + 2929233 * 2 ^ 59
def prefixEnd_2929233 : Nat := 4983230072969 + 3 ^ 40 * 2929233 * 2
def baseEnd_2929233 : Nat := 1002736318674428730744139

theorem tailTrace_2929233 : CollatzResearch.WordTrace tailWord_2929233 prefixEnd_2929233 1002736318674428730744139 := by
  unfold tailWord_2929233
  simp only [CollatzResearch.WordTrace]
  refine ⟨106837904596896589012728353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71225269731264392675152235 106837904596896589012728353)
  ·
    refine ⟨80128428447672441759546265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106837904596896589012728353 80128428447672441759546265)
    ·
      refine ⟨60096321335754331319659699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80128428447672441759546265 60096321335754331319659699)
      ·
        refine ⟨90144482003631496979489549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60096321335754331319659699 90144482003631496979489549)
        ·
          refine ⟨33804180751361811367308581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90144482003631496979489549 33804180751361811367308581)
          ·
            refine ⟨6338283890880339631370359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33804180751361811367308581 6338283890880339631370359)
            ·
              refine ⟨9507425836320509447055539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6338283890880339631370359 9507425836320509447055539)
              ·
                refine ⟨14261138754480764170583309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9507425836320509447055539 14261138754480764170583309)
                ·
                  refine ⟨5347927032930286563968741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14261138754480764170583309 5347927032930286563968741)
                  ·
                    refine ⟨1002736318674428730744139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5347927032930286563968741 1002736318674428730744139)
                    ·
                      rfl

theorem cell22_2929233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_2929233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929233 prefixEnd_2929233 := by exact prefixLift 2929233
  have htrace : WordTrace (prefixWord ++ tailWord_2929233) baseStart_2929233 baseEnd_2929233 := by
    simpa [prefixWord, tailWord_2929233, baseEnd_2929233] using wordTrace_append hprefix tailTrace_2929233
  have hstable : (prefixWord ++ tailWord_2929233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929233).length < 2 ^ (prefixWord ++ tailWord_2929233).sum := by decide
  have hdescent : baseEnd_2929233 < baseStart_2929233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929263 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 4, 3]
def baseStart_2929263 : Nat := 118140960795 + 2929263 * 2 ^ 59
def prefixEnd_2929263 : Nat := 4983230072969 + 3 ^ 40 * 2929263 * 2
def baseEnd_2929263 : Nat := 1002746588287518652494047

theorem tailTrace_2929263 : CollatzResearch.WordTrace tailWord_2929263 prefixEnd_2929263 1002746588287518652494047 := by
  unfold tailWord_2929263
  simp only [CollatzResearch.WordTrace]
  refine ⟨106838998786787904136320443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71225999191191936090880295 106838998786787904136320443)
  ·
    refine ⟨160258498180181856204480665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106838998786787904136320443 160258498180181856204480665)
    ·
      refine ⟨120193873635136392153360499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160258498180181856204480665 120193873635136392153360499)
      ·
        refine ⟨180290810452704588230040749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120193873635136392153360499 180290810452704588230040749)
        ·
          refine ⟨67609053919764220586265281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180290810452704588230040749 67609053919764220586265281)
          ·
            refine ⟨50706790439823165439698961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67609053919764220586265281 50706790439823165439698961)
            ·
              refine ⟨38030092829867374079774221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50706790439823165439698961 38030092829867374079774221)
              ·
                refine ⟨14261284811200265279915333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38030092829867374079774221 14261284811200265279915333)
                ·
                  refine ⟨2673990902100049739984125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14261284811200265279915333 2673990902100049739984125)
                  ·
                    refine ⟨1002746588287518652494047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2673990902100049739984125 1002746588287518652494047)
                    ·
                      rfl

theorem cell22_2929263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_2929263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929263 prefixEnd_2929263 := by exact prefixLift 2929263
  have htrace : WordTrace (prefixWord ++ tailWord_2929263) baseStart_2929263 baseEnd_2929263 := by
    simpa [prefixWord, tailWord_2929263, baseEnd_2929263] using wordTrace_append hprefix tailTrace_2929263
  have hstable : (prefixWord ++ tailWord_2929263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929263).length < 2 ^ (prefixWord ++ tailWord_2929263).sum := by decide
  have hdescent : baseEnd_2929263 < baseStart_2929263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929280 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 2, 3]
def baseStart_2929280 : Nat := 118140960795 + 2929280 * 2 ^ 59
def prefixEnd_2929280 : Nat := 4983230072969 + 3 ^ 40 * 2929280 * 2
def baseEnd_2929280 : Nat := 1002752407734936274818995

theorem tailTrace_2929280 : CollatzResearch.WordTrace tailWord_2929280 prefixEnd_2929280 1002752407734936274818995 := by
  unfold tailWord_2929280
  simp only [CollatzResearch.WordTrace]
  refine ⟨53419809413863158019844647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71226412551817544026459529 53419809413863158019844647)
  ·
    refine ⟨80129714120794737029766971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53419809413863158019844647 80129714120794737029766971)
    ·
      refine ⟨120194571181192105544650457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80129714120794737029766971 120194571181192105544650457)
      ·
        refine ⟨90145928385894079158487843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120194571181192105544650457 90145928385894079158487843)
        ·
          refine ⟨135218892578841118737731765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90145928385894079158487843 135218892578841118737731765)
          ·
            refine ⟨12676771179266354881662353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135218892578841118737731765 12676771179266354881662353)
            ·
              refine ⟨9507578384449766161246765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12676771179266354881662353 9507578384449766161246765)
              ·
                refine ⟨3565341894168662310467537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9507578384449766161246765 3565341894168662310467537)
                ·
                  refine ⟨2674006420626496732850653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3565341894168662310467537 2674006420626496732850653)
                  ·
                    refine ⟨1002752407734936274818995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2674006420626496732850653 1002752407734936274818995)
                    ·
                      rfl

theorem cell22_2929280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_2929280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929280 prefixEnd_2929280 := by exact prefixLift 2929280
  have htrace : WordTrace (prefixWord ++ tailWord_2929280) baseStart_2929280 baseEnd_2929280 := by
    simpa [prefixWord, tailWord_2929280, baseEnd_2929280] using wordTrace_append hprefix tailTrace_2929280
  have hstable : (prefixWord ++ tailWord_2929280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929280).length < 2 ^ (prefixWord ++ tailWord_2929280).sum := by decide
  have hdescent : baseEnd_2929280 < baseStart_2929280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929291 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 9]
def baseStart_2929291 : Nat := 118140960795 + 2929291 * 2 ^ 59
def prefixEnd_2929291 : Nat := 4983230072969 + 3 ^ 40 * 2929291 * 2
def baseEnd_2929291 : Nat := 1002756173259735912793961

theorem tailTrace_2929291 : CollatzResearch.WordTrace tailWord_2929291 prefixEnd_2929291 1002756173259735912793961 := by
  unfold tailWord_2929291
  simp only [CollatzResearch.WordTrace]
  refine ⟨106840020030686464918339727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71226680020457643278893151 106840020030686464918339727)
  ·
    refine ⟨160260030046029697377509591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106840020030686464918339727 160260030046029697377509591)
    ·
      refine ⟨240390045069044546066264387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160260030046029697377509591 240390045069044546066264387)
      ·
        refine ⟨360585067603566819099396581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240390045069044546066264387 360585067603566819099396581)
        ·
          refine ⟨67609700175668778581136859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360585067603566819099396581 67609700175668778581136859)
          ·
            refine ⟨101414550263503167871705289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67609700175668778581136859 101414550263503167871705289)
            ·
              refine ⟨76060912697627375903778967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101414550263503167871705289 76060912697627375903778967)
              ·
                refine ⟨114091369046441063855668451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76060912697627375903778967 114091369046441063855668451)
                ·
                  refine ⟨171137053569661595783502677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114091369046441063855668451 171137053569661595783502677)
                  ·
                    refine ⟨1002756173259735912793961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171137053569661595783502677 1002756173259735912793961)
                    ·
                      rfl

theorem cell22_2929291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_2929291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929291 prefixEnd_2929291 := by exact prefixLift 2929291
  have htrace : WordTrace (prefixWord ++ tailWord_2929291) baseStart_2929291 baseEnd_2929291 := by
    simpa [prefixWord, tailWord_2929291, baseEnd_2929291] using wordTrace_append hprefix tailTrace_2929291
  have hstable : (prefixWord ++ tailWord_2929291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929291).length < 2 ^ (prefixWord ++ tailWord_2929291).sum := by decide
  have hdescent : baseEnd_2929291 < baseStart_2929291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929413 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_2929413 : Nat := 118140960795 + 2929413 * 2 ^ 59
def prefixEnd_2929413 : Nat := 4983230072969 + 3 ^ 40 * 2929413 * 2
def baseEnd_2929413 : Nat := 1002797936352968261243587

theorem tailTrace_2929413 : CollatzResearch.WordTrace tailWord_2929413 prefixEnd_2929413 1002797936352968261243587 := by
  unfold tailWord_2929413
  simp only [CollatzResearch.WordTrace]
  refine ⟨106844469736244479754280893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71229646490829653169520595 106844469736244479754280893)
  ·
    refine ⟨40066676151091679907855335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106844469736244479754280893 40066676151091679907855335)
    ·
      refine ⟨60100014226637519861783003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40066676151091679907855335 60100014226637519861783003)
      ·
        refine ⟨90150021339956279792674505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60100014226637519861783003 90150021339956279792674505)
        ·
          refine ⟨67612516004967209844505879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90150021339956279792674505 67612516004967209844505879)
          ·
            refine ⟨101418774007450814766758819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67612516004967209844505879 101418774007450814766758819)
            ·
              refine ⟨152128161011176222150138229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101418774007450814766758819 152128161011176222150138229)
              ·
                refine ⟨14262015094797770826575459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152128161011176222150138229 14262015094797770826575459)
                ·
                  refine ⟨21393022642196656239863189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14262015094797770826575459 21393022642196656239863189)
                  ·
                    refine ⟨1002797936352968261243587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21393022642196656239863189 1002797936352968261243587)
                    ·
                      rfl

theorem cell22_2929413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_2929413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929413 prefixEnd_2929413 := by exact prefixLift 2929413
  have htrace : WordTrace (prefixWord ++ tailWord_2929413) baseStart_2929413 baseEnd_2929413 := by
    simpa [prefixWord, tailWord_2929413, baseEnd_2929413] using wordTrace_append hprefix tailTrace_2929413
  have hstable : (prefixWord ++ tailWord_2929413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929413).length < 2 ^ (prefixWord ++ tailWord_2929413).sum := by decide
  have hdescent : baseEnd_2929413 < baseStart_2929413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929415 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 3, 5]
def baseStart_2929415 : Nat := 118140960795 + 2929415 * 2 ^ 59
def prefixEnd_2929415 : Nat := 4983230072969 + 3 ^ 40 * 2929415 * 2
def baseEnd_2929415 : Nat := 1002798620993840922693581

theorem tailTrace_2929415 : CollatzResearch.WordTrace tailWord_2929415 prefixEnd_2929415 1002798620993840922693581 := by
  unfold tailWord_2929415
  simp only [CollatzResearch.WordTrace]
  refine ⟨106844542682237234095853699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71229695121491489397235799 106844542682237234095853699)
  ·
    refine ⟨160266814023355851143780549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106844542682237234095853699 160266814023355851143780549)
    ·
      refine ⟨30050027629379222089458853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160266814023355851143780549 30050027629379222089458853)
      ·
        refine ⟨5634380180508604141773535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30050027629379222089458853 5634380180508604141773535)
        ·
          refine ⟨8451570270762906212660303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634380180508604141773535 8451570270762906212660303)
          ·
            refine ⟨12677355406144359318990455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451570270762906212660303 12677355406144359318990455)
            ·
              refine ⟨19016033109216538978485683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12677355406144359318990455 19016033109216538978485683)
              ·
                refine ⟨28524049663824808467728525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19016033109216538978485683 28524049663824808467728525)
                ·
                  refine ⟨10696518623934303175398197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28524049663824808467728525 10696518623934303175398197)
                  ·
                    refine ⟨1002798620993840922693581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10696518623934303175398197 1002798620993840922693581)
                    ·
                      rfl

theorem cell22_2929415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_2929415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929415 prefixEnd_2929415 := by exact prefixLift 2929415
  have htrace : WordTrace (prefixWord ++ tailWord_2929415) baseStart_2929415 baseEnd_2929415 := by
    simpa [prefixWord, tailWord_2929415, baseEnd_2929415] using wordTrace_append hprefix tailTrace_2929415
  have hstable : (prefixWord ++ tailWord_2929415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929415).length < 2 ^ (prefixWord ++ tailWord_2929415).sum := by decide
  have hdescent : baseEnd_2929415 < baseStart_2929415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929443 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 2, 7]
def baseStart_2929443 : Nat := 118140960795 + 2929443 * 2 ^ 59
def prefixEnd_2929443 : Nat := 4983230072969 + 3 ^ 40 * 2929443 * 2
def baseEnd_2929443 : Nat := 1002808205966058182993495

theorem tailTrace_2929443 : CollatzResearch.WordTrace tailWord_2929443 prefixEnd_2929443 1002808205966058182993495 := by
  unfold tailWord_2929443
  simp only [CollatzResearch.WordTrace]
  refine ⟨106845563926135794877872983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71230375950757196585248655 106845563926135794877872983)
  ·
    refine ⟨160268345889203692316809475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106845563926135794877872983 160268345889203692316809475)
    ·
      refine ⟨240402518833805538475214213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160268345889203692316809475 240402518833805538475214213)
      ·
        refine ⟨45075472281338538464102665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240402518833805538475214213 45075472281338538464102665)
        ·
          refine ⟨33806604211003903848076999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45075472281338538464102665 33806604211003903848076999)
          ·
            refine ⟨50709906316505855772115499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33806604211003903848076999 50709906316505855772115499)
            ·
              refine ⟨76064859474758783658173249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50709906316505855772115499 76064859474758783658173249)
              ·
                refine ⟨57048644606069087743629937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76064859474758783658173249 57048644606069087743629937)
                ·
                  refine ⟨42786483454551815807722453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57048644606069087743629937 42786483454551815807722453)
                  ·
                    refine ⟨1002808205966058182993495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42786483454551815807722453 1002808205966058182993495)
                    ·
                      rfl

theorem cell22_2929443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_2929443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929443 prefixEnd_2929443 := by exact prefixLift 2929443
  have htrace : WordTrace (prefixWord ++ tailWord_2929443) baseStart_2929443 baseEnd_2929443 := by
    simpa [prefixWord, tailWord_2929443, baseEnd_2929443] using wordTrace_append hprefix tailTrace_2929443
  have hstable : (prefixWord ++ tailWord_2929443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929443).length < 2 ^ (prefixWord ++ tailWord_2929443).sum := by decide
  have hdescent : baseEnd_2929443 < baseStart_2929443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929490 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_2929490 : Nat := 118140960795 + 2929490 * 2 ^ 59
def prefixEnd_2929490 : Nat := 4983230072969 + 3 ^ 40 * 2929490 * 2
def baseEnd_2929490 : Nat := 334274765008855242356117

theorem tailTrace_2929490 : CollatzResearch.WordTrace tailWord_2929490 prefixEnd_2929490 334274765008855242356117 := by
  unfold tailWord_2929490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26711819539241380476208481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71231518771310347936555949 26711819539241380476208481)
  ·
    refine ⟨20033864654431035357156361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26711819539241380476208481 20033864654431035357156361)
    ·
      refine ⟨15025398490823276517867271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20033864654431035357156361 15025398490823276517867271)
      ·
        refine ⟨22538097736234914776800907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15025398490823276517867271 22538097736234914776800907)
        ·
          refine ⟨33807146604352372165201361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22538097736234914776800907 33807146604352372165201361)
          ·
            refine ⟨25355359953264279123901021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33807146604352372165201361 25355359953264279123901021)
            ·
              refine ⟨9508259982474104671462883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25355359953264279123901021 9508259982474104671462883)
              ·
                refine ⟨14262389973711157007194325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9508259982474104671462883 14262389973711157007194325)
                ·
                  refine ⟨334274765008855242356117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14262389973711157007194325 334274765008855242356117)
                  ·
                    rfl

theorem cell22_2929490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_2929490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929490 prefixEnd_2929490 := by exact prefixLift 2929490
  have htrace : WordTrace (prefixWord ++ tailWord_2929490) baseStart_2929490 baseEnd_2929490 := by
    simpa [prefixWord, tailWord_2929490, baseEnd_2929490] using wordTrace_append hprefix tailTrace_2929490
  have hstable : (prefixWord ++ tailWord_2929490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929490).length < 2 ^ (prefixWord ++ tailWord_2929490).sum := by decide
  have hdescent : baseEnd_2929490 < baseStart_2929490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929520 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_2929520 : Nat := 118140960795 + 2929520 * 2 ^ 59
def prefixEnd_2929520 : Nat := 4983230072969 + 3 ^ 40 * 2929520 * 2
def baseEnd_2929520 : Nat := 1002834564639655648818259

theorem tailTrace_2929520 : CollatzResearch.WordTrace tailWord_2929520 prefixEnd_2929520 1002834564639655648818259 := by
  unfold tailWord_2929520
  simp only [CollatzResearch.WordTrace]
  refine ⟨53424186173428418514213007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71232248231237891352284009 53424186173428418514213007)
  ·
    refine ⟨80136279260142627771319511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53424186173428418514213007 80136279260142627771319511)
    ·
      refine ⟨120204418890213941656979267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80136279260142627771319511 120204418890213941656979267)
      ·
        refine ⟨180306628335320912485468901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120204418890213941656979267 180306628335320912485468901)
        ·
          refine ⟨33807492812872671091025419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180306628335320912485468901 33807492812872671091025419)
          ·
            refine ⟨50711239219309006636538129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33807492812872671091025419 50711239219309006636538129)
            ·
              refine ⟨38033429414481754977403597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50711239219309006636538129 38033429414481754977403597)
              ·
                refine ⟨14262536030430658116526349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38033429414481754977403597 14262536030430658116526349)
                ·
                  refine ⟨5348451011411496793697381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14262536030430658116526349 5348451011411496793697381)
                  ·
                    refine ⟨1002834564639655648818259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5348451011411496793697381 1002834564639655648818259)
                    ·
                      rfl

theorem cell22_2929520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_2929520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929520 prefixEnd_2929520 := by exact prefixLift 2929520
  have htrace : WordTrace (prefixWord ++ tailWord_2929520) baseStart_2929520 baseEnd_2929520 := by
    simpa [prefixWord, tailWord_2929520, baseEnd_2929520] using wordTrace_append hprefix tailTrace_2929520
  have hstable : (prefixWord ++ tailWord_2929520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929520).length < 2 ^ (prefixWord ++ tailWord_2929520).sum := by decide
  have hdescent : baseEnd_2929520 < baseStart_2929520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929558 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2929558 : Nat := 118140960795 + 2929558 * 2 ^ 59
def prefixEnd_2929558 : Nat := 4983230072969 + 3 ^ 40 * 2929558 * 2
def baseEnd_2929558 : Nat := 334282524272078738789381

theorem tailTrace_2929558 : CollatzResearch.WordTrace tailWord_2929558 prefixEnd_2929558 334282524272078738789381 := by
  unfold tailWord_2929558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6678109895044948094894333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71233172213812779678872885 6678109895044948094894333)
  ·
    refine ⟨2504291210641855535585375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6678109895044948094894333 2504291210641855535585375)
    ·
      refine ⟨3756436815962783303378063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2504291210641855535585375 3756436815962783303378063)
      ·
        refine ⟨5634655223944174955067095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3756436815962783303378063 5634655223944174955067095)
        ·
          refine ⟨8451982835916262432600643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634655223944174955067095 8451982835916262432600643)
          ·
            refine ⟨12677974253874393648900965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451982835916262432600643 12677974253874393648900965)
            ·
              refine ⟨2377120172601448809168931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12677974253874393648900965 2377120172601448809168931)
              ·
                refine ⟨3565680258902173213753397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377120172601448809168931 3565680258902173213753397)
                ·
                  refine ⟨334282524272078738789381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3565680258902173213753397 334282524272078738789381)
                  ·
                    rfl

theorem cell22_2929558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2929558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929558 prefixEnd_2929558 := by exact prefixLift 2929558
  have htrace : WordTrace (prefixWord ++ tailWord_2929558) baseStart_2929558 baseEnd_2929558 := by
    simpa [prefixWord, tailWord_2929558, baseEnd_2929558] using wordTrace_append hprefix tailTrace_2929558
  have hstable : (prefixWord ++ tailWord_2929558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929558).length < 2 ^ (prefixWord ++ tailWord_2929558).sum := by decide
  have hdescent : baseEnd_2929558 < baseStart_2929558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929588 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2929588 : Nat := 118140960795 + 2929588 * 2 ^ 59
def prefixEnd_2929588 : Nat := 4983230072969 + 3 ^ 40 * 2929588 * 2
def baseEnd_2929588 : Nat := 1002857842429326138118051

theorem tailTrace_2929588 : CollatzResearch.WordTrace tailWord_2929588 prefixEnd_2929588 1002857842429326138118051 := by
  unfold tailWord_2929588
  simp only [CollatzResearch.WordTrace]
  refine ⟨53425426255305242320950709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71233901673740323094600945 53425426255305242320950709)
  ·
    refine ⟨5008633711434866467589129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53425426255305242320950709 5008633711434866467589129)
    ·
      refine ⟨3756475283576149850691847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5008633711434866467589129 3756475283576149850691847)
      ·
        refine ⟨5634712925364224776037771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3756475283576149850691847 5634712925364224776037771)
        ·
          refine ⟨8452069388046337164056657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634712925364224776037771 8452069388046337164056657)
          ·
            refine ⟨6339052041034752873042493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8452069388046337164056657 6339052041034752873042493)
            ·
              refine ⟨2377144515388032327390935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6339052041034752873042493 2377144515388032327390935)
              ·
                refine ⟨3565716773082048491086403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377144515388032327390935 3565716773082048491086403)
                ·
                  refine ⟨5348575159623072736629605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3565716773082048491086403 5348575159623072736629605)
                  ·
                    refine ⟨1002857842429326138118051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5348575159623072736629605 1002857842429326138118051)
                    ·
                      rfl

theorem cell22_2929588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2929588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929588 prefixEnd_2929588 := by exact prefixLift 2929588
  have htrace : WordTrace (prefixWord ++ tailWord_2929588) baseStart_2929588 baseEnd_2929588 := by
    simpa [prefixWord, tailWord_2929588, baseEnd_2929588] using wordTrace_append hprefix tailTrace_2929588
  have hstable : (prefixWord ++ tailWord_2929588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929588).length < 2 ^ (prefixWord ++ tailWord_2929588).sum := by decide
  have hdescent : baseEnd_2929588 < baseStart_2929588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929597 : List Nat := [1, 4, 1, 2, 5, 9]
def baseStart_2929597 : Nat := 118140960795 + 2929597 * 2 ^ 59
def prefixEnd_2929597 : Nat := 4983230072969 + 3 ^ 40 * 2929597 * 2
def baseEnd_2929597 : Nat := 12380999053250038452383

theorem tailTrace_2929597 : CollatzResearch.WordTrace tailWord_2929597 prefixEnd_2929597 12380999053250038452383 := by
  unfold tailWord_2929597
  simp only [CollatzResearch.WordTrace]
  refine ⟨106851180767577879178979045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71234120511718586119319363 106851180767577879178979045)
  ·
    refine ⟨20034596393920852346058571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106851180767577879178979045 20034596393920852346058571)
    ·
      refine ⟨30051894590881278519087857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20034596393920852346058571 30051894590881278519087857)
      ·
        refine ⟨22538920943160958889315893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30051894590881278519087857 22538920943160958889315893)
        ·
          refine ⟨2113023838421339895873365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22538920943160958889315893 2113023838421339895873365)
          ·
            refine ⟨12380999053250038452383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2113023838421339895873365 12380999053250038452383)
            ·
              rfl

theorem cell22_2929597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 9].length) (baseStart_2929597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929597 prefixEnd_2929597 := by exact prefixLift 2929597
  have htrace : WordTrace (prefixWord ++ tailWord_2929597) baseStart_2929597 baseEnd_2929597 := by
    simpa [prefixWord, tailWord_2929597, baseEnd_2929597] using wordTrace_append hprefix tailTrace_2929597
  have hstable : (prefixWord ++ tailWord_2929597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929597).length < 2 ^ (prefixWord ++ tailWord_2929597).sum := by decide
  have hdescent : baseEnd_2929597 < baseStart_2929597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929629 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2929629 : Nat := 118140960795 + 2929629 * 2 ^ 59
def prefixEnd_2929629 : Nat := 4983230072969 + 3 ^ 40 * 2929629 * 2
def baseEnd_2929629 : Nat := 1002871877567215697842925

theorem tailTrace_2929629 : CollatzResearch.WordTrace tailWord_2929629 prefixEnd_2929629 1002871877567215697842925 := by
  unfold tailWord_2929629
  simp only [CollatzResearch.WordTrace]
  refine ⟨106852347903461948644143941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71234898602307965762762627 106852347903461948644143941)
  ·
    refine ⟨20034815231899115370776989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106852347903461948644143941 20034815231899115370776989)
    ·
      refine ⟨7513055711962168264041371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20034815231899115370776989 7513055711962168264041371)
      ·
        refine ⟨11269583567943252396062057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7513055711962168264041371 11269583567943252396062057)
        ·
          refine ⟨8452187675957439297046543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11269583567943252396062057 8452187675957439297046543)
          ·
            refine ⟨12678281513936158945569815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8452187675957439297046543 12678281513936158945569815)
            ·
              refine ⟨19017422270904238418354723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12678281513936158945569815 19017422270904238418354723)
              ·
                refine ⟨28526133406356357627532085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19017422270904238418354723 28526133406356357627532085)
                ·
                  refine ⟨2674325006845908527581133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28526133406356357627532085 2674325006845908527581133)
                  ·
                    refine ⟨1002871877567215697842925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2674325006845908527581133 1002871877567215697842925)
                    ·
                      rfl

theorem cell22_2929629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2929629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929629 prefixEnd_2929629 := by exact prefixLift 2929629
  have htrace : WordTrace (prefixWord ++ tailWord_2929629) baseStart_2929629 baseEnd_2929629 := by
    simpa [prefixWord, tailWord_2929629, baseEnd_2929629] using wordTrace_append hprefix tailTrace_2929629
  have hstable : (prefixWord ++ tailWord_2929629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929629).length < 2 ^ (prefixWord ++ tailWord_2929629).sum := by decide
  have hdescent : baseEnd_2929629 < baseStart_2929629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929719 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 2, 3]
def baseStart_2929719 : Nat := 118140960795 + 2929719 * 2 ^ 59
def prefixEnd_2929719 : Nat := 4983230072969 + 3 ^ 40 * 2929719 * 2
def baseEnd_2929719 : Nat := 1002902686406485463092649

theorem tailTrace_2929719 : CollatzResearch.WordTrace tailWord_2929719 prefixEnd_2929719 1002902686406485463092649 := by
  unfold tailWord_2929719
  simp only [CollatzResearch.WordTrace]
  refine ⟨106855630473135894014920211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71237086982090596009946807 106855630473135894014920211)
  ·
    refine ⟨160283445709703841022380317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106855630473135894014920211 160283445709703841022380317)
    ·
      refine ⟨60106292141138940383392619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160283445709703841022380317 60106292141138940383392619)
      ·
        refine ⟨90159438211708410575088929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60106292141138940383392619 90159438211708410575088929)
        ·
          refine ⟨67619578658781307931316697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90159438211708410575088929 67619578658781307931316697)
          ·
            refine ⟨50714683994085980948487523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67619578658781307931316697 50714683994085980948487523)
            ·
              refine ⟨76072025991128971422731285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50714683994085980948487523 76072025991128971422731285)
              ·
                refine ⟨3565876218334170535440529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76072025991128971422731285 3565876218334170535440529)
                ·
                  refine ⟨2674407163750627901580397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3565876218334170535440529 2674407163750627901580397)
                  ·
                    refine ⟨1002902686406485463092649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2674407163750627901580397 1002902686406485463092649)
                    ·
                      rfl

theorem cell22_2929719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_2929719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929719 prefixEnd_2929719 := by exact prefixLift 2929719
  have htrace : WordTrace (prefixWord ++ tailWord_2929719) baseStart_2929719 baseEnd_2929719 := by
    simpa [prefixWord, tailWord_2929719, baseEnd_2929719] using wordTrace_append hprefix tailTrace_2929719
  have hstable : (prefixWord ++ tailWord_2929719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929719).length < 2 ^ (prefixWord ++ tailWord_2929719).sum := by decide
  have hdescent : baseEnd_2929719 < baseStart_2929719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929792 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_2929792 : Nat := 118140960795 + 2929792 * 2 ^ 59
def prefixEnd_2929792 : Nat := 4983230072969 + 3 ^ 40 * 2929792 * 2
def baseEnd_2929792 : Nat := 1002927675798337606017425

theorem tailTrace_2929792 : CollatzResearch.WordTrace tailWord_2929792 prefixEnd_2929792 1002927675798337606017425 := by
  unfold tailWord_2929792
  simp only [CollatzResearch.WordTrace]
  refine ⟨53429146500935713741163815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71238862001247618321551753 53429146500935713741163815)
  ·
    refine ⟨80143719751403570611745723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53429146500935713741163815 80143719751403570611745723)
    ·
      refine ⟨120215579627105355917618585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80143719751403570611745723 120215579627105355917618585)
      ·
        refine ⟨90161684720329016938213939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120215579627105355917618585 90161684720329016938213939)
        ·
          refine ⟨135242527080493525407320909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90161684720329016938213939 135242527080493525407320909)
          ·
            refine ⟨50715947655185072027745341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135242527080493525407320909 50715947655185072027745341)
            ·
              refine ⟨19018480370694402010404503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50715947655185072027745341 19018480370694402010404503)
              ·
                refine ⟨28527720556041603015606755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19018480370694402010404503 28527720556041603015606755)
                ·
                  refine ⟨42791580834062404523410133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28527720556041603015606755 42791580834062404523410133)
                  ·
                    refine ⟨1002927675798337606017425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42791580834062404523410133 1002927675798337606017425)
                    ·
                      rfl

theorem cell22_2929792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_2929792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929792 prefixEnd_2929792 := by exact prefixLift 2929792
  have htrace : WordTrace (prefixWord ++ tailWord_2929792) baseStart_2929792 baseEnd_2929792 := by
    simpa [prefixWord, tailWord_2929792, baseEnd_2929792] using wordTrace_append hprefix tailTrace_2929792
  have hstable : (prefixWord ++ tailWord_2929792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929792).length < 2 ^ (prefixWord ++ tailWord_2929792).sum := by decide
  have hdescent : baseEnd_2929792 < baseStart_2929792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929901 : List Nat := [1, 5, 1, 2, 2, 2, 2, 7]
def baseStart_2929901 : Nat := 118140960795 + 2929901 * 2 ^ 59
def prefixEnd_2929901 : Nat := 4983230072969 + 3 ^ 40 * 2929901 * 2
def baseEnd_2929901 : Nat := 111440554302877517226899

theorem tailTrace_2929901 : CollatzResearch.WordTrace tailWord_2929901 prefixEnd_2929901 111440554302877517226899 := by
  unfold tailWord_2929901
  simp only [CollatzResearch.WordTrace]
  refine ⟨106862268558476539098045557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71241512372317692732030371 106862268558476539098045557)
  ·
    refine ⟨10018337677357175540441771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106862268558476539098045557 10018337677357175540441771)
    ·
      refine ⟨15027506516035763310662657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10018337677357175540441771 15027506516035763310662657)
      ·
        refine ⟨11270629887026822482996993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15027506516035763310662657 11270629887026822482996993)
        ·
          refine ⟨8452972415270116862247745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11270629887026822482996993 8452972415270116862247745)
          ·
            refine ⟨6339729311452587646685809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8452972415270116862247745 6339729311452587646685809)
            ·
              refine ⟨4754796983589440735014357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6339729311452587646685809 4754796983589440735014357)
              ·
                refine ⟨111440554302877517226899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4754796983589440735014357 111440554302877517226899)
                ·
                  rfl

theorem cell22_2929901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 7].length) (baseStart_2929901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929901 prefixEnd_2929901 := by exact prefixLift 2929901
  have htrace : WordTrace (prefixWord ++ tailWord_2929901) baseStart_2929901 baseEnd_2929901 := by
    simpa [prefixWord, tailWord_2929901, baseEnd_2929901] using wordTrace_append hprefix tailTrace_2929901
  have hstable : (prefixWord ++ tailWord_2929901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929901).length < 2 ^ (prefixWord ++ tailWord_2929901).sum := by decide
  have hdescent : baseEnd_2929901 < baseStart_2929901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929946 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_2929946 : Nat := 118140960795 + 2929946 * 2 ^ 59
def prefixEnd_2929946 : Nat := 4983230072969 + 3 ^ 40 * 2929946 * 2
def baseEnd_2929946 : Nat := 334326797715177512555651

theorem tailTrace_2929946 : CollatzResearch.WordTrace tailWord_2929946 prefixEnd_2929946 334326797715177512555651 := by
  unfold tailWord_2929946
  simp only [CollatzResearch.WordTrace]
  refine ⟨26715977460828377945858423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71242606562209007855622461 26715977460828377945858423)
  ·
    refine ⟨40073966191242566918787635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26715977460828377945858423 40073966191242566918787635)
    ·
      refine ⟨60110949286863850378181453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40073966191242566918787635 60110949286863850378181453)
      ·
        refine ⟨22541605982573943891818045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60110949286863850378181453 22541605982573943891818045)
        ·
          refine ⟨8453102243465228959431767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22541605982573943891818045 8453102243465228959431767)
          ·
            refine ⟨12679653365197843439147651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8453102243465228959431767 12679653365197843439147651)
            ·
              refine ⟨19019480047796765158721477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12679653365197843439147651 19019480047796765158721477)
              ·
                refine ⟨3566152508961893467260277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19019480047796765158721477 3566152508961893467260277)
                ·
                  refine ⟨334326797715177512555651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3566152508961893467260277 334326797715177512555651)
                  ·
                    rfl

theorem cell22_2929946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_2929946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929946 prefixEnd_2929946 := by exact prefixLift 2929946
  have htrace : WordTrace (prefixWord ++ tailWord_2929946) baseStart_2929946 baseEnd_2929946 := by
    simpa [prefixWord, tailWord_2929946, baseEnd_2929946] using wordTrace_append hprefix tailTrace_2929946
  have hstable : (prefixWord ++ tailWord_2929946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929946).length < 2 ^ (prefixWord ++ tailWord_2929946).sum := by decide
  have hdescent : baseEnd_2929946 < baseStart_2929946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929976 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_2929976 : Nat := 118140960795 + 2929976 * 2 ^ 59
def prefixEnd_2929976 : Nat := 4983230072969 + 3 ^ 40 * 2929976 * 2
def baseEnd_2929976 : Nat := 1002990662758622459416861

theorem tailTrace_2929976 : CollatzResearch.WordTrace tailWord_2929976 prefixEnd_2929976 1002990662758622459416861 := by
  unfold tailWord_2929976
  simp only [CollatzResearch.WordTrace]
  refine ⟨53432502016602413453512891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71243336022136551271350521 53432502016602413453512891)
  ·
    refine ⟨80148753024903620180269337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53432502016602413453512891 80148753024903620180269337)
    ·
      refine ⟨60111564768677715135202003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80148753024903620180269337 60111564768677715135202003)
      ·
        refine ⟨90167347153016572702803005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60111564768677715135202003 90167347153016572702803005)
        ·
          refine ⟨33812755182381214763551127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90167347153016572702803005 33812755182381214763551127)
          ·
            refine ⟨50719132773571822145326691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33812755182381214763551127 50719132773571822145326691)
            ·
              refine ⟨76078699160357733217990037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50719132773571822145326691 76078699160357733217990037)
              ·
                refine ⟨3566189023141768744593283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76078699160357733217990037 3566189023141768744593283)
                ·
                  refine ⟨5349283534712653116889925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566189023141768744593283 5349283534712653116889925)
                  ·
                    refine ⟨1002990662758622459416861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5349283534712653116889925 1002990662758622459416861)
                    ·
                      rfl

theorem cell22_2929976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_2929976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929976 prefixEnd_2929976 := by exact prefixLift 2929976
  have htrace : WordTrace (prefixWord ++ tailWord_2929976) baseStart_2929976 baseEnd_2929976 := by
    simpa [prefixWord, tailWord_2929976, baseEnd_2929976] using wordTrace_append hprefix tailTrace_2929976
  have hstable : (prefixWord ++ tailWord_2929976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929976).length < 2 ^ (prefixWord ++ tailWord_2929976).sum := by decide
  have hdescent : baseEnd_2929976 < baseStart_2929976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929993 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 1, 4]
def baseStart_2929993 : Nat := 118140960795 + 2929993 * 2 ^ 59
def prefixEnd_2929993 : Nat := 4983230072969 + 3 ^ 40 * 2929993 * 2
def baseEnd_2929993 : Nat := 1002996482206040081741809

theorem tailTrace_2929993 : CollatzResearch.WordTrace tailWord_2929993 prefixEnd_2929993 1002996482206040081741809 := by
  unfold tailWord_2929993
  simp only [CollatzResearch.WordTrace]
  refine ⟨106865624074143238810394633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71243749382762159206929755 106865624074143238810394633)
  ·
    refine ⟨80149218055607429107795975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106865624074143238810394633 80149218055607429107795975)
    ·
      refine ⟨120223827083411143661693963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80149218055607429107795975 120223827083411143661693963)
      ·
        refine ⟨180335740625116715492540945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120223827083411143661693963 180335740625116715492540945)
        ·
          refine ⟨135251805468837536619405709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180335740625116715492540945 135251805468837536619405709)
          ·
            refine ⟨50719427050814076232277141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135251805468837536619405709 50719427050814076232277141)
            ·
              refine ⟨2377473143006909823387991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50719427050814076232277141 2377473143006909823387991)
              ·
                refine ⟨3566209714510364735081987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377473143006909823387991 3566209714510364735081987)
                ·
                  refine ⟨5349314571765547102622981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566209714510364735081987 5349314571765547102622981)
                  ·
                    refine ⟨1002996482206040081741809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5349314571765547102622981 1002996482206040081741809)
                    ·
                      rfl

theorem cell22_2929993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 4].length) (baseStart_2929993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929993 prefixEnd_2929993 := by exact prefixLift 2929993
  have htrace : WordTrace (prefixWord ++ tailWord_2929993) baseStart_2929993 baseEnd_2929993 := by
    simpa [prefixWord, tailWord_2929993, baseEnd_2929993] using wordTrace_append hprefix tailTrace_2929993
  have hstable : (prefixWord ++ tailWord_2929993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929993).length < 2 ^ (prefixWord ++ tailWord_2929993).sum := by decide
  have hdescent : baseEnd_2929993 < baseStart_2929993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929997 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2929997 : Nat := 118140960795 + 2929997 * 2 ^ 59
def prefixEnd_2929997 : Nat := 4983230072969 + 3 ^ 40 * 2929997 * 2
def baseEnd_2929997 : Nat := 334332617162595134880599

theorem tailTrace_2929997 : CollatzResearch.WordTrace tailWord_2929997 prefixEnd_2929997 334332617162595134880599 := by
  unfold tailWord_2929997
  simp only [CollatzResearch.WordTrace]
  refine ⟨106865769966128747493540245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71243846644085831662360163 106865769966128747493540245)
  ·
    refine ⟨5009332967162285038759699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106865769966128747493540245 5009332967162285038759699)
    ·
      refine ⟨7513999450743427558139549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5009332967162285038759699 7513999450743427558139549)
      ·
        refine ⟨2817749794028785334302331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7513999450743427558139549 2817749794028785334302331)
        ·
          refine ⟨4226624691043178001453497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2817749794028785334302331 4226624691043178001453497)
          ·
            refine ⟨3169968518282383501090123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4226624691043178001453497 3169968518282383501090123)
            ·
              refine ⟨4754952777423575251635185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3169968518282383501090123 4754952777423575251635185)
              ·
                refine ⟨3566214583067681438726389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4754952777423575251635185 3566214583067681438726389)
                ·
                  refine ⟨334332617162595134880599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3566214583067681438726389 334332617162595134880599)
                  ·
                    rfl

theorem cell22_2929997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2929997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2929997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2929997 prefixEnd_2929997 := by exact prefixLift 2929997
  have htrace : WordTrace (prefixWord ++ tailWord_2929997) baseStart_2929997 baseEnd_2929997 := by
    simpa [prefixWord, tailWord_2929997, baseEnd_2929997] using wordTrace_append hprefix tailTrace_2929997
  have hstable : (prefixWord ++ tailWord_2929997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929997).length < 2 ^ (prefixWord ++ tailWord_2929997).sum := by decide
  have hdescent : baseEnd_2929997 < baseStart_2929997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930158 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2930158 : Nat := 118140960795 + 2930158 * 2 ^ 59
def prefixEnd_2930158 : Nat := 4983230072969 + 3 ^ 40 * 2930158 * 2
def baseEnd_2930158 : Nat := 1003052965078034651366303

theorem tailTrace_2930158 : CollatzResearch.WordTrace tailWord_2930158 prefixEnd_2930158 1003052965078034651366303 := by
  unfold tailWord_2930158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13358955264818183998768891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71247761412363647993434085 13358955264818183998768891)
  ·
    refine ⟨20038432897227275998153337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13358955264818183998768891 20038432897227275998153337)
    ·
      refine ⟨15028824672920456998615003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20038432897227275998153337 15028824672920456998615003)
      ·
        refine ⟨22543237009380685497922505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15028824672920456998615003 22543237009380685497922505)
        ·
          refine ⟨16907427757035514123441879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22543237009380685497922505 16907427757035514123441879)
          ·
            refine ⟨25361141635553271185162819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16907427757035514123441879 25361141635553271185162819)
            ·
              refine ⟨38041712453329906777744229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25361141635553271185162819 38041712453329906777744229)
              ·
                refine ⟨7132821084999357520827043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38041712453329906777744229 7132821084999357520827043)
                ·
                  refine ⟨10699231627499036281240565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7132821084999357520827043 10699231627499036281240565)
                  ·
                    refine ⟨1003052965078034651366303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10699231627499036281240565 1003052965078034651366303)
                    ·
                      rfl

theorem cell22_2930158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2930158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930158 prefixEnd_2930158 := by exact prefixLift 2930158
  have htrace : WordTrace (prefixWord ++ tailWord_2930158) baseStart_2930158 baseEnd_2930158 := by
    simpa [prefixWord, tailWord_2930158, baseEnd_2930158] using wordTrace_append hprefix tailTrace_2930158
  have hstable : (prefixWord ++ tailWord_2930158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930158).length < 2 ^ (prefixWord ++ tailWord_2930158).sum := by decide
  have hdescent : baseEnd_2930158 < baseStart_2930158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930160 : List Nat := [2, 1, 1, 1, 3, 5, 2, 3, 4]
def baseStart_2930160 : Nat := 118140960795 + 2930160 * 2 ^ 59
def prefixEnd_2930160 : Nat := 4983230072969 + 3 ^ 40 * 2930160 * 2
def baseEnd_2930160 : Nat := 334351216572969104272099

theorem tailTrace_2930160 : CollatzResearch.WordTrace tailWord_2930160 prefixEnd_2930160 334351216572969104272099 := by
  unfold tailWord_2930160
  simp only [CollatzResearch.WordTrace]
  refine ⟨53435857532269113165861967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71247810043025484221149289 53435857532269113165861967)
  ·
    refine ⟨80153786298403669748792951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53435857532269113165861967 80153786298403669748792951)
    ·
      refine ⟨120230679447605504623189427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80153786298403669748792951 120230679447605504623189427)
      ·
        refine ⟨180346019171408256934784141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120230679447605504623189427 180346019171408256934784141)
        ·
          refine ⟨67629757189278096350544053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180346019171408256934784141 67629757189278096350544053)
          ·
            refine ⟨6340289736494821532863505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67629757189278096350544053 6340289736494821532863505)
            ·
              refine ⟨4755217302371116149647629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340289736494821532863505 4755217302371116149647629)
              ·
                refine ⟨1783206488389168556117861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4755217302371116149647629 1783206488389168556117861)
                ·
                  refine ⟨334351216572969104272099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1783206488389168556117861 334351216572969104272099)
                  ·
                    rfl

theorem cell22_2930160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 4].length) (baseStart_2930160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930160 prefixEnd_2930160 := by exact prefixLift 2930160
  have htrace : WordTrace (prefixWord ++ tailWord_2930160) baseStart_2930160 baseEnd_2930160 := by
    simpa [prefixWord, tailWord_2930160, baseEnd_2930160] using wordTrace_append hprefix tailTrace_2930160
  have hstable : (prefixWord ++ tailWord_2930160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930160).length < 2 ^ (prefixWord ++ tailWord_2930160).sum := by decide
  have hdescent : baseEnd_2930160 < baseStart_2930160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930162 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_2930162 : Nat := 118140960795 + 2930162 * 2 ^ 59
def prefixEnd_2930162 : Nat := 4983230072969 + 3 ^ 40 * 2930162 * 2
def baseEnd_2930162 : Nat := 1003054334359779974266291

theorem tailTrace_2930162 : CollatzResearch.WordTrace tailWord_2930162 prefixEnd_2930162 1003054334359779974266291 := by
  unfold tailWord_2930162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26717947002632745168324185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71247858673687320448864493 26717947002632745168324185)
  ·
    refine ⟨20038460251974558876243139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26717947002632745168324185 20038460251974558876243139)
    ·
      refine ⟨30057690377961838314364709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20038460251974558876243139 30057690377961838314364709)
      ·
        refine ⟨5635816945867844683943383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30057690377961838314364709 5635816945867844683943383)
        ·
          refine ⟨8453725418801767025915075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5635816945867844683943383 8453725418801767025915075)
          ·
            refine ⟨12680588128202650538872613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8453725418801767025915075 12680588128202650538872613)
            ·
              refine ⟨2377610274037996976038615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12680588128202650538872613 2377610274037996976038615)
              ·
                refine ⟨3566415411056995464057923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377610274037996976038615 3566415411056995464057923)
                ·
                  refine ⟨5349623116585493196086885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566415411056995464057923 5349623116585493196086885)
                  ·
                    refine ⟨1003054334359779974266291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5349623116585493196086885 1003054334359779974266291)
                    ·
                      rfl

theorem cell22_2930162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_2930162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930162 prefixEnd_2930162 := by exact prefixLift 2930162
  have htrace : WordTrace (prefixWord ++ tailWord_2930162) baseStart_2930162 baseEnd_2930162 := by
    simpa [prefixWord, tailWord_2930162, baseEnd_2930162] using wordTrace_append hprefix tailTrace_2930162
  have hstable : (prefixWord ++ tailWord_2930162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930162).length < 2 ^ (prefixWord ++ tailWord_2930162).sum := by decide
  have hdescent : baseEnd_2930162 < baseStart_2930162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930233 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 7]
def baseStart_2930233 : Nat := 118140960795 + 2930233 * 2 ^ 59
def prefixEnd_2930233 : Nat := 4983230072969 + 3 ^ 40 * 2930233 * 2
def baseEnd_2930233 : Nat := 334359546370253151913691

theorem tailTrace_2930233 : CollatzResearch.WordTrace tailWord_2930233 prefixEnd_2930233 334359546370253151913691 := by
  unfold tailWord_2930233
  simp only [CollatzResearch.WordTrace]
  refine ⟨106874377593273759799131353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71249585062182506532754235 106874377593273759799131353)
  ·
    refine ⟨80155783194955319849348515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106874377593273759799131353 80155783194955319849348515)
    ·
      refine ⟨120233674792432979774022773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80155783194955319849348515 120233674792432979774022773)
      ·
        refine ⟨11271907011790591853814635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120233674792432979774022773 11271907011790591853814635)
        ·
          refine ⟨16907860517685887780721953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11271907011790591853814635 16907860517685887780721953)
          ·
            refine ⟨12680895388264415835541465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16907860517685887780721953 12680895388264415835541465)
            ·
              refine ⟨9510671541198311876656099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12680895388264415835541465 9510671541198311876656099)
              ·
                refine ⟨14266007311797467814984149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9510671541198311876656099 14266007311797467814984149)
                ·
                  refine ⟨334359546370253151913691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14266007311797467814984149 334359546370253151913691)
                  ·
                    rfl

theorem cell22_2930233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_2930233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930233 prefixEnd_2930233 := by exact prefixLift 2930233
  have htrace : WordTrace (prefixWord ++ tailWord_2930233) baseStart_2930233 baseEnd_2930233 := by
    simpa [prefixWord, tailWord_2930233, baseEnd_2930233] using wordTrace_append hprefix tailTrace_2930233
  have hstable : (prefixWord ++ tailWord_2930233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930233).length < 2 ^ (prefixWord ++ tailWord_2930233).sum := by decide
  have hdescent : baseEnd_2930233 < baseStart_2930233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930312 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 6]
def baseStart_2930312 : Nat := 118140960795 + 2930312 * 2 ^ 59
def prefixEnd_2930312 : Nat := 4983230072969 + 3 ^ 40 * 2930312 * 2
def baseEnd_2930312 : Nat := 334368560808409861005277

theorem tailTrace_2930312 : CollatzResearch.WordTrace tailWord_2930312 prefixEnd_2930312 334368560808409861005277 := by
  unfold tailWord_2930312
  simp only [CollatzResearch.WordTrace]
  refine ⟨53438629479993778145628595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71251505973325037527504793 53438629479993778145628595)
  ·
    refine ⟨80157944219990667218442893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53438629479993778145628595 80157944219990667218442893)
    ·
      refine ⟨30059229082496500206916085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80157944219990667218442893 30059229082496500206916085)
      ·
        refine ⟨2818052726484046894398383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30059229082496500206916085 2818052726484046894398383)
        ·
          refine ⟨4227079089726070341597575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818052726484046894398383 4227079089726070341597575)
          ·
            refine ⟨6340618634589105512396363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227079089726070341597575 6340618634589105512396363)
            ·
              refine ⟨9510927951883658268594545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6340618634589105512396363 9510927951883658268594545)
              ·
                refine ⟨7133195963912743701445909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9510927951883658268594545 7133195963912743701445909)
                ·
                  refine ⟨334368560808409861005277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7133195963912743701445909 334368560808409861005277)
                  ·
                    rfl

theorem cell22_2930312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_2930312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930312 prefixEnd_2930312 := by exact prefixLift 2930312
  have htrace : WordTrace (prefixWord ++ tailWord_2930312) baseStart_2930312 baseEnd_2930312 := by
    simpa [prefixWord, tailWord_2930312, baseEnd_2930312] using wordTrace_append hprefix tailTrace_2930312
  have hstable : (prefixWord ++ tailWord_2930312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930312).length < 2 ^ (prefixWord ++ tailWord_2930312).sum := by decide
  have hdescent : baseEnd_2930312 < baseStart_2930312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930372 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2930372 : Nat := 118140960795 + 2930372 * 2 ^ 59
def prefixEnd_2930372 : Nat := 4983230072969 + 3 ^ 40 * 2930372 * 2
def baseEnd_2930372 : Nat := 1003126221651409426515647

theorem tailTrace_2930372 : CollatzResearch.WordTrace tailWord_2930372 prefixEnd_2930372 1003126221651409426515647 := by
  unfold tailWord_2930372
  simp only [CollatzResearch.WordTrace]
  refine ⟨53439723669885093269220685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71252964893180124358960913 53439723669885093269220685)
  ·
    refine ⟨20039896376206909975957757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53439723669885093269220685 20039896376206909975957757)
    ·
      refine ⟨7514961141077591240984159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20039896376206909975957757 7514961141077591240984159)
      ·
        refine ⟨11272441711616386861476239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7514961141077591240984159 11272441711616386861476239)
        ·
          refine ⟨16908662567424580292214359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11272441711616386861476239 16908662567424580292214359)
          ·
            refine ⟨25362993851136870438321539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16908662567424580292214359 25362993851136870438321539)
            ·
              refine ⟨38044490776705305657482309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25362993851136870438321539 38044490776705305657482309)
              ·
                refine ⟨7133342020632244810777933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38044490776705305657482309 7133342020632244810777933)
                ·
                  refine ⟨2675003257737091804041725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7133342020632244810777933 2675003257737091804041725)
                  ·
                    refine ⟨1003126221651409426515647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2675003257737091804041725 1003126221651409426515647)
                    ·
                      rfl

theorem cell22_2930372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2930372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930372 prefixEnd_2930372 := by exact prefixLift 2930372
  have htrace : WordTrace (prefixWord ++ tailWord_2930372) baseStart_2930372 baseEnd_2930372 := by
    simpa [prefixWord, tailWord_2930372, baseEnd_2930372] using wordTrace_append hprefix tailTrace_2930372
  have hstable : (prefixWord ++ tailWord_2930372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930372).length < 2 ^ (prefixWord ++ tailWord_2930372).sum := by decide
  have hdescent : baseEnd_2930372 < baseStart_2930372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930374 : List Nat := [6, 1, 2, 1, 1, 2, 1, 8]
def baseStart_2930374 : Nat := 118140960795 + 2930374 * 2 ^ 59
def prefixEnd_2930374 : Nat := 4983230072969 + 3 ^ 40 * 2930374 * 2
def baseEnd_2930374 : Nat := 111458545143586898662849

theorem tailTrace_2930374 : CollatzResearch.WordTrace tailWord_2930374 prefixEnd_2930374 111458545143586898662849 := by
  unfold tailWord_2930374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339985008930091902500443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71253013523841960586676117 3339985008930091902500443)
  ·
    refine ⟨5009977513395137853750665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3339985008930091902500443 5009977513395137853750665)
    ·
      refine ⟨3757483135046353390312999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5009977513395137853750665 3757483135046353390312999)
      ·
        refine ⟨5636224702569530085469499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757483135046353390312999 5636224702569530085469499)
        ·
          refine ⟨8454337053854295128204249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636224702569530085469499 8454337053854295128204249)
          ·
            refine ⟨6340752790390721346153187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8454337053854295128204249 6340752790390721346153187)
            ·
              refine ⟨9511129185586082019229781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6340752790390721346153187 9511129185586082019229781)
              ·
                refine ⟨111458545143586898662849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9511129185586082019229781 111458545143586898662849)
                ·
                  rfl

theorem cell22_2930374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_2930374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930374 prefixEnd_2930374 := by exact prefixLift 2930374
  have htrace : WordTrace (prefixWord ++ tailWord_2930374) baseStart_2930374 baseEnd_2930374 := by
    simpa [prefixWord, tailWord_2930374, baseEnd_2930374] using wordTrace_append hprefix tailTrace_2930374
  have hstable : (prefixWord ++ tailWord_2930374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930374).length < 2 ^ (prefixWord ++ tailWord_2930374).sum := by decide
  have hdescent : baseEnd_2930374 < baseStart_2930374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930383 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 1, 7]
def baseStart_2930383 : Nat := 118140960795 + 2930383 * 2 ^ 59
def prefixEnd_2930383 : Nat := 4983230072969 + 3 ^ 40 * 2930383 * 2
def baseEnd_2930383 : Nat := 1003129987176209064490613

theorem tailTrace_2930383 : CollatzResearch.WordTrace tailWord_2930383 prefixEnd_2930383 1003129987176209064490613 := by
  unfold tailWord_2930383
  simp only [CollatzResearch.WordTrace]
  refine ⟨106879848542730335417091803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71253232361820223611394535 106879848542730335417091803)
  ·
    refine ⟨160319772814095503125637705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106879848542730335417091803 160319772814095503125637705)
    ·
      refine ⟨120239829610571627344228279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160319772814095503125637705 120239829610571627344228279)
      ·
        refine ⟨180359744415857441016342419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120239829610571627344228279 180359744415857441016342419)
        ·
          refine ⟨270539616623786161524513629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180359744415857441016342419 270539616623786161524513629)
          ·
            refine ⟨101452356233919810571692611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270539616623786161524513629 101452356233919810571692611)
            ·
              refine ⟨152178534350879715857538917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101452356233919810571692611 152178534350879715857538917)
              ·
                refine ⟨28533475190789946723288547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152178534350879715857538917 28533475190789946723288547)
                ·
                  refine ⟨42800212786184920084932821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28533475190789946723288547 42800212786184920084932821)
                  ·
                    refine ⟨1003129987176209064490613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42800212786184920084932821 1003129987176209064490613)
                    ·
                      rfl

theorem cell22_2930383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_2930383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930383 prefixEnd_2930383 := by exact prefixLift 2930383
  have htrace : WordTrace (prefixWord ++ tailWord_2930383) baseStart_2930383 baseEnd_2930383 := by
    simpa [prefixWord, tailWord_2930383, baseEnd_2930383] using wordTrace_append hprefix tailTrace_2930383
  have hstable : (prefixWord ++ tailWord_2930383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930383).length < 2 ^ (prefixWord ++ tailWord_2930383).sum := by decide
  have hdescent : baseEnd_2930383 < baseStart_2930383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930415 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 3, 4]
def baseStart_2930415 : Nat := 118140960795 + 2930415 * 2 ^ 59
def prefixEnd_2930415 : Nat := 4983230072969 + 3 ^ 40 * 2930415 * 2
def baseEnd_2930415 : Nat := 1003140941430171647690515

theorem tailTrace_2930415 : CollatzResearch.WordTrace tailWord_2930415 prefixEnd_2930415 1003140941430171647690515 := by
  unfold tailWord_2930415
  simp only [CollatzResearch.WordTrace]
  refine ⟨106881015678614404882256699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71254010452409603254837799 106881015678614404882256699)
  ·
    refine ⟨160321523517921607323385049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106881015678614404882256699 160321523517921607323385049)
    ·
      refine ⟨120241142638441205492538787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160321523517921607323385049 120241142638441205492538787)
      ·
        refine ⟨180361713957661808238808181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120241142638441205492538787 180361713957661808238808181)
        ·
          refine ⟨16908910683530794522388267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180361713957661808238808181 16908910683530794522388267)
          ·
            refine ⟨25363366025296191783582401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16908910683530794522388267 25363366025296191783582401)
            ·
              refine ⟨19022524518972143837686801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25363366025296191783582401 19022524518972143837686801)
              ·
                refine ⟨14266893389229107878265101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19022524518972143837686801 14266893389229107878265101)
                ·
                  refine ⟨5350085020960915454349413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14266893389229107878265101 5350085020960915454349413)
                  ·
                    refine ⟨1003140941430171647690515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350085020960915454349413 1003140941430171647690515)
                    ·
                      rfl

theorem cell22_2930415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_2930415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930415 prefixEnd_2930415 := by exact prefixLift 2930415
  have htrace : WordTrace (prefixWord ++ tailWord_2930415) baseStart_2930415 baseEnd_2930415 := by
    simpa [prefixWord, tailWord_2930415, baseEnd_2930415] using wordTrace_append hprefix tailTrace_2930415
  have hstable : (prefixWord ++ tailWord_2930415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930415).length < 2 ^ (prefixWord ++ tailWord_2930415).sum := by decide
  have hdescent : baseEnd_2930415 < baseStart_2930415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930494 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2930494 : Nat := 118140960795 + 2930494 * 2 ^ 59
def prefixEnd_2930494 : Nat := 4983230072969 + 3 ^ 40 * 2930494 * 2
def baseEnd_2930494 : Nat := 1003167984744641774965273

theorem tailTrace_2930494 : CollatzResearch.WordTrace tailWord_2930494 prefixEnd_2930494 1003167984744641774965273 := by
  unfold tailWord_2930494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360487130666025171797817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71255931363552134249588357 13360487130666025171797817)
  ·
    refine ⟨10020365347999518878848363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13360487130666025171797817 10020365347999518878848363)
    ·
      refine ⟨15030548021999278318272545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10020365347999518878848363 15030548021999278318272545)
      ·
        refine ⟨11272911016499458738704409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15030548021999278318272545 11272911016499458738704409)
        ·
          refine ⟨8454683262374594054028307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11272911016499458738704409 8454683262374594054028307)
          ·
            refine ⟨12682024893561891081042461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8454683262374594054028307 12682024893561891081042461)
            ·
              refine ⟨4755759335085709155390923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12682024893561891081042461 4755759335085709155390923)
              ·
                refine ⟨7133639002628563733086385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755759335085709155390923 7133639002628563733086385)
                ·
                  refine ⟨5350229251971422799814789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7133639002628563733086385 5350229251971422799814789)
                  ·
                    refine ⟨1003167984744641774965273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350229251971422799814789 1003167984744641774965273)
                    ·
                      rfl

theorem cell22_2930494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2930494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930494 prefixEnd_2930494 := by exact prefixLift 2930494
  have htrace : WordTrace (prefixWord ++ tailWord_2930494) baseStart_2930494 baseEnd_2930494 := by
    simpa [prefixWord, tailWord_2930494, baseEnd_2930494] using wordTrace_append hprefix tailTrace_2930494
  have hstable : (prefixWord ++ tailWord_2930494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930494).length < 2 ^ (prefixWord ++ tailWord_2930494).sum := by decide
  have hdescent : baseEnd_2930494 < baseStart_2930494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930659 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 5, 3]
def baseStart_2930659 : Nat := 118140960795 + 2930659 * 2 ^ 59
def prefixEnd_2930659 : Nat := 4983230072969 + 3 ^ 40 * 2930659 * 2
def baseEnd_2930659 : Nat := 1003224467616636344589767

theorem tailTrace_2930659 : CollatzResearch.WordTrace tailWord_2930659 prefixEnd_2930659 1003224467616636344589767 := by
  unfold tailWord_2930659
  simp only [CollatzResearch.WordTrace]
  refine ⟨106889915089730434554139031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71259943393153623036092687 106889915089730434554139031)
  ·
    refine ⟨160334872634595651831208547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106889915089730434554139031 160334872634595651831208547)
    ·
      refine ⟨240502308951893477746812821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160334872634595651831208547 240502308951893477746812821)
      ·
        refine ⟨11273545732120006769381851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 240502308951893477746812821 11273545732120006769381851)
        ·
          refine ⟨16910318598180010154072777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11273545732120006769381851 16910318598180010154072777)
          ·
            refine ⟨12682738948635007615554583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16910318598180010154072777 12682738948635007615554583)
            ·
              refine ⟨19024108422952511423331875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12682738948635007615554583 19024108422952511423331875)
              ·
                refine ⟨28536162634428767134997813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19024108422952511423331875 28536162634428767134997813)
                ·
                  refine ⟨2675265246977696918906045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28536162634428767134997813 2675265246977696918906045)
                  ·
                    refine ⟨1003224467616636344589767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2675265246977696918906045 1003224467616636344589767)
                    ·
                      rfl

theorem cell22_2930659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 3].length) (baseStart_2930659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930659 prefixEnd_2930659 := by exact prefixLift 2930659
  have htrace : WordTrace (prefixWord ++ tailWord_2930659) baseStart_2930659 baseEnd_2930659 := by
    simpa [prefixWord, tailWord_2930659, baseEnd_2930659] using wordTrace_append hprefix tailTrace_2930659
  have hstable : (prefixWord ++ tailWord_2930659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930659).length < 2 ^ (prefixWord ++ tailWord_2930659).sum := by decide
  have hdescent : baseEnd_2930659 < baseStart_2930659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930663 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 2, 4]
def baseStart_2930663 : Nat := 118140960795 + 2930663 * 2 ^ 59
def prefixEnd_2930663 : Nat := 4983230072969 + 3 ^ 40 * 2930663 * 2
def baseEnd_2930663 : Nat := 1003225836898381667489755

theorem tailTrace_2930663 : CollatzResearch.WordTrace tailWord_2930663 prefixEnd_2930663 1003225836898381667489755 := by
  unfold tailWord_2930663
  simp only [CollatzResearch.WordTrace]
  refine ⟨106890060981715943237284643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71260040654477295491523095 106890060981715943237284643)
  ·
    refine ⟨160335091472573914855926965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106890060981715943237284643 160335091472573914855926965)
    ·
      refine ⟨15031414825553804517743153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160335091472573914855926965 15031414825553804517743153)
      ·
        refine ⟨11273561119165353388307365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15031414825553804517743153 11273561119165353388307365)
        ·
          refine ⟨2113792709843503760307631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11273561119165353388307365 2113792709843503760307631)
          ·
            refine ⟨3170689064765255640461447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113792709843503760307631 3170689064765255640461447)
            ·
              refine ⟨4756033597147883460692171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170689064765255640461447 4756033597147883460692171)
              ·
                refine ⟨7134050395721825191038257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756033597147883460692171 7134050395721825191038257)
                ·
                  refine ⟨5350537796791368893278693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7134050395721825191038257 5350537796791368893278693)
                  ·
                    refine ⟨1003225836898381667489755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350537796791368893278693 1003225836898381667489755)
                    ·
                      rfl

theorem cell22_2930663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_2930663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930663 prefixEnd_2930663 := by exact prefixLift 2930663
  have htrace : WordTrace (prefixWord ++ tailWord_2930663) baseStart_2930663 baseEnd_2930663 := by
    simpa [prefixWord, tailWord_2930663, baseEnd_2930663] using wordTrace_append hprefix tailTrace_2930663
  have hstable : (prefixWord ++ tailWord_2930663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930663).length < 2 ^ (prefixWord ++ tailWord_2930663).sum := by decide
  have hdescent : baseEnd_2930663 < baseStart_2930663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930727 : List Nat := [1, 1, 7, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2930727 : Nat := 118140960795 + 2930727 * 2 ^ 59
def prefixEnd_2930727 : Nat := 4983230072969 + 3 ^ 40 * 2930727 * 2
def baseEnd_2930727 : Nat := 1003247745406306833889559

theorem tailTrace_2930727 : CollatzResearch.WordTrace tailWord_2930727 prefixEnd_2930727 1003247745406306833889559 := by
  unfold tailWord_2930727
  simp only [CollatzResearch.WordTrace]
  refine ⟨106892395253484082167614435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71261596835656054778409623 106892395253484082167614435)
  ·
    refine ⟨160338592880226123251421653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106892395253484082167614435 160338592880226123251421653)
    ·
      refine ⟨3757935770630299763705195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 160338592880226123251421653 3757935770630299763705195)
      ·
        refine ⟨5636903655945449645557793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757935770630299763705195 5636903655945449645557793)
        ·
          refine ⟨4227677741959087234168345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5636903655945449645557793 4227677741959087234168345)
          ·
            refine ⟨3170758306469315425626259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4227677741959087234168345 3170758306469315425626259)
            ·
              refine ⟨4756137459703973138439389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170758306469315425626259 4756137459703973138439389)
              ·
                refine ⟨1783551547388989926914771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4756137459703973138439389 1783551547388989926914771)
                ·
                  refine ⟨2675327321083484890372157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783551547388989926914771 2675327321083484890372157)
                  ·
                    refine ⟨1003247745406306833889559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2675327321083484890372157 1003247745406306833889559)
                    ·
                      rfl

theorem cell22_2930727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2930727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930727 prefixEnd_2930727 := by exact prefixLift 2930727
  have htrace : WordTrace (prefixWord ++ tailWord_2930727) baseStart_2930727 baseEnd_2930727 := by
    simpa [prefixWord, tailWord_2930727, baseEnd_2930727] using wordTrace_append hprefix tailTrace_2930727
  have hstable : (prefixWord ++ tailWord_2930727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930727).length < 2 ^ (prefixWord ++ tailWord_2930727).sum := by decide
  have hdescent : baseEnd_2930727 < baseStart_2930727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930770 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_2930770 : Nat := 118140960795 + 2930770 * 2 ^ 59
def prefixEnd_2930770 : Nat := 4983230072969 + 3 ^ 40 * 2930770 * 2
def baseEnd_2930770 : Nat := 1003262465185069055064427

theorem tailTrace_2930770 : CollatzResearch.WordTrace tailWord_2930770 prefixEnd_2930770 1003262465185069055064427 := by
  unfold tailWord_2930770
  simp only [CollatzResearch.WordTrace]
  refine ⟨26723490898082075127857441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71262642394885533674286509 26723490898082075127857441)
  ·
    refine ⟨20042618173561556345893081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26723490898082075127857441 20042618173561556345893081)
    ·
      refine ⟨15031963630171167259419811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20042618173561556345893081 15031963630171167259419811)
      ·
        refine ⟨22547945445256750889129717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15031963630171167259419811 22547945445256750889129717)
        ·
          refine ⟨2113869885492820395855911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22547945445256750889129717 2113869885492820395855911)
          ·
            refine ⟨3170804828239230593783867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113869885492820395855911 3170804828239230593783867)
            ·
              refine ⟨4756207242358845890675801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170804828239230593783867 4756207242358845890675801)
              ·
                refine ⟨3567155431769134418006851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4756207242358845890675801 3567155431769134418006851)
                ·
                  refine ⟨5350733147653701627010277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567155431769134418006851 5350733147653701627010277)
                  ·
                    refine ⟨1003262465185069055064427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350733147653701627010277 1003262465185069055064427)
                    ·
                      rfl

theorem cell22_2930770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_2930770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930770 prefixEnd_2930770 := by exact prefixLift 2930770
  have htrace : WordTrace (prefixWord ++ tailWord_2930770) baseStart_2930770 baseEnd_2930770 := by
    simpa [prefixWord, tailWord_2930770, baseEnd_2930770] using wordTrace_append hprefix tailTrace_2930770
  have hstable : (prefixWord ++ tailWord_2930770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930770).length < 2 ^ (prefixWord ++ tailWord_2930770).sum := by decide
  have hdescent : baseEnd_2930770 < baseStart_2930770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930809 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_2930809 : Nat := 118140960795 + 2930809 * 2 ^ 59
def prefixEnd_2930809 : Nat := 4983230072969 + 3 ^ 40 * 2930809 * 2
def baseEnd_2930809 : Nat := 1003275815682085953339307

theorem tailTrace_2930809 : CollatzResearch.WordTrace tailWord_2930809 prefixEnd_2930809 1003275815682085953339307 := by
  unfold tailWord_2930809
  simp only [CollatzResearch.WordTrace]
  refine ⟨106895386039187010172099481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71263590692791340114732987 106895386039187010172099481)
  ·
    refine ⟨80171539529390257629074611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106895386039187010172099481 80171539529390257629074611)
    ·
      refine ⟨120257309294085386443611917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80171539529390257629074611 120257309294085386443611917)
      ·
        refine ⟨45096490985282019916354469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120257309294085386443611917 45096490985282019916354469)
        ·
          refine ⟨8455592059740378734316463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45096490985282019916354469 8455592059740378734316463)
          ·
            refine ⟨12683388089610568101474695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8455592059740378734316463 12683388089610568101474695)
            ·
              refine ⟨19025082134415852152212043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12683388089610568101474695 19025082134415852152212043)
              ·
                refine ⟨28537623201623778228318065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19025082134415852152212043 28537623201623778228318065)
                ·
                  refine ⟨21403217401217833671238549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28537623201623778228318065 21403217401217833671238549)
                  ·
                    refine ⟨1003275815682085953339307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21403217401217833671238549 1003275815682085953339307)
                    ·
                      rfl

theorem cell22_2930809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_2930809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930809 prefixEnd_2930809 := by exact prefixLift 2930809
  have htrace : WordTrace (prefixWord ++ tailWord_2930809) baseStart_2930809 baseEnd_2930809 := by
    simpa [prefixWord, tailWord_2930809, baseEnd_2930809] using wordTrace_append hprefix tailTrace_2930809
  have hstable : (prefixWord ++ tailWord_2930809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930809).length < 2 ^ (prefixWord ++ tailWord_2930809).sum := by decide
  have hdescent : baseEnd_2930809 < baseStart_2930809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930838 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2930838 : Nat := 118140960795 + 2930838 * 2 ^ 59
def prefixEnd_2930838 : Nat := 4983230072969 + 3 ^ 40 * 2930838 * 2
def baseEnd_2930838 : Nat := 1003285742974739544364219

theorem tailTrace_2930838 : CollatzResearch.WordTrace tailWord_2930838 prefixEnd_2930838 1003285742974739544364219 := by
  unfold tailWord_2930838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6681027734755121757806573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71264295837387965416603445 6681027734755121757806573)
  ·
    refine ⟨2505385400533170659177465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6681027734755121757806573 2505385400533170659177465)
    ·
      refine ⟨1879039050399877994383099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2505385400533170659177465 1879039050399877994383099)
      ·
        refine ⟨2818558575599816991574649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879039050399877994383099 2818558575599816991574649)
        ·
          refine ⟨2113918931699862743680987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2818558575599816991574649 2113918931699862743680987)
          ·
            refine ⟨3170878397549794115521481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2113918931699862743680987 3170878397549794115521481)
            ·
              refine ⟨2378158798162345586641111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3170878397549794115521481 2378158798162345586641111)
              ·
                refine ⟨3567238197243518379961667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378158798162345586641111 3567238197243518379961667)
                ·
                  refine ⟨5350857295865277569942501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567238197243518379961667 5350857295865277569942501)
                  ·
                    refine ⟨1003285742974739544364219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350857295865277569942501 1003285742974739544364219)
                    ·
                      rfl

theorem cell22_2930838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2930838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930838 prefixEnd_2930838 := by exact prefixLift 2930838
  have htrace : WordTrace (prefixWord ++ tailWord_2930838) baseStart_2930838 baseEnd_2930838 := by
    simpa [prefixWord, tailWord_2930838, baseEnd_2930838] using wordTrace_append hprefix tailTrace_2930838
  have hstable : (prefixWord ++ tailWord_2930838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930838).length < 2 ^ (prefixWord ++ tailWord_2930838).sum := by decide
  have hdescent : baseEnd_2930838 < baseStart_2930838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930845 : List Nat := [1, 4, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2930845 : Nat := 118140960795 + 2930845 * 2 ^ 59
def prefixEnd_2930845 : Nat := 4983230072969 + 3 ^ 40 * 2930845 * 2
def baseEnd_2930845 : Nat := 1003288139217793859439197

theorem tailTrace_2930845 : CollatzResearch.WordTrace tailWord_2930845 prefixEnd_2930845 1003288139217793859439197 := by
  unfold tailWord_2930845
  simp only [CollatzResearch.WordTrace]
  refine ⟨106896699067056588320409989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71264466044704392213606659 106896699067056588320409989)
  ·
    refine ⟨20043131075073110310076873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106896699067056588320409989 20043131075073110310076873)
    ·
      refine ⟨15032348306304832732557655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20043131075073110310076873 15032348306304832732557655)
      ·
        refine ⟨22548522459457249098836483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15032348306304832732557655 22548522459457249098836483)
        ·
          refine ⟨33822783689185873648254725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22548522459457249098836483 33822783689185873648254725)
          ·
            refine ⟨6341771941722351309047761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33822783689185873648254725 6341771941722351309047761)
            ·
              refine ⟨4756328956291763481785821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6341771941722351309047761 4756328956291763481785821)
              ·
                refine ⟨1783623358609411305669683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4756328956291763481785821 1783623358609411305669683)
                ·
                  refine ⟨2675435037914116958504525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783623358609411305669683 2675435037914116958504525)
                  ·
                    refine ⟨1003288139217793859439197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2675435037914116958504525 1003288139217793859439197)
                    ·
                      rfl

theorem cell22_2930845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2930845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930845 prefixEnd_2930845 := by exact prefixLift 2930845
  have htrace : WordTrace (prefixWord ++ tailWord_2930845) baseStart_2930845 baseEnd_2930845 := by
    simpa [prefixWord, tailWord_2930845, baseEnd_2930845] using wordTrace_append hprefix tailTrace_2930845
  have hstable : (prefixWord ++ tailWord_2930845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930845).length < 2 ^ (prefixWord ++ tailWord_2930845).sum := by decide
  have hdescent : baseEnd_2930845 < baseStart_2930845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930858 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_2930858 : Nat := 118140960795 + 2930858 * 2 ^ 59
def prefixEnd_2930858 : Nat := 4983230072969 + 3 ^ 40 * 2930858 * 2
def baseEnd_2930858 : Nat := 334430863127822052954719

theorem tailTrace_2930858 : CollatzResearch.WordTrace tailWord_2930858 prefixEnd_2930858 334430863127822052954719 := by
  unfold tailWord_2930858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26724293304002372885158307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71264782144006327693755485 26724293304002372885158307)
  ·
    refine ⟨40086439956003559327737461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26724293304002372885158307 40086439956003559327737461)
    ·
      refine ⟨3758103745875333686975387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40086439956003559327737461 3758103745875333686975387)
      ·
        refine ⟨5637155618813000530463081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758103745875333686975387 5637155618813000530463081)
        ·
          refine ⟨4227866714109750397847311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5637155618813000530463081 4227866714109750397847311)
          ·
            refine ⟨6341800071164625596770967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227866714109750397847311 6341800071164625596770967)
            ·
              refine ⟨9512700106746938395156451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341800071164625596770967 9512700106746938395156451)
              ·
                refine ⟨14269050160120407592734677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9512700106746938395156451 14269050160120407592734677)
                ·
                  refine ⟨334430863127822052954719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14269050160120407592734677 334430863127822052954719)
                  ·
                    rfl

theorem cell22_2930858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_2930858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930858 prefixEnd_2930858 := by exact prefixLift 2930858
  have htrace : WordTrace (prefixWord ++ tailWord_2930858) baseStart_2930858 baseEnd_2930858 := by
    simpa [prefixWord, tailWord_2930858, baseEnd_2930858] using wordTrace_append hprefix tailTrace_2930858
  have hstable : (prefixWord ++ tailWord_2930858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930858).length < 2 ^ (prefixWord ++ tailWord_2930858).sum := by decide
  have hdescent : baseEnd_2930858 < baseStart_2930858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930862 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2930862 : Nat := 118140960795 + 2930862 * 2 ^ 59
def prefixEnd_2930862 : Nat := 4983230072969 + 3 ^ 40 * 2930862 * 2
def baseEnd_2930862 : Nat := 1003293958665211481764145

theorem tailTrace_2930862 : CollatzResearch.WordTrace tailWord_2930862 prefixEnd_2930862 1003293958665211481764145 := by
  unfold tailWord_2930862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13362164888499375027972355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71264879405330000149185893 13362164888499375027972355)
  ·
    refine ⟨20043247332749062541958533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13362164888499375027972355 20043247332749062541958533)
    ·
      refine ⟨3758108874890449226617225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20043247332749062541958533 3758108874890449226617225)
      ·
        refine ⟨2818581656167836919962919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3758108874890449226617225 2818581656167836919962919)
        ·
          refine ⟨4227872484251755379944379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818581656167836919962919 4227872484251755379944379)
          ·
            refine ⟨6341808726377633069916569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227872484251755379944379 6341808726377633069916569)
            ·
              refine ⟨4756356544783224802437427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6341808726377633069916569 4756356544783224802437427)
              ·
                refine ⟨7134534817174837203656141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756356544783224802437427 7134534817174837203656141)
                ·
                  refine ⟨2675450556440563951371053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7134534817174837203656141 2675450556440563951371053)
                  ·
                    refine ⟨1003293958665211481764145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2675450556440563951371053 1003293958665211481764145)
                    ·
                      rfl

theorem cell22_2930862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2930862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930862 prefixEnd_2930862 := by exact prefixLift 2930862
  have htrace : WordTrace (prefixWord ++ tailWord_2930862) baseStart_2930862 baseEnd_2930862 := by
    simpa [prefixWord, tailWord_2930862, baseEnd_2930862] using wordTrace_append hprefix tailTrace_2930862
  have hstable : (prefixWord ++ tailWord_2930862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930862).length < 2 ^ (prefixWord ++ tailWord_2930862).sum := by decide
  have hdescent : baseEnd_2930862 < baseStart_2930862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930920 : List Nat := [2, 1, 4, 1, 2, 3, 3, 2, 4]
def baseStart_2930920 : Nat := 118140960795 + 2930920 * 2 ^ 59
def prefixEnd_2930920 : Nat := 4983230072969 + 3 ^ 40 * 2930920 * 2
def baseEnd_2930920 : Nat := 334437937750172887937989

theorem tailTrace_2930920 : CollatzResearch.WordTrace tailWord_2930920 prefixEnd_2930920 334437937750172887937989 := by
  unfold tailWord_2930920
  simp only [CollatzResearch.WordTrace]
  refine ⟨53449717270892438064695107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71266289694523250752926809 53449717270892438064695107)
  ·
    refine ⟨80174575906338657097042661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53449717270892438064695107 80174575906338657097042661)
    ·
      refine ⟨15032732982438498205695499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80174575906338657097042661 15032732982438498205695499)
      ·
        refine ⟨22549099473657747308543249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15032732982438498205695499 22549099473657747308543249)
        ·
          refine ⟨16911824605243310481407437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22549099473657747308543249 16911824605243310481407437)
          ·
            refine ⟨6341934226966241430527789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16911824605243310481407437 6341934226966241430527789)
            ·
              refine ⟨2378225335112340536447921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6341934226966241430527789 2378225335112340536447921)
              ·
                refine ⟨1783669001334255402335941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378225335112340536447921 1783669001334255402335941)
                ·
                  refine ⟨334437937750172887937989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1783669001334255402335941 334437937750172887937989)
                  ·
                    rfl

theorem cell22_2930920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 4].length) (baseStart_2930920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930920 prefixEnd_2930920 := by exact prefixLift 2930920
  have htrace : WordTrace (prefixWord ++ tailWord_2930920) baseStart_2930920 baseEnd_2930920 := by
    simpa [prefixWord, tailWord_2930920, baseEnd_2930920] using wordTrace_append hprefix tailTrace_2930920
  have hstable : (prefixWord ++ tailWord_2930920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930920).length < 2 ^ (prefixWord ++ tailWord_2930920).sum := by decide
  have hdescent : baseEnd_2930920 < baseStart_2930920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930959 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 9]
def baseStart_2930959 : Nat := 118140960795 + 2930959 * 2 ^ 59
def prefixEnd_2930959 : Nat := 4983230072969 + 3 ^ 40 * 2930959 * 2
def baseEnd_2930959 : Nat := 334442387915845187362949

theorem tailTrace_2930959 : CollatzResearch.WordTrace tailWord_2930959 prefixEnd_2930959 334442387915845187362949 := by
  unfold tailWord_2930959
  simp only [CollatzResearch.WordTrace]
  refine ⟨106900856988643585790059931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71267237992429057193373287 106900856988643585790059931)
  ·
    refine ⟨160351285482965378685089897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106900856988643585790059931 160351285482965378685089897)
    ·
      refine ⟨120263464112224034013817423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160351285482965378685089897 120263464112224034013817423)
      ·
        refine ⟨180395196168336051020726135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120263464112224034013817423 180395196168336051020726135)
        ·
          refine ⟨270592794252504076531089203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180395196168336051020726135 270592794252504076531089203)
          ·
            refine ⟨405889191378756114796633805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270592794252504076531089203 405889191378756114796633805)
            ·
              refine ⟨152208446767033543048737677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405889191378756114796633805 152208446767033543048737677)
              ·
                refine ⟨57078167537637578643276629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152208446767033543048737677 57078167537637578643276629)
                ·
                  refine ⟨334442387915845187362949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57078167537637578643276629 334442387915845187362949)
                  ·
                    rfl

theorem cell22_2930959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 9].length) (baseStart_2930959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2930959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2930959 prefixEnd_2930959 := by exact prefixLift 2930959
  have htrace : WordTrace (prefixWord ++ tailWord_2930959) baseStart_2930959 baseEnd_2930959 := by
    simpa [prefixWord, tailWord_2930959, baseEnd_2930959] using wordTrace_append hprefix tailTrace_2930959
  have hstable : (prefixWord ++ tailWord_2930959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930959).length < 2 ^ (prefixWord ++ tailWord_2930959).sum := by decide
  have hdescent : baseEnd_2930959 < baseStart_2930959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931051 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 4]
def baseStart_2931051 : Nat := 118140960795 + 2931051 * 2 ^ 59
def prefixEnd_2931051 : Nat := 4983230072969 + 3 ^ 40 * 2931051 * 2
def baseEnd_2931051 : Nat := 1003358657227677988788565

theorem tailTrace_2931051 : CollatzResearch.WordTrace tailWord_2931051 prefixEnd_2931051 1003358657227677988788565 := by
  unfold tailWord_2931051
  simp only [CollatzResearch.WordTrace]
  refine ⟨106904212504310285502409007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71269475002873523668272671 106904212504310285502409007)
  ·
    refine ⟨160356318756465428253613511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106904212504310285502409007 160356318756465428253613511)
    ·
      refine ⟨240534478134698142380420267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160356318756465428253613511 240534478134698142380420267)
      ·
        refine ⟨360801717202047213570630401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240534478134698142380420267 360801717202047213570630401)
        ·
          refine ⟨270601287901535410177972801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360801717202047213570630401 270601287901535410177972801)
          ·
            refine ⟨202950965926151557633479601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270601287901535410177972801 202950965926151557633479601)
            ·
              refine ⟨152213224444613668225109701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202950965926151557633479601 152213224444613668225109701)
              ·
                refine ⟨28539979583365062792208069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152213224444613668225109701 28539979583365062792208069)
                ·
                  refine ⟨5351246171880949273539013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28539979583365062792208069 5351246171880949273539013)
                  ·
                    refine ⟨1003358657227677988788565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5351246171880949273539013 1003358657227677988788565)
                    ·
                      rfl

theorem cell22_2931051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4].length) (baseStart_2931051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931051 prefixEnd_2931051 := by exact prefixLift 2931051
  have htrace : WordTrace (prefixWord ++ tailWord_2931051) baseStart_2931051 baseEnd_2931051 := by
    simpa [prefixWord, tailWord_2931051, baseEnd_2931051] using wordTrace_append hprefix tailTrace_2931051
  have hstable : (prefixWord ++ tailWord_2931051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931051).length < 2 ^ (prefixWord ++ tailWord_2931051).sum := by decide
  have hdescent : baseEnd_2931051 < baseStart_2931051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931175 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2931175 : Nat := 118140960795 + 2931175 * 2 ^ 59
def prefixEnd_2931175 : Nat := 4983230072969 + 3 ^ 40 * 2931175 * 2
def baseEnd_2931175 : Nat := 1003401104961782998688185

theorem tailTrace_2931175 : CollatzResearch.WordTrace tailWord_2931175 prefixEnd_2931175 1003401104961782998688185 := by
  unfold tailWord_2931175
  simp only [CollatzResearch.WordTrace]
  refine ⟨106908735155861054679922979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71272490103907369786615319 106908735155861054679922979)
  ·
    refine ⟨160363102733791582019884469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106908735155861054679922979 160363102733791582019884469)
    ·
      refine ⟨15034040881292960814364169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160363102733791582019884469 15034040881292960814364169)
      ·
        refine ⟨11275530660969720610773127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15034040881292960814364169 11275530660969720610773127)
        ·
          refine ⟨16913295991454580916159691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11275530660969720610773127 16913295991454580916159691)
          ·
            refine ⟨25369943987181871374239537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16913295991454580916159691 25369943987181871374239537)
            ·
              refine ⟨19027457990386403530679653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25369943987181871374239537 19027457990386403530679653)
              ·
                refine ⟨3567648373197450662002435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19027457990386403530679653 3567648373197450662002435)
                ·
                  refine ⟨5351472559796175993003653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567648373197450662002435 5351472559796175993003653)
                  ·
                    refine ⟨1003401104961782998688185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5351472559796175993003653 1003401104961782998688185)
                    ·
                      rfl

theorem cell22_2931175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2931175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931175 prefixEnd_2931175 := by exact prefixLift 2931175
  have htrace : WordTrace (prefixWord ++ tailWord_2931175) baseStart_2931175 baseEnd_2931175 := by
    simpa [prefixWord, tailWord_2931175, baseEnd_2931175] using wordTrace_append hprefix tailTrace_2931175
  have hstable : (prefixWord ++ tailWord_2931175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931175).length < 2 ^ (prefixWord ++ tailWord_2931175).sum := by decide
  have hdescent : baseEnd_2931175 < baseStart_2931175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931203 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 4, 4]
def baseStart_2931203 : Nat := 118140960795 + 2931203 * 2 ^ 59
def prefixEnd_2931203 : Nat := 4983230072969 + 3 ^ 40 * 2931203 * 2
def baseEnd_2931203 : Nat := 1003410689934000258988099

theorem tailTrace_2931203 : CollatzResearch.WordTrace tailWord_2931203 prefixEnd_2931203 1003410689934000258988099 := by
  unfold tailWord_2931203
  simp only [CollatzResearch.WordTrace]
  refine ⟨106909756399759615461942263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71273170933173076974628175 106909756399759615461942263)
  ·
    refine ⟨160364634599639423192913395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106909756399759615461942263 160364634599639423192913395)
    ·
      refine ⟨240546951899459134789370093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160364634599639423192913395 240546951899459134789370093)
      ·
        refine ⟨90205106962297175546013785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240546951899459134789370093 90205106962297175546013785)
        ·
          refine ⟨67653830221722881659510339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90205106962297175546013785 67653830221722881659510339)
          ·
            refine ⟨101480745332584322489265509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67653830221722881659510339 101480745332584322489265509)
            ·
              refine ⟨19027639749859560466737283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101480745332584322489265509 19027639749859560466737283)
              ·
                refine ⟨28541459624789340700105925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19027639749859560466737283 28541459624789340700105925)
                ·
                  refine ⟨5351523679648001381269861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28541459624789340700105925 5351523679648001381269861)
                  ·
                    refine ⟨1003410689934000258988099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5351523679648001381269861 1003410689934000258988099)
                    ·
                      rfl

theorem cell22_2931203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 4].length) (baseStart_2931203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931203 prefixEnd_2931203 := by exact prefixLift 2931203
  have htrace : WordTrace (prefixWord ++ tailWord_2931203) baseStart_2931203 baseEnd_2931203 := by
    simpa [prefixWord, tailWord_2931203, baseEnd_2931203] using wordTrace_append hprefix tailTrace_2931203
  have hstable : (prefixWord ++ tailWord_2931203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931203).length < 2 ^ (prefixWord ++ tailWord_2931203).sum := by decide
  have hdescent : baseEnd_2931203 < baseStart_2931203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931233 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_2931233 : Nat := 118140960795 + 2931233 * 2 ^ 59
def prefixEnd_2931233 : Nat := 4983230072969 + 3 ^ 40 * 2931233 * 2
def baseEnd_2931233 : Nat := 1003420959547090180738007

theorem tailTrace_2931233 : CollatzResearch.WordTrace tailWord_2931233 prefixEnd_2931233 1003420959547090180738007 := by
  unfold tailWord_2931233
  simp only [CollatzResearch.WordTrace]
  refine ⟨106910850589650930585534353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71273900393100620390356235 106910850589650930585534353)
  ·
    refine ⟨80183137942238197939150765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106910850589650930585534353 80183137942238197939150765)
    ·
      refine ⟨30068676728339324227181537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80183137942238197939150765 30068676728339324227181537)
      ·
        refine ⟨22551507546254493170386153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30068676728339324227181537 22551507546254493170386153)
        ·
          refine ⟨16913630659690869877789615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22551507546254493170386153 16913630659690869877789615)
          ·
            refine ⟨25370445989536304816684423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16913630659690869877789615 25370445989536304816684423)
            ·
              refine ⟨38055668984304457225026635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25370445989536304816684423 38055668984304457225026635)
              ·
                refine ⟨57083503476456685837539953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38055668984304457225026635 57083503476456685837539953)
                ·
                  refine ⟨42812627607342514378154965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57083503476456685837539953 42812627607342514378154965)
                  ·
                    refine ⟨1003420959547090180738007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42812627607342514378154965 1003420959547090180738007)
                    ·
                      rfl

theorem cell22_2931233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_2931233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931233 prefixEnd_2931233 := by exact prefixLift 2931233
  have htrace : WordTrace (prefixWord ++ tailWord_2931233) baseStart_2931233 baseEnd_2931233 := by
    simpa [prefixWord, tailWord_2931233, baseEnd_2931233] using wordTrace_append hprefix tailTrace_2931233
  have hstable : (prefixWord ++ tailWord_2931233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931233).length < 2 ^ (prefixWord ++ tailWord_2931233).sum := by decide
  have hdescent : baseEnd_2931233 < baseStart_2931233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931235 : List Nat := [1, 1, 1, 4, 4, 1, 4, 6]
def baseStart_2931235 : Nat := 118140960795 + 2931235 * 2 ^ 59
def prefixEnd_2931235 : Nat := 4983230072969 + 3 ^ 40 * 2931235 * 2
def baseEnd_2931235 : Nat := 111491293798662538020889

theorem tailTrace_2931235 : CollatzResearch.WordTrace tailWord_2931235 prefixEnd_2931235 111491293798662538020889 := by
  unfold tailWord_2931235
  simp only [CollatzResearch.WordTrace]
  refine ⟨106910923535643684927107159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71273949023762456618071439 106910923535643684927107159)
  ·
    refine ⟨160366385303465527390660739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106910923535643684927107159 160366385303465527390660739)
    ·
      refine ⟨240549577955198291085991109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160366385303465527390660739 240549577955198291085991109)
      ·
        refine ⟨45103045866599679578623333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240549577955198291085991109 45103045866599679578623333)
        ·
          refine ⟨8456821099987439920991875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45103045866599679578623333 8456821099987439920991875)
          ·
            refine ⟨12685231649981159881487813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8456821099987439920991875 12685231649981159881487813)
            ·
              refine ⟨2378480934371467477778965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12685231649981159881487813 2378480934371467477778965)
              ·
                refine ⟨111491293798662538020889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2378480934371467477778965 111491293798662538020889)
                ·
                  rfl

theorem cell22_2931235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 6].length) (baseStart_2931235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931235 prefixEnd_2931235 := by exact prefixLift 2931235
  have htrace : WordTrace (prefixWord ++ tailWord_2931235) baseStart_2931235 baseEnd_2931235 := by
    simpa [prefixWord, tailWord_2931235, baseEnd_2931235] using wordTrace_append hprefix tailTrace_2931235
  have hstable : (prefixWord ++ tailWord_2931235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931235).length < 2 ^ (prefixWord ++ tailWord_2931235).sum := by decide
  have hdescent : baseEnd_2931235 < baseStart_2931235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931250 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_2931250 : Nat := 118140960795 + 2931250 * 2 ^ 59
def prefixEnd_2931250 : Nat := 4983230072969 + 3 ^ 40 * 2931250 * 2
def baseEnd_2931250 : Nat := 1003426778994507803062955

theorem tailTrace_2931250 : CollatzResearch.WordTrace tailWord_2931250 prefixEnd_2931250 1003426778994507803062955 := by
  unfold tailWord_2931250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26727867657647335622225801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71274313753726228325935469 26727867657647335622225801)
  ·
    refine ⟨20045900743235501716669351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26727867657647335622225801 20045900743235501716669351)
    ·
      refine ⟨30068851114853252575004027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20045900743235501716669351 30068851114853252575004027)
      ·
        refine ⟨45103276672279878862506041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30068851114853252575004027 45103276672279878862506041)
        ·
          refine ⟨33827457504209909146879531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45103276672279878862506041 33827457504209909146879531)
          ·
            refine ⟨50741186256314863720319297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33827457504209909146879531 50741186256314863720319297)
            ·
              refine ⟨38055889692236147790239473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50741186256314863720319297 38055889692236147790239473)
              ·
                refine ⟨28541917269177110842679605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38055889692236147790239473 28541917269177110842679605)
                ·
                  refine ⟨2675804743985354141501213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28541917269177110842679605 2675804743985354141501213)
                  ·
                    refine ⟨1003426778994507803062955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2675804743985354141501213 1003426778994507803062955)
                    ·
                      rfl

theorem cell22_2931250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_2931250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931250 prefixEnd_2931250 := by exact prefixLift 2931250
  have htrace : WordTrace (prefixWord ++ tailWord_2931250) baseStart_2931250 baseEnd_2931250 := by
    simpa [prefixWord, tailWord_2931250, baseEnd_2931250] using wordTrace_append hprefix tailTrace_2931250
  have hstable : (prefixWord ++ tailWord_2931250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931250).length < 2 ^ (prefixWord ++ tailWord_2931250).sum := by decide
  have hdescent : baseEnd_2931250 < baseStart_2931250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931263 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 7]
def baseStart_2931263 : Nat := 118140960795 + 2931263 * 2 ^ 59
def prefixEnd_2931263 : Nat := 4983230072969 + 3 ^ 40 * 2931263 * 2
def baseEnd_2931263 : Nat := 334477076386726700829305

theorem tailTrace_2931263 : CollatzResearch.WordTrace tailWord_2931263 prefixEnd_2931263 334477076386726700829305 := by
  unfold tailWord_2931263
  simp only [CollatzResearch.WordTrace]
  refine ⟨106911944779542245709126443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71274629853028163806084295 106911944779542245709126443)
  ·
    refine ⟨160367917169313368563689665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106911944779542245709126443 160367917169313368563689665)
    ·
      refine ⟨120275937876985026422767249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160367917169313368563689665 120275937876985026422767249)
      ·
        refine ⟨90206953407738769817075437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120275937876985026422767249 90206953407738769817075437)
        ·
          refine ⟨33827607527902038681403289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90206953407738769817075437 33827607527902038681403289)
          ·
            refine ⟨25370705645926529011052467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33827607527902038681403289 25370705645926529011052467)
            ·
              refine ⟨38056058468889793516578701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25370705645926529011052467 38056058468889793516578701)
              ·
                refine ⟨14271021925833672568717013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38056058468889793516578701 14271021925833672568717013)
                ·
                  refine ⟨334477076386726700829305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14271021925833672568717013 334477076386726700829305)
                  ·
                    rfl

theorem cell22_2931263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 7].length) (baseStart_2931263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931263 prefixEnd_2931263 := by exact prefixLift 2931263
  have htrace : WordTrace (prefixWord ++ tailWord_2931263) baseStart_2931263 baseEnd_2931263 := by
    simpa [prefixWord, tailWord_2931263, baseEnd_2931263] using wordTrace_append hprefix tailTrace_2931263
  have hstable : (prefixWord ++ tailWord_2931263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931263).length < 2 ^ (prefixWord ++ tailWord_2931263).sum := by decide
  have hdescent : baseEnd_2931263 < baseStart_2931263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931267 : List Nat := [1, 1, 1, 3, 1, 2, 1, 8, 1, 3]
def baseStart_2931267 : Nat := 118140960795 + 2931267 * 2 ^ 59
def prefixEnd_2931267 : Nat := 4983230072969 + 3 ^ 40 * 2931267 * 2
def baseEnd_2931267 : Nat := 1003432598441925425387903

theorem tailTrace_2931267 : CollatzResearch.WordTrace tailWord_2931267 prefixEnd_2931267 1003432598441925425387903 := by
  unfold tailWord_2931267
  simp only [CollatzResearch.WordTrace]
  refine ⟨106912090671527754392272055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71274727114351836261514703 106912090671527754392272055)
  ·
    refine ⟨160368136007291631588408083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106912090671527754392272055 160368136007291631588408083)
    ·
      refine ⟨240552204010937447382612125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160368136007291631588408083 240552204010937447382612125)
      ·
        refine ⟨90207076504101542768479547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240552204010937447382612125 90207076504101542768479547)
        ·
          refine ⟨135310614756152314152719321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90207076504101542768479547 135310614756152314152719321)
          ·
            refine ⟨101482961067114235614539491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135310614756152314152719321 101482961067114235614539491)
            ·
              refine ⟨152224441600671353421809237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101482961067114235614539491 152224441600671353421809237)
              ·
                refine ⟨1783880175007867422911827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 152224441600671353421809237 1783880175007867422911827)
                ·
                  refine ⟨2675820262511801134367741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783880175007867422911827 2675820262511801134367741)
                  ·
                    refine ⟨1003432598441925425387903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2675820262511801134367741 1003432598441925425387903)
                    ·
                      rfl

theorem cell22_2931267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 3].length) (baseStart_2931267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931267 prefixEnd_2931267 := by exact prefixLift 2931267
  have htrace : WordTrace (prefixWord ++ tailWord_2931267) baseStart_2931267 baseEnd_2931267 := by
    simpa [prefixWord, tailWord_2931267, baseEnd_2931267] using wordTrace_append hprefix tailTrace_2931267
  have hstable : (prefixWord ++ tailWord_2931267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931267).length < 2 ^ (prefixWord ++ tailWord_2931267).sum := by decide
  have hdescent : baseEnd_2931267 < baseStart_2931267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931361 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 1, 4]
def baseStart_2931361 : Nat := 118140960795 + 2931361 * 2 ^ 59
def prefixEnd_2931361 : Nat := 4983230072969 + 3 ^ 40 * 2931361 * 2
def baseEnd_2931361 : Nat := 1003464776562940513537615

theorem tailTrace_2931361 : CollatzResearch.WordTrace tailWord_2931361 prefixEnd_2931361 1003464776562940513537615 := by
  unfold tailWord_2931361
  simp only [CollatzResearch.WordTrace]
  refine ⟨106915519133187208446193937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71277012755458138964129291 106915519133187208446193937)
  ·
    refine ⟨80186639349890406334645453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106915519133187208446193937 80186639349890406334645453)
    ·
      refine ⟨30069989756208902375492045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80186639349890406334645453 30069989756208902375492045)
      ·
        refine ⟨11276246158578338390809517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30069989756208902375492045 11276246158578338390809517)
        ·
          refine ⟨4228592309466876896553569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11276246158578338390809517 4228592309466876896553569)
          ·
            refine ⟨3171444232100157672415177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4228592309466876896553569 3171444232100157672415177)
            ·
              refine ⟨2378583174075118254311383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171444232100157672415177 2378583174075118254311383)
              ·
                refine ⟨3567874761112677381467075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378583174075118254311383 3567874761112677381467075)
                ·
                  refine ⟨5351812141669016072200613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567874761112677381467075 5351812141669016072200613)
                  ·
                    refine ⟨1003464776562940513537615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5351812141669016072200613 1003464776562940513537615)
                    ·
                      rfl

theorem cell22_2931361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_2931361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931361 prefixEnd_2931361 := by exact prefixLift 2931361
  have htrace : WordTrace (prefixWord ++ tailWord_2931361) baseStart_2931361 baseEnd_2931361 := by
    simpa [prefixWord, tailWord_2931361, baseEnd_2931361] using wordTrace_append hprefix tailTrace_2931361
  have hstable : (prefixWord ++ tailWord_2931361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931361).length < 2 ^ (prefixWord ++ tailWord_2931361).sum := by decide
  have hdescent : baseEnd_2931361 < baseStart_2931361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931404 : List Nat := [2, 2, 1, 5, 1, 3, 2, 6]
def baseStart_2931404 : Nat := 118140960795 + 2931404 * 2 ^ 59
def prefixEnd_2931404 : Nat := 4983230072969 + 3 ^ 40 * 2931404 * 2
def baseEnd_2931404 : Nat := 111497721815744748301387

theorem tailTrace_2931404 : CollatzResearch.WordTrace tailWord_2931404 prefixEnd_2931404 111497721815744748301387 := by
  unfold tailWord_2931404
  simp only [CollatzResearch.WordTrace]
  refine ⟨53458543736015713395004633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71278058314687617860006177 53458543736015713395004633)
  ·
    refine ⟨40093907802011785046253475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53458543736015713395004633 40093907802011785046253475)
    ·
      refine ⟨60140861703017677569380213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40093907802011785046253475 60140861703017677569380213)
      ·
        refine ⟨5638205784657907272129395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60140861703017677569380213 5638205784657907272129395)
        ·
          refine ⟨8457308676986860908194093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5638205784657907272129395 8457308676986860908194093)
          ·
            refine ⟨3171490753870072840572785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8457308676986860908194093 3171490753870072840572785)
            ·
              refine ⟨2378618065402554630429589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171490753870072840572785 2378618065402554630429589)
              ·
                refine ⟨111497721815744748301387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2378618065402554630429589 111497721815744748301387)
                ·
                  rfl

theorem cell22_2931404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 6].length) (baseStart_2931404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931404 prefixEnd_2931404 := by exact prefixLift 2931404
  have htrace : WordTrace (prefixWord ++ tailWord_2931404) baseStart_2931404 baseEnd_2931404 := by
    simpa [prefixWord, tailWord_2931404, baseEnd_2931404] using wordTrace_append hprefix tailTrace_2931404
  have hstable : (prefixWord ++ tailWord_2931404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931404).length < 2 ^ (prefixWord ++ tailWord_2931404).sum := by decide
  have hdescent : baseEnd_2931404 < baseStart_2931404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931415 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 7]
def baseStart_2931415 : Nat := 118140960795 + 2931415 * 2 ^ 59
def prefixEnd_2931415 : Nat := 4983230072969 + 3 ^ 40 * 2931415 * 2
def baseEnd_2931415 : Nat := 334494420622167457562483

theorem tailTrace_2931415 : CollatzResearch.WordTrace tailWord_2931415 prefixEnd_2931415 334494420622167457562483 := by
  unfold tailWord_2931415
  simp only [CollatzResearch.WordTrace]
  refine ⟨106917488674991575668659699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71278325783327717112439799 106917488674991575668659699)
  ·
    refine ⟨160376233012487363502989549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106917488674991575668659699 160376233012487363502989549)
    ·
      refine ⟨60141087379682761313621081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160376233012487363502989549 60141087379682761313621081)
      ·
        refine ⟨45105815534762070985215811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60141087379682761313621081 45105815534762070985215811)
        ·
          refine ⟨67658723302143106477823717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45105815534762070985215811 67658723302143106477823717)
          ·
            refine ⟨12686010619151832464591947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67658723302143106477823717 12686010619151832464591947)
            ·
              refine ⟨19029015928727748696887921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12686010619151832464591947 19029015928727748696887921)
              ·
                refine ⟨14271761946545811522665941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19029015928727748696887921 14271761946545811522665941)
                ·
                  refine ⟨334494420622167457562483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14271761946545811522665941 334494420622167457562483)
                  ·
                    rfl

theorem cell22_2931415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 7].length) (baseStart_2931415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931415 prefixEnd_2931415 := by exact prefixLift 2931415
  have htrace : WordTrace (prefixWord ++ tailWord_2931415) baseStart_2931415 baseEnd_2931415 := by
    simpa [prefixWord, tailWord_2931415, baseEnd_2931415] using wordTrace_append hprefix tailTrace_2931415
  have hstable : (prefixWord ++ tailWord_2931415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931415).length < 2 ^ (prefixWord ++ tailWord_2931415).sum := by decide
  have hdescent : baseEnd_2931415 < baseStart_2931415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931509 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2931509 : Nat := 118140960795 + 2931509 * 2 ^ 59
def prefixEnd_2931509 : Nat := 4983230072969 + 3 ^ 40 * 2931509 * 2
def baseEnd_2931509 : Nat := 1003515439987517460837161

theorem tailTrace_2931509 : CollatzResearch.WordTrace tailWord_2931509 prefixEnd_2931509 1003515439987517460837161 := by
  unfold tailWord_2931509
  simp only [CollatzResearch.WordTrace]
  refine ⟨106920917136651029722581581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71280611424434019815054387 106920917136651029722581581)
  ·
    refine ⟨40095343926244136145968093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106920917136651029722581581 40095343926244136145968093)
    ·
      refine ⟨15035753972341551054738035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40095343926244136145968093 15035753972341551054738035)
      ·
        refine ⟨22553630958512326582107053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15035753972341551054738035 22553630958512326582107053)
        ·
          refine ⟨8457611609442122468290145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22553630958512326582107053 8457611609442122468290145)
          ·
            refine ⟨6343208707081591851217609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8457611609442122468290145 6343208707081591851217609)
            ·
              refine ⟨4757406530311193888413207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6343208707081591851217609 4757406530311193888413207)
              ·
                refine ⟨7136109795466790832619811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4757406530311193888413207 7136109795466790832619811)
                ·
                  refine ⟨10704164693200186248929717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7136109795466790832619811 10704164693200186248929717)
                  ·
                    refine ⟨1003515439987517460837161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10704164693200186248929717 1003515439987517460837161)
                    ·
                      rfl

theorem cell22_2931509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2931509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931509 prefixEnd_2931509 := by exact prefixLift 2931509
  have htrace : WordTrace (prefixWord ++ tailWord_2931509) baseStart_2931509 baseEnd_2931509 := by
    simpa [prefixWord, tailWord_2931509, baseEnd_2931509] using wordTrace_append hprefix tailTrace_2931509
  have hstable : (prefixWord ++ tailWord_2931509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931509).length < 2 ^ (prefixWord ++ tailWord_2931509).sum := by decide
  have hdescent : baseEnd_2931509 < baseStart_2931509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931567 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 5]
def baseStart_2931567 : Nat := 118140960795 + 2931567 * 2 ^ 59
def prefixEnd_2931567 : Nat := 4983230072969 + 3 ^ 40 * 2931567 * 2
def baseEnd_2931567 : Nat := 334511764857608214295661

theorem tailTrace_2931567 : CollatzResearch.WordTrace tailWord_2931567 prefixEnd_2931567 334511764857608214295661 := by
  unfold tailWord_2931567
  simp only [CollatzResearch.WordTrace]
  refine ⟨106923032570440905628192955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71282021713627270418795303 106923032570440905628192955)
  ·
    refine ⟨160384548855661358442289433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106923032570440905628192955 160384548855661358442289433)
    ·
      refine ⟨120288411641746018831717075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160384548855661358442289433 120288411641746018831717075)
      ·
        refine ⟨180432617462619028247575613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120288411641746018831717075 180432617462619028247575613)
        ·
          refine ⟨67662231548482135592840855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180432617462619028247575613 67662231548482135592840855)
          ·
            refine ⟨101493347322723203389261283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67662231548482135592840855 101493347322723203389261283)
            ·
              refine ⟨152240020984084805083891925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101493347322723203389261283 152240020984084805083891925)
              ·
                refine ⟨3568125491814487619153717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 152240020984084805083891925 3568125491814487619153717)
                ·
                  refine ⟨334511764857608214295661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3568125491814487619153717 334511764857608214295661)
                  ·
                    rfl

theorem cell22_2931567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 5].length) (baseStart_2931567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931567 prefixEnd_2931567 := by exact prefixLift 2931567
  have htrace : WordTrace (prefixWord ++ tailWord_2931567) baseStart_2931567 baseEnd_2931567 := by
    simpa [prefixWord, tailWord_2931567, baseEnd_2931567] using wordTrace_append hprefix tailTrace_2931567
  have hstable : (prefixWord ++ tailWord_2931567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931567).length < 2 ^ (prefixWord ++ tailWord_2931567).sum := by decide
  have hdescent : baseEnd_2931567 < baseStart_2931567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931618 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_2931618 : Nat := 118140960795 + 2931618 * 2 ^ 59
def prefixEnd_2931618 : Nat := 4983230072969 + 3 ^ 40 * 2931618 * 2
def baseEnd_2931618 : Nat := 334517584305025836620609

theorem tailTrace_2931618 : CollatzResearch.WordTrace tailWord_2931618 prefixEnd_2931618 334517584305025836620609 := by
  unfold tailWord_2931618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26731223173314035334574877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71283261795504094225533005 26731223173314035334574877)
  ·
    refine ⟨10024208689992763250465579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26731223173314035334574877 10024208689992763250465579)
    ·
      refine ⟨15036313034989144875698369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10024208689992763250465579 15036313034989144875698369)
      ·
        refine ⟨11277234776241858656773777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15036313034989144875698369 11277234776241858656773777)
        ·
          refine ⟨8457926082181393992580333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11277234776241858656773777 8457926082181393992580333)
          ·
            refine ⟨3171722280818022747217625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8457926082181393992580333 3171722280818022747217625)
            ·
              refine ⟨2378791710613517060413219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171722280818022747217625 2378791710613517060413219)
              ·
                refine ⟨3568187565920275590619829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378791710613517060413219 3568187565920275590619829)
                ·
                  refine ⟨334517584305025836620609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3568187565920275590619829 334517584305025836620609)
                  ·
                    rfl

theorem cell22_2931618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_2931618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931618 prefixEnd_2931618 := by exact prefixLift 2931618
  have htrace : WordTrace (prefixWord ++ tailWord_2931618) baseStart_2931618 baseEnd_2931618 := by
    simpa [prefixWord, tailWord_2931618, baseEnd_2931618] using wordTrace_append hprefix tailTrace_2931618
  have hstable : (prefixWord ++ tailWord_2931618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931618).length < 2 ^ (prefixWord ++ tailWord_2931618).sum := by decide
  have hdescent : baseEnd_2931618 < baseStart_2931618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931646 : List Nat := [4, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_2931646 : Nat := 118140960795 + 2931646 * 2 ^ 59
def prefixEnd_2931646 : Nat := 4983230072969 + 3 ^ 40 * 2931646 * 2
def baseEnd_2931646 : Nat := 334520779295764923387247

theorem tailTrace_2931646 : CollatzResearch.WordTrace tailWord_2931646 prefixEnd_2931646 334520779295764923387247 := by
  unfold tailWord_2931646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13365739242144337765039849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71283942624769801413545861 13365739242144337765039849)
  ·
    refine ⟨10024304431608253323779887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13365739242144337765039849 10024304431608253323779887)
    ·
      refine ⟨15036456647412379985669831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10024304431608253323779887 15036456647412379985669831)
      ·
        refine ⟨22554684971118569978504747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15036456647412379985669831 22554684971118569978504747)
        ·
          refine ⟨33832027456677854967757121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22554684971118569978504747 33832027456677854967757121)
          ·
            refine ⟨25374020592508391225817841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33832027456677854967757121 25374020592508391225817841)
            ·
              refine ⟨19030515444381293419363381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25374020592508391225817841 19030515444381293419363381)
              ·
                refine ⟨1784110822910746258065317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19030515444381293419363381 1784110822910746258065317)
                ·
                  refine ⟨334520779295764923387247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784110822910746258065317 334520779295764923387247)
                  ·
                    rfl

theorem cell22_2931646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_2931646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931646 prefixEnd_2931646 := by exact prefixLift 2931646
  have htrace : WordTrace (prefixWord ++ tailWord_2931646) baseStart_2931646 baseEnd_2931646 := by
    simpa [prefixWord, tailWord_2931646, baseEnd_2931646] using wordTrace_append hprefix tailTrace_2931646
  have hstable : (prefixWord ++ tailWord_2931646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931646).length < 2 ^ (prefixWord ++ tailWord_2931646).sum := by decide
  have hdescent : baseEnd_2931646 < baseStart_2931646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931659 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 2, 4]
def baseStart_2931659 : Nat := 118140960795 + 2931659 * 2 ^ 59
def prefixEnd_2931659 : Nat := 4983230072969 + 3 ^ 40 * 2931659 * 2
def baseEnd_2931659 : Nat := 1003566788052967069586701

theorem tailTrace_2931659 : CollatzResearch.WordTrace tailWord_2931659 prefixEnd_2931659 1003566788052967069586701 := by
  unfold tailWord_2931659
  simp only [CollatzResearch.WordTrace]
  refine ⟨106926388086107605340542031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71284258724071736893694687 106926388086107605340542031)
  ·
    refine ⟨160389582129161408010813047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106926388086107605340542031 160389582129161408010813047)
    ·
      refine ⟨240584373193742112016219571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160389582129161408010813047 240584373193742112016219571)
      ·
        refine ⟨360876559790613168024329357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240584373193742112016219571 360876559790613168024329357)
        ·
          refine ⟨135328709921479938009123509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360876559790613168024329357 135328709921479938009123509)
          ·
            refine ⟨12687066555138744188355329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135328709921479938009123509 12687066555138744188355329)
            ·
              refine ⟨9515299916354058141266497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12687066555138744188355329 9515299916354058141266497)
              ·
                refine ⟨7136474937265543605949873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9515299916354058141266497 7136474937265543605949873)
                ·
                  refine ⟨5352356202949157704462405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7136474937265543605949873 5352356202949157704462405)
                  ·
                    refine ⟨1003566788052967069586701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5352356202949157704462405 1003566788052967069586701)
                    ·
                      rfl

theorem cell22_2931659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 4].length) (baseStart_2931659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931659 prefixEnd_2931659 := by exact prefixLift 2931659
  have htrace : WordTrace (prefixWord ++ tailWord_2931659) baseStart_2931659 baseEnd_2931659 := by
    simpa [prefixWord, tailWord_2931659, baseEnd_2931659] using wordTrace_append hprefix tailTrace_2931659
  have hstable : (prefixWord ++ tailWord_2931659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931659).length < 2 ^ (prefixWord ++ tailWord_2931659).sum := by decide
  have hdescent : baseEnd_2931659 < baseStart_2931659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931663 : List Nat := [1, 1, 2, 1, 1, 8, 2, 2, 4]
def baseStart_2931663 : Nat := 118140960795 + 2931663 * 2 ^ 59
def prefixEnd_2931663 : Nat := 4983230072969 + 3 ^ 40 * 2931663 * 2
def baseEnd_2931663 : Nat := 334522719111570797495563

theorem tailTrace_2931663 : CollatzResearch.WordTrace tailWord_2931663 prefixEnd_2931663 334522719111570797495563 := by
  unfold tailWord_2931663
  simp only [CollatzResearch.WordTrace]
  refine ⟨106926533978093114023687643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71284355985395409349125095 106926533978093114023687643)
  ·
    refine ⟨160389800967139671035531465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106926533978093114023687643 160389800967139671035531465)
    ·
      refine ⟨120292350725354753276648599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160389800967139671035531465 120292350725354753276648599)
      ·
        refine ⟨180438526088032129914972899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120292350725354753276648599 180438526088032129914972899)
        ·
          refine ⟨270657789132048194872459349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180438526088032129914972899 270657789132048194872459349)
          ·
            refine ⟨3171770966391189783661633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 270657789132048194872459349 3171770966391189783661633)
            ·
              refine ⟨2378828224793392337746225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171770966391189783661633 2378828224793392337746225)
              ·
                refine ⟨1784121168595044253309669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378828224793392337746225 1784121168595044253309669)
                ·
                  refine ⟨334522719111570797495563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784121168595044253309669 334522719111570797495563)
                  ·
                    rfl

theorem cell22_2931663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 4].length) (baseStart_2931663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931663 prefixEnd_2931663 := by exact prefixLift 2931663
  have htrace : WordTrace (prefixWord ++ tailWord_2931663) baseStart_2931663 baseEnd_2931663 := by
    simpa [prefixWord, tailWord_2931663, baseEnd_2931663] using wordTrace_append hprefix tailTrace_2931663
  have hstable : (prefixWord ++ tailWord_2931663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931663).length < 2 ^ (prefixWord ++ tailWord_2931663).sum := by decide
  have hdescent : baseEnd_2931663 < baseStart_2931663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931674 : List Nat := [3, 1, 1, 2, 4, 1, 3, 7]
def baseStart_2931674 : Nat := 118140960795 + 2931674 * 2 ^ 59
def prefixEnd_2931674 : Nat := 4983230072969 + 3 ^ 40 * 2931674 * 2
def baseEnd_2931674 : Nat := 111507991428834670051295

theorem tailTrace_2931674 : CollatzResearch.WordTrace tailWord_2931674 prefixEnd_2931674 111507991428834670051295 := by
  unfold tailWord_2931674
  simp only [CollatzResearch.WordTrace]
  refine ⟨26731733795263315725584519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71284623454035508601558717 26731733795263315725584519)
  ·
    refine ⟨40097600692894973588376779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26731733795263315725584519 40097600692894973588376779)
    ·
      refine ⟨60146401039342460382565169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40097600692894973588376779 60146401039342460382565169)
      ·
        refine ⟨45109800779506845286923877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60146401039342460382565169 45109800779506845286923877)
        ·
          refine ⟨8458087646157533491298227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45109800779506845286923877 8458087646157533491298227)
          ·
            refine ⟨12687131469236300236947341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8458087646157533491298227 12687131469236300236947341)
            ·
              refine ⟨4757674300963612588855253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12687131469236300236947341 4757674300963612588855253)
              ·
                refine ⟨111507991428834670051295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4757674300963612588855253 111507991428834670051295)
                ·
                  rfl

theorem cell22_2931674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_2931674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931674 prefixEnd_2931674 := by exact prefixLift 2931674
  have htrace : WordTrace (prefixWord ++ tailWord_2931674) baseStart_2931674 baseEnd_2931674 := by
    simpa [prefixWord, tailWord_2931674, baseEnd_2931674] using wordTrace_append hprefix tailTrace_2931674
  have hstable : (prefixWord ++ tailWord_2931674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931674).length < 2 ^ (prefixWord ++ tailWord_2931674).sum := by decide
  have hdescent : baseEnd_2931674 < baseStart_2931674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931719 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 7]
def baseStart_2931719 : Nat := 118140960795 + 2931719 * 2 ^ 59
def prefixEnd_2931719 : Nat := 4983230072969 + 3 ^ 40 * 2931719 * 2
def baseEnd_2931719 : Nat := 334529109093048971028839

theorem tailTrace_2931719 : CollatzResearch.WordTrace tailWord_2931719 prefixEnd_2931719 334529109093048971028839 := by
  unfold tailWord_2931719
  simp only [CollatzResearch.WordTrace]
  refine ⟨106928576465890235587726211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71285717643926823725150807 106928576465890235587726211)
  ·
    refine ⟨160392864698835353381589317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106928576465890235587726211 160392864698835353381589317)
    ·
      refine ⟨30073662131031628759047997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160392864698835353381589317 30073662131031628759047997)
      ·
        refine ⟨11277623299136860784642999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30073662131031628759047997 11277623299136860784642999)
        ·
          refine ⟨16916434948705291176964499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11277623299136860784642999 16916434948705291176964499)
          ·
            refine ⟨25374652423057936765446749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16916434948705291176964499 25374652423057936765446749)
            ·
              refine ⟨9515494658646726287042531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25374652423057936765446749 9515494658646726287042531)
              ·
                refine ⟨14273241987970089430563797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9515494658646726287042531 14273241987970089430563797)
                ·
                  refine ⟨334529109093048971028839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14273241987970089430563797 334529109093048971028839)
                  ·
                    rfl

theorem cell22_2931719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 7].length) (baseStart_2931719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931719 prefixEnd_2931719 := by exact prefixLift 2931719
  have htrace : WordTrace (prefixWord ++ tailWord_2931719) baseStart_2931719 baseEnd_2931719 := by
    simpa [prefixWord, tailWord_2931719, baseEnd_2931719] using wordTrace_append hprefix tailTrace_2931719
  have hstable : (prefixWord ++ tailWord_2931719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931719).length < 2 ^ (prefixWord ++ tailWord_2931719).sum := by decide
  have hdescent : baseEnd_2931719 < baseStart_2931719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931723 : List Nat := [1, 1, 1, 1, 6, 2, 2, 4, 1, 3]
def baseStart_2931723 : Nat := 118140960795 + 2931723 * 2 ^ 59
def prefixEnd_2931723 : Nat := 4983230072969 + 3 ^ 40 * 2931723 * 2
def baseEnd_2931723 : Nat := 1003588696560892235986505

theorem tailTrace_2931723 : CollatzResearch.WordTrace tailWord_2931723 prefixEnd_2931723 1003588696560892235986505 := by
  unfold tailWord_2931723
  simp only [CollatzResearch.WordTrace]
  refine ⟨106928722357875744270871823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71285814905250496180581215 106928722357875744270871823)
  ·
    refine ⟨160393083536813616406307735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106928722357875744270871823 160393083536813616406307735)
    ·
      refine ⟨240589625305220424609461603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160393083536813616406307735 240589625305220424609461603)
      ·
        refine ⟨360884437957830636914192405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240589625305220424609461603 360884437957830636914192405)
        ·
          refine ⟨16916458029273311105352769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 360884437957830636914192405 16916458029273311105352769)
          ·
            refine ⟨12687343521954983329014577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16916458029273311105352769 12687343521954983329014577)
            ·
              refine ⟨9515507641466237496760933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12687343521954983329014577 9515507641466237496760933)
              ·
                refine ⟨1784157682774919530642675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9515507641466237496760933 1784157682774919530642675)
                ·
                  refine ⟨2676236524162379295964013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784157682774919530642675 2676236524162379295964013)
                  ·
                    refine ⟨1003588696560892235986505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676236524162379295964013 1003588696560892235986505)
                    ·
                      rfl

theorem cell22_2931723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 3].length) (baseStart_2931723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931723 prefixEnd_2931723 := by exact prefixLift 2931723
  have htrace : WordTrace (prefixWord ++ tailWord_2931723) baseStart_2931723 baseEnd_2931723 := by
    simpa [prefixWord, tailWord_2931723, baseEnd_2931723] using wordTrace_append hprefix tailTrace_2931723
  have hstable : (prefixWord ++ tailWord_2931723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931723).length < 2 ^ (prefixWord ++ tailWord_2931723).sum := by decide
  have hdescent : baseEnd_2931723 < baseStart_2931723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931781 : List Nat := [1, 3, 1, 1, 1, 3, 2, 6, 4]
def baseStart_2931781 : Nat := 118140960795 + 2931781 * 2 ^ 59
def prefixEnd_2931781 : Nat := 4983230072969 + 3 ^ 40 * 2931781 * 2
def baseEnd_2931781 : Nat := 334536183715399806012109

theorem tailTrace_2931781 : CollatzResearch.WordTrace tailWord_2931781 prefixEnd_2931781 334536183715399806012109 := by
  unfold tailWord_2931781
  simp only [CollatzResearch.WordTrace]
  refine ⟨106930837791665620176483197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71287225194443746784322131 106930837791665620176483197)
  ·
    refine ⟨40099064171874607566181199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106930837791665620176483197 40099064171874607566181199)
    ·
      refine ⟨60148596257811911349271799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40099064171874607566181199 60148596257811911349271799)
      ·
        refine ⟨90222894386717867023907699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60148596257811911349271799 90222894386717867023907699)
        ·
          refine ⟨135334341580076800535861549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90222894386717867023907699 135334341580076800535861549)
          ·
            refine ⟨50750378092528800200948081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135334341580076800535861549 50750378092528800200948081)
            ·
              refine ⟨38062783569396600150711061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50750378092528800200948081 38062783569396600150711061)
              ·
                refine ⟨1784192979815465632064581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38062783569396600150711061 1784192979815465632064581)
                ·
                  refine ⟨334536183715399806012109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784192979815465632064581 334536183715399806012109)
                  ·
                    rfl

theorem cell22_2931781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_2931781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931781 prefixEnd_2931781 := by exact prefixLift 2931781
  have htrace : WordTrace (prefixWord ++ tailWord_2931781) baseStart_2931781 baseEnd_2931781 := by
    simpa [prefixWord, tailWord_2931781, baseEnd_2931781] using wordTrace_append hprefix tailTrace_2931781
  have hstable : (prefixWord ++ tailWord_2931781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931781).length < 2 ^ (prefixWord ++ tailWord_2931781).sum := by decide
  have hdescent : baseEnd_2931781 < baseStart_2931781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931809 : List Nat := [1, 2, 3, 1, 1, 2, 4, 8]
def baseStart_2931809 : Nat := 118140960795 + 2931809 * 2 ^ 59
def prefixEnd_2931809 : Nat := 4983230072969 + 3 ^ 40 * 2931809 * 2
def baseEnd_2931809 : Nat := 111513126235379630926249

theorem tailTrace_2931809 : CollatzResearch.WordTrace tailWord_2931809 prefixEnd_2931809 111513126235379630926249 := by
  unfold tailWord_2931809
  simp only [CollatzResearch.WordTrace]
  refine ⟨106931859035564180958502481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71287906023709453972334987 106931859035564180958502481)
  ·
    refine ⟨80198894276673135718876861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106931859035564180958502481 80198894276673135718876861)
    ·
      refine ⟨30074585353752425894578823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80198894276673135718876861 30074585353752425894578823)
      ·
        refine ⟨45111878030628638841868235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30074585353752425894578823 45111878030628638841868235)
        ·
          refine ⟨67667817045942958262802353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45111878030628638841868235 67667817045942958262802353)
          ·
            refine ⟨50750862784457218697101765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67667817045942958262802353 50750862784457218697101765)
            ·
              refine ⟨9515786772085728505706581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50750862784457218697101765 9515786772085728505706581)
              ·
                refine ⟨111513126235379630926249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9515786772085728505706581 111513126235379630926249)
                ·
                  rfl

theorem cell22_2931809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 8].length) (baseStart_2931809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931809 prefixEnd_2931809 := by exact prefixLift 2931809
  have htrace : WordTrace (prefixWord ++ tailWord_2931809) baseStart_2931809 baseEnd_2931809 := by
    simpa [prefixWord, tailWord_2931809, baseEnd_2931809] using wordTrace_append hprefix tailTrace_2931809
  have hstable : (prefixWord ++ tailWord_2931809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931809).length < 2 ^ (prefixWord ++ tailWord_2931809).sum := by decide
  have hdescent : baseEnd_2931809 < baseStart_2931809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931830 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_2931830 : Nat := 118140960795 + 2931830 * 2 ^ 59
def prefixEnd_2931830 : Nat := 4983230072969 + 3 ^ 40 * 2931830 * 2
def baseEnd_2931830 : Nat := 1003625324847579623561177

theorem tailTrace_2931830 : CollatzResearch.WordTrace tailWord_2931830 prefixEnd_2931830 1003625324847579623561177 := by
  unfold tailWord_2931830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683289060530506346563559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71288416645658734363344629 6683289060530506346563559)
  ·
    refine ⟨10024933590795759519845339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6683289060530506346563559 10024933590795759519845339)
    ·
      refine ⟨15037400386193639279768009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10024933590795759519845339 15037400386193639279768009)
      ·
        refine ⟨11278050289645229459826007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15037400386193639279768009 11278050289645229459826007)
        ·
          refine ⟨16917075434467844189739011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11278050289645229459826007 16917075434467844189739011)
          ·
            refine ⟨25375613151701766284608517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16917075434467844189739011 25375613151701766284608517)
            ·
              refine ⟨4757927465944081178364097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25375613151701766284608517 4757927465944081178364097)
              ·
                refine ⟨3568445599458060883773073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4757927465944081178364097 3568445599458060883773073)
                ·
                  refine ⟨2676334199593545662829805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3568445599458060883773073 2676334199593545662829805)
                  ·
                    refine ⟨1003625324847579623561177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676334199593545662829805 1003625324847579623561177)
                    ·
                      rfl

theorem cell22_2931830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_2931830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931830 prefixEnd_2931830 := by exact prefixLift 2931830
  have htrace : WordTrace (prefixWord ++ tailWord_2931830) baseStart_2931830 baseEnd_2931830 := by
    simpa [prefixWord, tailWord_2931830, baseEnd_2931830] using wordTrace_append hprefix tailTrace_2931830
  have hstable : (prefixWord ++ tailWord_2931830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931830).length < 2 ^ (prefixWord ++ tailWord_2931830).sum := by decide
  have hdescent : baseEnd_2931830 < baseStart_2931830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931858 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2931858 : Nat := 118140960795 + 2931858 * 2 ^ 59
def prefixEnd_2931858 : Nat := 4983230072969 + 3 ^ 40 * 2931858 * 2
def baseEnd_2931858 : Nat := 1003634909819796883861091

theorem tailTrace_2931858 : CollatzResearch.WordTrace tailWord_2931858 prefixEnd_2931858 1003634909819796883861091 := by
  unfold tailWord_2931858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26733411553096665581759057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71289097474924441551357485 26733411553096665581759057)
  ·
    refine ⟨20050058664822499186319293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26733411553096665581759057 20050058664822499186319293)
    ·
      refine ⟨7518771999308437194869735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20050058664822499186319293 7518771999308437194869735)
      ·
        refine ⟨11278157998962655792304603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7518771999308437194869735 11278157998962655792304603)
        ·
          refine ⟨16917236998443983688456905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11278157998962655792304603 16917236998443983688456905)
          ·
            refine ⟨12687927748832987766342679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16917236998443983688456905 12687927748832987766342679)
            ·
              refine ⟨19031891623249481649514019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12687927748832987766342679 19031891623249481649514019)
              ·
                refine ⟨28547837434874222474271029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19031891623249481649514019 28547837434874222474271029)
                ·
                  refine ⟨2676359759519458356962909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28547837434874222474271029 2676359759519458356962909)
                  ·
                    refine ⟨1003634909819796883861091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676359759519458356962909 1003634909819796883861091)
                    ·
                      rfl

theorem cell22_2931858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2931858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931858 prefixEnd_2931858 := by exact prefixLift 2931858
  have htrace : WordTrace (prefixWord ++ tailWord_2931858) baseStart_2931858 baseEnd_2931858 := by
    simpa [prefixWord, tailWord_2931858, baseEnd_2931858] using wordTrace_append hprefix tailTrace_2931858
  have hstable : (prefixWord ++ tailWord_2931858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931858).length < 2 ^ (prefixWord ++ tailWord_2931858).sum := by decide
  have hdescent : baseEnd_2931858 < baseStart_2931858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931901 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_2931901 : Nat := 118140960795 + 2931901 * 2 ^ 59
def prefixEnd_2931901 : Nat := 4983230072969 + 3 ^ 40 * 2931901 * 2
def baseEnd_2931901 : Nat := 1003649629598559105035959

theorem tailTrace_2931901 : CollatzResearch.WordTrace tailWord_2931901 prefixEnd_2931901 1003649629598559105035959 := by
  unfold tailWord_2931901
  simp only [CollatzResearch.WordTrace]
  refine ⟨106935214551230880670851557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71290143034153920447234371 106935214551230880670851557)
  ·
    refine ⟨20050352728355790125784667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106935214551230880670851557 20050352728355790125784667)
    ·
      refine ⟨30075529092533685188677001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20050352728355790125784667 30075529092533685188677001)
      ·
        refine ⟨22556646819400263891507751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30075529092533685188677001 22556646819400263891507751)
        ·
          refine ⟨33834970229100395837261627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22556646819400263891507751 33834970229100395837261627)
          ·
            refine ⟨50752455343650593755892441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33834970229100395837261627 50752455343650593755892441)
            ·
              refine ⟨38064341507737945316919331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50752455343650593755892441 38064341507737945316919331)
              ·
                refine ⟨57096512261606917975378997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38064341507737945316919331 57096512261606917975378997)
                ·
                  refine ⟨5352798024525648560191781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57096512261606917975378997 5352798024525648560191781)
                  ·
                    refine ⟨1003649629598559105035959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5352798024525648560191781 1003649629598559105035959)
                    ·
                      rfl

theorem cell22_2931901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_2931901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931901 prefixEnd_2931901 := by exact prefixLift 2931901
  have htrace : WordTrace (prefixWord ++ tailWord_2931901) baseStart_2931901 baseEnd_2931901 := by
    simpa [prefixWord, tailWord_2931901, baseEnd_2931901] using wordTrace_append hprefix tailTrace_2931901
  have hstable : (prefixWord ++ tailWord_2931901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931901).length < 2 ^ (prefixWord ++ tailWord_2931901).sum := by decide
  have hdescent : baseEnd_2931901 < baseStart_2931901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931926 : List Nat := [5, 2, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2931926 : Nat := 118140960795 + 2931926 * 2 ^ 59
def prefixEnd_2931926 : Nat := 4983230072969 + 3 ^ 40 * 2931926 * 2
def baseEnd_2931926 : Nat := 1003658187609467373160883

theorem tailTrace_2931926 : CollatzResearch.WordTrace tailWord_2931926 prefixEnd_2931926 1003658187609467373160883 := by
  unfold tailWord_2931926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683507898508769371281977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71290750917426873293674421 6683507898508769371281977)
  ·
    refine ⟨5012630923881577028461483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6683507898508769371281977 5012630923881577028461483)
    ·
      refine ⟨7518946385822365542692225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5012630923881577028461483 7518946385822365542692225)
      ·
        refine ⟨5639209789366774157019169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7518946385822365542692225 5639209789366774157019169)
        ·
          refine ⟨4229407342025080617764377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5639209789366774157019169 4229407342025080617764377)
          ·
            refine ⟨3172055506518810463323283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4229407342025080617764377 3172055506518810463323283)
            ·
              refine ⟨4758083259778215694984925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172055506518810463323283 4758083259778215694984925)
              ·
                refine ⟨1784281222416830885619347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4758083259778215694984925 1784281222416830885619347)
                ·
                  refine ⟨2676421833625246328429021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784281222416830885619347 2676421833625246328429021)
                  ·
                    refine ⟨1003658187609467373160883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676421833625246328429021 1003658187609467373160883)
                    ·
                      rfl

theorem cell22_2931926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2931926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931926 prefixEnd_2931926 := by exact prefixLift 2931926
  have htrace : WordTrace (prefixWord ++ tailWord_2931926) baseStart_2931926 baseEnd_2931926 := by
    simpa [prefixWord, tailWord_2931926, baseEnd_2931926] using wordTrace_append hprefix tailTrace_2931926
  have hstable : (prefixWord ++ tailWord_2931926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931926).length < 2 ^ (prefixWord ++ tailWord_2931926).sum := by decide
  have hdescent : baseEnd_2931926 < baseStart_2931926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931948 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_2931948 : Nat := 118140960795 + 2931948 * 2 ^ 59
def prefixEnd_2931948 : Nat := 4983230072969 + 3 ^ 40 * 2931948 * 2
def baseEnd_2931948 : Nat := 1003665718659066649110815

theorem tailTrace_2931948 : CollatzResearch.WordTrace tailWord_2931948 prefixEnd_2931948 1003665718659066649110815 := by
  unfold tailWord_2931948
  simp only [CollatzResearch.WordTrace]
  refine ⟨53468464391030303848906249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71291285854707071798541665 53468464391030303848906249)
  ·
    refine ⟨40101348293272727886679687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53468464391030303848906249 40101348293272727886679687)
    ·
      refine ⟨60152022439909091830019531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40101348293272727886679687 60152022439909091830019531)
      ·
        refine ⟨90228033659863637745029297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60152022439909091830019531 90228033659863637745029297)
        ·
          refine ⟨67671025244897728308771973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90228033659863637745029297 67671025244897728308771973)
          ·
            refine ⟨12688317233418324057894745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67671025244897728308771973 12688317233418324057894745)
            ·
              refine ⟨9516237925063743043421059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12688317233418324057894745 9516237925063743043421059)
              ·
                refine ⟨14274356887595614565131589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9516237925063743043421059 14274356887595614565131589)
                ·
                  refine ⟨2676441916424177730962173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14274356887595614565131589 2676441916424177730962173)
                  ·
                    refine ⟨1003665718659066649110815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676441916424177730962173 1003665718659066649110815)
                    ·
                      rfl

theorem cell22_2931948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_2931948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931948 prefixEnd_2931948 := by exact prefixLift 2931948
  have htrace : WordTrace (prefixWord ++ tailWord_2931948) baseStart_2931948 baseEnd_2931948 := by
    simpa [prefixWord, tailWord_2931948, baseEnd_2931948] using wordTrace_append hprefix tailTrace_2931948
  have hstable : (prefixWord ++ tailWord_2931948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931948).length < 2 ^ (prefixWord ++ tailWord_2931948).sum := by decide
  have hdescent : baseEnd_2931948 < baseStart_2931948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931956 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2931956 : Nat := 118140960795 + 2931956 * 2 ^ 59
def prefixEnd_2931956 : Nat := 4983230072969 + 3 ^ 40 * 2931956 * 2
def baseEnd_2931956 : Nat := 334556152407519098303597

theorem tailTrace_2931956 : CollatzResearch.WordTrace tailWord_2931956 prefixEnd_2931956 334556152407519098303597 := by
  unfold tailWord_2931956
  simp only [CollatzResearch.WordTrace]
  refine ⟨53468610283015812532051861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71291480377354416709402481 53468610283015812532051861)
  ·
    refine ⟨2506341107016366212439931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53468610283015812532051861 2506341107016366212439931)
    ·
      refine ⟨3759511660524549318659897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2506341107016366212439931 3759511660524549318659897)
      ·
        refine ⟨2819633745393411988994923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3759511660524549318659897 2819633745393411988994923)
        ·
          refine ⟨4229450618090117983492385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2819633745393411988994923 4229450618090117983492385)
          ·
            refine ⟨3172087963567588487619289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4229450618090117983492385 3172087963567588487619289)
            ·
              refine ⟨2379065972675691365714467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3172087963567588487619289 2379065972675691365714467)
              ·
                refine ⟨3568598959013537048571701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379065972675691365714467 3568598959013537048571701)
                ·
                  refine ⟨334556152407519098303597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3568598959013537048571701 334556152407519098303597)
                  ·
                    rfl

theorem cell22_2931956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2931956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931956 prefixEnd_2931956 := by exact prefixLift 2931956
  have htrace : WordTrace (prefixWord ++ tailWord_2931956) baseStart_2931956 baseEnd_2931956 := by
    simpa [prefixWord, tailWord_2931956, baseEnd_2931956] using wordTrace_append hprefix tailTrace_2931956
  have hstable : (prefixWord ++ tailWord_2931956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931956).length < 2 ^ (prefixWord ++ tailWord_2931956).sum := by decide
  have hdescent : baseEnd_2931956 < baseStart_2931956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931961 : List Nat := [1, 2, 1, 3, 1, 1, 6, 7]
def baseStart_2931961 : Nat := 118140960795 + 2931961 * 2 ^ 59
def prefixEnd_2931961 : Nat := 4983230072969 + 3 ^ 40 * 2931961 * 2
def baseEnd_2931961 : Nat := 111518907647193216503975

theorem tailTrace_2931961 : CollatzResearch.WordTrace tailWord_2931961 prefixEnd_2931961 111518907647193216503975 := by
  unfold tailWord_2931961
  simp only [CollatzResearch.WordTrace]
  refine ⟨106937402931013510918035737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71291601954009007278690491 106937402931013510918035737)
  ·
    refine ⟨80203052198260133188526803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106937402931013510918035737 80203052198260133188526803)
    ·
      refine ⟨120304578297390199782790205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80203052198260133188526803 120304578297390199782790205)
      ·
        refine ⟨45114216861521324918546327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120304578297390199782790205 45114216861521324918546327)
        ·
          refine ⟨67671325292281987377819491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45114216861521324918546327 67671325292281987377819491)
          ·
            refine ⟨101506987938422981066729237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67671325292281987377819491 101506987938422981066729237)
            ·
              refine ⟨4758140059613577237502933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101506987938422981066729237 4758140059613577237502933)
              ·
                refine ⟨111518907647193216503975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4758140059613577237502933 111518907647193216503975)
                ·
                  rfl

theorem cell22_2931961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 7].length) (baseStart_2931961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2931961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2931961 prefixEnd_2931961 := by exact prefixLift 2931961
  have htrace : WordTrace (prefixWord ++ tailWord_2931961) baseStart_2931961 baseEnd_2931961 := by
    simpa [prefixWord, tailWord_2931961, baseEnd_2931961] using wordTrace_append hprefix tailTrace_2931961
  have hstable : (prefixWord ++ tailWord_2931961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931961).length < 2 ^ (prefixWord ++ tailWord_2931961).sum := by decide
  have hdescent : baseEnd_2931961 < baseStart_2931961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932008 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2932008 : Nat := 118140960795 + 2932008 * 2 ^ 59
def prefixEnd_2932008 : Nat := 4983230072969 + 3 ^ 40 * 2932008 * 2
def baseEnd_2932008 : Nat := 1003686257885246492610631

theorem tailTrace_2932008 : CollatzResearch.WordTrace tailWord_2932008 prefixEnd_2932008 1003686257885246492610631 := by
  unfold tailWord_2932008
  simp only [CollatzResearch.WordTrace]
  refine ⟨53469558580921618972498339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71292744774562158629997785 53469558580921618972498339)
  ·
    refine ⟨80204337871382428458747509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53469558580921618972498339 80204337871382428458747509)
    ·
      refine ⟨7519156675442102668007579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80204337871382428458747509 7519156675442102668007579)
      ·
        refine ⟨11278735013163154002011369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7519156675442102668007579 11278735013163154002011369)
        ·
          refine ⟨8459051259872365501508527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11278735013163154002011369 8459051259872365501508527)
          ·
            refine ⟨12688576889808548252262791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8459051259872365501508527 12688576889808548252262791)
            ·
              refine ⟨19032865334712822378394187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12688576889808548252262791 19032865334712822378394187)
              ·
                refine ⟨28549298002069233567591281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19032865334712822378394187 28549298002069233567591281)
                ·
                  refine ⟨21411973501551925175693461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28549298002069233567591281 21411973501551925175693461)
                  ·
                    refine ⟨1003686257885246492610631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21411973501551925175693461 1003686257885246492610631)
                    ·
                      rfl

theorem cell22_2932008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2932008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932008 prefixEnd_2932008 := by exact prefixLift 2932008
  have htrace : WordTrace (prefixWord ++ tailWord_2932008) baseStart_2932008 baseEnd_2932008 := by
    simpa [prefixWord, tailWord_2932008, baseEnd_2932008] using wordTrace_append hprefix tailTrace_2932008
  have hstable : (prefixWord ++ tailWord_2932008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932008).length < 2 ^ (prefixWord ++ tailWord_2932008).sum := by decide
  have hdescent : baseEnd_2932008 < baseStart_2932008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932051 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 8]
def baseStart_2932051 : Nat := 118140960795 + 2932051 * 2 ^ 59
def prefixEnd_2932051 : Nat := 4983230072969 + 3 ^ 40 * 2932051 * 2
def baseEnd_2932051 : Nat := 334566992554669571261833

theorem tailTrace_2932051 : CollatzResearch.WordTrace tailWord_2932051 prefixEnd_2932051 334566992554669571261833 := by
  unfold tailWord_2932051
  simp only [CollatzResearch.WordTrace]
  refine ⟨106940685500687456288812007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71293790333791637525874671 106940685500687456288812007)
  ·
    refine ⟨160411028251031184433218011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106940685500687456288812007 160411028251031184433218011)
    ·
      refine ⟨240616542376546776649827017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160411028251031184433218011 240616542376546776649827017)
      ·
        refine ⟨180462406782410082487370263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240616542376546776649827017 180462406782410082487370263)
        ·
          refine ⟨270693610173615123731055395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180462406782410082487370263 270693610173615123731055395)
          ·
            refine ⟨406040415260422685596583093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270693610173615123731055395 406040415260422685596583093)
            ·
              refine ⟨38066288930664626774679665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 406040415260422685596583093 38066288930664626774679665)
              ·
                refine ⟨28549716697998470081009749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38066288930664626774679665 28549716697998470081009749)
                ·
                  refine ⟨334566992554669571261833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28549716697998470081009749 334566992554669571261833)
                  ·
                    rfl

theorem cell22_2932051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 8].length) (baseStart_2932051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932051 prefixEnd_2932051 := by exact prefixLift 2932051
  have htrace : WordTrace (prefixWord ++ tailWord_2932051) baseStart_2932051 baseEnd_2932051 := by
    simpa [prefixWord, tailWord_2932051, baseEnd_2932051] using wordTrace_append hprefix tailTrace_2932051
  have hstable : (prefixWord ++ tailWord_2932051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932051).length < 2 ^ (prefixWord ++ tailWord_2932051).sum := by decide
  have hdescent : baseEnd_2932051 < baseStart_2932051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932061 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2932061 : Nat := 118140960795 + 2932061 * 2 ^ 59
def prefixEnd_2932061 : Nat := 4983230072969 + 3 ^ 40 * 2932061 * 2
def baseEnd_2932061 : Nat := 1003704400868372021035469

theorem tailTrace_2932061 : CollatzResearch.WordTrace tailWord_2932061 prefixEnd_2932061 1003704400868372021035469 := by
  unfold tailWord_2932061
  simp only [CollatzResearch.WordTrace]
  refine ⟨106941050230651227996676037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71294033487100818664450691 106941050230651227996676037)
  ·
    refine ⟨20051446918247105249376757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106941050230651227996676037 20051446918247105249376757)
    ·
      refine ⟨1879823148585666117129071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20051446918247105249376757 1879823148585666117129071)
      ·
        refine ⟨2819734722878499175693607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879823148585666117129071 2819734722878499175693607)
        ·
          refine ⟨4229602084317748763540411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2819734722878499175693607 4229602084317748763540411)
          ·
            refine ⟨6344403126476623145310617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229602084317748763540411 6344403126476623145310617)
            ·
              refine ⟨4758302344857467358982963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6344403126476623145310617 4758302344857467358982963)
              ·
                refine ⟨7137453517286201038474445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4758302344857467358982963 7137453517286201038474445)
                ·
                  refine ⟨2676545068982325389427917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7137453517286201038474445 2676545068982325389427917)
                  ·
                    refine ⟨1003704400868372021035469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676545068982325389427917 1003704400868372021035469)
                    ·
                      rfl

theorem cell22_2932061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2932061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932061 prefixEnd_2932061 := by exact prefixLift 2932061
  have htrace : WordTrace (prefixWord ++ tailWord_2932061) baseStart_2932061 baseEnd_2932061 := by
    simpa [prefixWord, tailWord_2932061, baseEnd_2932061] using wordTrace_append hprefix tailTrace_2932061
  have hstable : (prefixWord ++ tailWord_2932061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932061).length < 2 ^ (prefixWord ++ tailWord_2932061).sum := by decide
  have hdescent : baseEnd_2932061 < baseStart_2932061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932068 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 6]
def baseStart_2932068 : Nat := 118140960795 + 2932068 * 2 ^ 59
def prefixEnd_2932068 : Nat := 4983230072969 + 3 ^ 40 * 2932068 * 2
def baseEnd_2932068 : Nat := 334568932370475445370149

theorem tailTrace_2932068 : CollatzResearch.WordTrace tailWord_2932068 prefixEnd_2932068 334568932370475445370149 := by
  unfold tailWord_2932068
  simp only [CollatzResearch.WordTrace]
  refine ⟨53470652770812934096090429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71294203694417245461453905 53470652770812934096090429)
  ·
    refine ⟨20051494789054850286033911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53470652770812934096090429 20051494789054850286033911)
    ·
      refine ⟨30077242183582275429050867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20051494789054850286033911 30077242183582275429050867)
      ·
        refine ⟨45115863275373413143576301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30077242183582275429050867 45115863275373413143576301)
        ·
          refine ⟨16918448728265029928841113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45115863275373413143576301 16918448728265029928841113)
          ·
            refine ⟨12688836546198772446630835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16918448728265029928841113 12688836546198772446630835)
            ·
              refine ⟨19033254819298158669946253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12688836546198772446630835 19033254819298158669946253)
              ·
                refine ⟨7137470557236809501229845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19033254819298158669946253 7137470557236809501229845)
                ·
                  refine ⟨334568932370475445370149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7137470557236809501229845 334568932370475445370149)
                  ·
                    rfl

theorem cell22_2932068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_2932068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932068 prefixEnd_2932068 := by exact prefixLift 2932068
  have htrace : WordTrace (prefixWord ++ tailWord_2932068) baseStart_2932068 baseEnd_2932068 := by
    simpa [prefixWord, tailWord_2932068, baseEnd_2932068] using wordTrace_append hprefix tailTrace_2932068
  have hstable : (prefixWord ++ tailWord_2932068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932068).length < 2 ^ (prefixWord ++ tailWord_2932068).sum := by decide
  have hdescent : baseEnd_2932068 < baseStart_2932068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932083 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 8, 3]
def baseStart_2932083 : Nat := 118140960795 + 2932083 * 2 ^ 59
def prefixEnd_2932083 : Nat := 4983230072969 + 3 ^ 40 * 2932083 * 2
def baseEnd_2932083 : Nat := 1003711931917971296985401

theorem tailTrace_2932083 : CollatzResearch.WordTrace tailWord_2932083 prefixEnd_2932083 1003711931917971296985401 := by
  unfold tailWord_2932083
  simp only [CollatzResearch.WordTrace]
  refine ⟨106941852636571525753976903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71294568424381017169317935 106941852636571525753976903)
  ·
    refine ⟨160412778954857288630965355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106941852636571525753976903 160412778954857288630965355)
    ·
      refine ⟨240619168432285932946448033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160412778954857288630965355 240619168432285932946448033)
      ·
        refine ⟨180464376324214449709836025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240619168432285932946448033 180464376324214449709836025)
        ·
          refine ⟨135348282243160837282377019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180464376324214449709836025 135348282243160837282377019)
          ·
            refine ⟨203022423364741255923565529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135348282243160837282377019 203022423364741255923565529)
            ·
              refine ⟨152266817523555941942674147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203022423364741255923565529 152266817523555941942674147)
              ·
                refine ⟨228400226285333912914011221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152266817523555941942674147 228400226285333912914011221)
                ·
                  refine ⟨2676565151781256791961069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 228400226285333912914011221 2676565151781256791961069)
                  ·
                    refine ⟨1003711931917971296985401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676565151781256791961069 1003711931917971296985401)
                    ·
                      rfl

theorem cell22_2932083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 3].length) (baseStart_2932083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932083 prefixEnd_2932083 := by exact prefixLift 2932083
  have htrace : WordTrace (prefixWord ++ tailWord_2932083) baseStart_2932083 baseEnd_2932083 := by
    simpa [prefixWord, tailWord_2932083, baseEnd_2932083] using wordTrace_append hprefix tailTrace_2932083
  have hstable : (prefixWord ++ tailWord_2932083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932083).length < 2 ^ (prefixWord ++ tailWord_2932083).sum := by decide
  have hdescent : baseEnd_2932083 < baseStart_2932083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932100 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_2932100 : Nat := 118140960795 + 2932100 * 2 ^ 59
def prefixEnd_2932100 : Nat := 4983230072969 + 3 ^ 40 * 2932100 * 2
def baseEnd_2932100 : Nat := 1003717751365388919310349

theorem tailTrace_2932100 : CollatzResearch.WordTrace tailWord_2932100 prefixEnd_2932100 1003717751365388919310349 := by
  unfold tailWord_2932100
  simp only [CollatzResearch.WordTrace]
  refine ⟨53471236338754968828672877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71294981785006625104897169 53471236338754968828672877)
  ·
    refine ⟨20051713627033113310752329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53471236338754968828672877 20051713627033113310752329)
    ·
      refine ⟨15038785220274834983064247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20051713627033113310752329 15038785220274834983064247)
      ·
        refine ⟨22558177830412252474596371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15038785220274834983064247 22558177830412252474596371)
        ·
          refine ⟨33837266745618378711894557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22558177830412252474596371 33837266745618378711894557)
          ·
            refine ⟨12688975029606892016960459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33837266745618378711894557 12688975029606892016960459)
            ·
              refine ⟨19033462544410338025440689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12688975029606892016960459 19033462544410338025440689)
              ·
                refine ⟨14275096908307753519080517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19033462544410338025440689 14275096908307753519080517)
                ·
                  refine ⟨2676580670307703784827597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14275096908307753519080517 2676580670307703784827597)
                  ·
                    refine ⟨1003717751365388919310349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676580670307703784827597 1003717751365388919310349)
                    ·
                      rfl

theorem cell22_2932100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_2932100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932100 prefixEnd_2932100 := by exact prefixLift 2932100
  have htrace : WordTrace (prefixWord ++ tailWord_2932100) baseStart_2932100 baseEnd_2932100 := by
    simpa [prefixWord, tailWord_2932100, baseEnd_2932100] using wordTrace_append hprefix tailTrace_2932100
  have hstable : (prefixWord ++ tailWord_2932100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932100).length < 2 ^ (prefixWord ++ tailWord_2932100).sum := by decide
  have hdescent : baseEnd_2932100 < baseStart_2932100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932130 : List Nat := [3, 3, 1, 2, 1, 3, 2, 7]
def baseStart_2932130 : Nat := 118140960795 + 2932130 * 2 ^ 59
def prefixEnd_2932130 : Nat := 4983230072969 + 3 ^ 40 * 2932130 * 2
def baseEnd_2932130 : Nat := 111525335664275426784473

theorem tailTrace_2932130 : CollatzResearch.WordTrace tailWord_2932130 prefixEnd_2932130 111525335664275426784473 := by
  unfold tailWord_2932130
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735891716850313195234461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71295711244934168520625229 26735891716850313195234461)
  ·
    refine ⟨10025959393818867448212923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26735891716850313195234461 10025959393818867448212923)
    ·
      refine ⟨15038939090728301172319385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10025959393818867448212923 15038939090728301172319385)
      ·
        refine ⟨11279204318046225879239539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15038939090728301172319385 11279204318046225879239539)
        ·
          refine ⟨16918806477069338818859309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11279204318046225879239539 16918806477069338818859309)
          ·
            refine ⟨6344552428901002057072241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16918806477069338818859309 6344552428901002057072241)
            ·
              refine ⟨4758414321675751542804181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6344552428901002057072241 4758414321675751542804181)
              ·
                refine ⟨111525335664275426784473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4758414321675751542804181 111525335664275426784473)
                ·
                  rfl

theorem cell22_2932130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_2932130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932130 prefixEnd_2932130 := by exact prefixLift 2932130
  have htrace : WordTrace (prefixWord ++ tailWord_2932130) baseStart_2932130 baseEnd_2932130 := by
    simpa [prefixWord, tailWord_2932130, baseEnd_2932130] using wordTrace_append hprefix tailTrace_2932130
  have hstable : (prefixWord ++ tailWord_2932130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932130).length < 2 ^ (prefixWord ++ tailWord_2932130).sum := by decide
  have hdescent : baseEnd_2932130 < baseStart_2932130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932145 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 5, 3]
def baseStart_2932145 : Nat := 118140960795 + 2932145 * 2 ^ 59
def prefixEnd_2932145 : Nat := 4983230072969 + 3 ^ 40 * 2932145 * 2
def baseEnd_2932145 : Nat := 1003733155785023801935211

theorem tailTrace_2932145 : CollatzResearch.WordTrace tailWord_2932145 prefixEnd_2932145 1003733155785023801935211 := by
  unfold tailWord_2932145
  simp only [CollatzResearch.WordTrace]
  refine ⟨106944113962346910342733889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71296075974897940228489259 106944113962346910342733889)
  ·
    refine ⟨80208085471760182757050417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106944113962346910342733889 80208085471760182757050417)
    ·
      refine ⟨60156064103820137067787813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80208085471760182757050417 60156064103820137067787813)
      ·
        refine ⟨11279262019466275700210215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60156064103820137067787813 11279262019466275700210215)
        ·
          refine ⟨16918893029199413550315323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11279262019466275700210215 16918893029199413550315323)
          ·
            refine ⟨25378339543799120325472985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16918893029199413550315323 25378339543799120325472985)
            ·
              refine ⟨19033754657849340244104739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25378339543799120325472985 19033754657849340244104739)
              ·
                refine ⟨28550631986774010366157109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19033754657849340244104739 28550631986774010366157109)
                ·
                  refine ⟨2676621748760063471827229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28550631986774010366157109 2676621748760063471827229)
                  ·
                    refine ⟨1003733155785023801935211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676621748760063471827229 1003733155785023801935211)
                    ·
                      rfl

theorem cell22_2932145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_2932145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932145 prefixEnd_2932145 := by exact prefixLift 2932145
  have htrace : WordTrace (prefixWord ++ tailWord_2932145) baseStart_2932145 baseEnd_2932145 := by
    simpa [prefixWord, tailWord_2932145, baseEnd_2932145] using wordTrace_append hprefix tailTrace_2932145
  have hstable : (prefixWord ++ tailWord_2932145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932145).length < 2 ^ (prefixWord ++ tailWord_2932145).sum := by decide
  have hdescent : baseEnd_2932145 < baseStart_2932145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932355 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 6]
def baseStart_2932355 : Nat := 118140960795 + 2932355 * 2 ^ 59
def prefixEnd_2932355 : Nat := 4983230072969 + 3 ^ 40 * 2932355 * 2
def baseEnd_2932355 : Nat := 334601681025551084728189

theorem tailTrace_2932355 : CollatzResearch.WordTrace tailWord_2932355 prefixEnd_2932355 334601681025551084728189 := by
  unfold tailWord_2932355
  simp only [CollatzResearch.WordTrace]
  refine ⟨106951773291586116207878519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71301182194390744138585679 106951773291586116207878519)
  ·
    refine ⟨160427659937379174311817779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106951773291586116207878519 160427659937379174311817779)
    ·
      refine ⟨240641489906068761467726669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160427659937379174311817779 240641489906068761467726669)
      ·
        refine ⟨90240558714775785550397501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240641489906068761467726669 90240558714775785550397501)
        ·
          refine ⟨33840209518040919581399063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90240558714775785550397501 33840209518040919581399063)
          ·
            refine ⟨50760314277061379372098595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33840209518040919581399063 50760314277061379372098595)
            ·
              refine ⟨76140471415592069058147893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50760314277061379372098595 76140471415592069058147893)
              ·
                refine ⟨7138169195211756474201365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76140471415592069058147893 7138169195211756474201365)
                ·
                  refine ⟨334601681025551084728189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7138169195211756474201365 334601681025551084728189)
                  ·
                    rfl

theorem cell22_2932355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 6].length) (baseStart_2932355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932355 prefixEnd_2932355 := by exact prefixLift 2932355
  have htrace : WordTrace (prefixWord ++ tailWord_2932355) baseStart_2932355 baseEnd_2932355 := by
    simpa [prefixWord, tailWord_2932355, baseEnd_2932355] using wordTrace_append hprefix tailTrace_2932355
  have hstable : (prefixWord ++ tailWord_2932355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932355).length < 2 ^ (prefixWord ++ tailWord_2932355).sum := by decide
  have hdescent : baseEnd_2932355 < baseStart_2932355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932387 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 4, 3]
def baseStart_2932387 : Nat := 118140960795 + 2932387 * 2 ^ 59
def prefixEnd_2932387 : Nat := 4983230072969 + 3 ^ 40 * 2932387 * 2
def baseEnd_2932387 : Nat := 1003815997330615837384469

theorem tailTrace_2932387 : CollatzResearch.WordTrace tailWord_2932387 prefixEnd_2932387 1003815997330615837384469 := by
  unfold tailWord_2932387
  simp only [CollatzResearch.WordTrace]
  refine ⟨106952940427470185673043415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71301960284980123782028943 106952940427470185673043415)
  ·
    refine ⟨160429410641205278509565123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106952940427470185673043415 160429410641205278509565123)
    ·
      refine ⟨240644115961807917764347685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160429410641205278509565123 240644115961807917764347685)
      ·
        refine ⟨45120771742838984580815191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240644115961807917764347685 45120771742838984580815191)
        ·
          refine ⟨67681157614258476871222787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45120771742838984580815191 67681157614258476871222787)
          ·
            refine ⟨101521736421387715306834181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67681157614258476871222787 101521736421387715306834181)
            ·
              refine ⟨19035325579010196620031409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101521736421387715306834181 19035325579010196620031409)
              ·
                refine ⟨14276494184257647465023557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19035325579010196620031409 14276494184257647465023557)
                ·
                  refine ⟨2676842659548308899691917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14276494184257647465023557 2676842659548308899691917)
                  ·
                    refine ⟨1003815997330615837384469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676842659548308899691917 1003815997330615837384469)
                    ·
                      rfl

theorem cell22_2932387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 3].length) (baseStart_2932387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932387 prefixEnd_2932387 := by exact prefixLift 2932387
  have htrace : WordTrace (prefixWord ++ tailWord_2932387) baseStart_2932387 baseEnd_2932387 := by
    simpa [prefixWord, tailWord_2932387, baseEnd_2932387] using wordTrace_append hprefix tailTrace_2932387
  have hstable : (prefixWord ++ tailWord_2932387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932387).length < 2 ^ (prefixWord ++ tailWord_2932387).sum := by decide
  have hdescent : baseEnd_2932387 < baseStart_2932387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932402 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_2932402 : Nat := 118140960795 + 2932402 * 2 ^ 59
def prefixEnd_2932402 : Nat := 4983230072969 + 3 ^ 40 * 2932402 * 2
def baseEnd_2932402 : Nat := 1003821132137160798259423

theorem tailTrace_2932402 : CollatzResearch.WordTrace tailWord_2932402 prefixEnd_2932402 1003821132137160798259423 := by
  unfold tailWord_2932402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26738371880603960808709865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71302325014943895489892973 26738371880603960808709865)
  ·
    refine ⟨20053778910452970606532399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26738371880603960808709865 20053778910452970606532399)
    ·
      refine ⟨30080668365679455909798599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20053778910452970606532399 30080668365679455909798599)
      ·
        refine ⟨45121002548519183864697899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30080668365679455909798599 45121002548519183864697899)
        ·
          refine ⟨67681503822778775797046849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45121002548519183864697899 67681503822778775797046849)
          ·
            refine ⟨50761127867084081847785137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67681503822778775797046849 50761127867084081847785137)
            ·
              refine ⟨38070845900313061385838853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50761127867084081847785137 38070845900313061385838853)
              ·
                refine ⟨7138283606308699009844785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38070845900313061385838853 7138283606308699009844785)
                ·
                  refine ⟨5353712704731524257383589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7138283606308699009844785 5353712704731524257383589)
                  ·
                    refine ⟨1003821132137160798259423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5353712704731524257383589 1003821132137160798259423)
                    ·
                      rfl

theorem cell22_2932402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_2932402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932402 prefixEnd_2932402 := by exact prefixLift 2932402
  have htrace : WordTrace (prefixWord ++ tailWord_2932402) baseStart_2932402 baseEnd_2932402 := by
    simpa [prefixWord, tailWord_2932402, baseEnd_2932402] using wordTrace_append hprefix tailTrace_2932402
  have hstable : (prefixWord ++ tailWord_2932402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932402).length < 2 ^ (prefixWord ++ tailWord_2932402).sum := by decide
  have hdescent : baseEnd_2932402 < baseStart_2932402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932406 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2932406 : Nat := 118140960795 + 2932406 * 2 ^ 59
def prefixEnd_2932406 : Nat := 4983230072969 + 3 ^ 40 * 2932406 * 2
def baseEnd_2932406 : Nat := 334607500472968707053137

theorem tailTrace_2932406 : CollatzResearch.WordTrace tailWord_2932406 prefixEnd_2932406 334607500472968707053137 := by
  unfold tailWord_2932406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6684602088400084494874067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71302422276267567945323381 6684602088400084494874067)
  ·
    refine ⟨10026903132600126742311101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6684602088400084494874067 10026903132600126742311101)
    ·
      refine ⟨3760088674725047528366663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10026903132600126742311101 3760088674725047528366663)
      ·
        refine ⟨5640133012087571292549995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3760088674725047528366663 5640133012087571292549995)
        ·
          refine ⟨8460199518131356938824993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640133012087571292549995 8460199518131356938824993)
          ·
            refine ⟨6345149638598517704118745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8460199518131356938824993 6345149638598517704118745)
            ·
              refine ⟨4758862228948888278089059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6345149638598517704118745 4758862228948888278089059)
              ·
                refine ⟨7138293343423332417133589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4758862228948888278089059 7138293343423332417133589)
                ·
                  refine ⟨334607500472968707053137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7138293343423332417133589 334607500472968707053137)
                  ·
                    rfl

theorem cell22_2932406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2932406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932406 prefixEnd_2932406 := by exact prefixLift 2932406
  have htrace : WordTrace (prefixWord ++ tailWord_2932406) baseStart_2932406 baseEnd_2932406 := by
    simpa [prefixWord, tailWord_2932406, baseEnd_2932406] using wordTrace_append hprefix tailTrace_2932406
  have hstable : (prefixWord ++ tailWord_2932406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932406).length < 2 ^ (prefixWord ++ tailWord_2932406).sum := by decide
  have hdescent : baseEnd_2932406 < baseStart_2932406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932432 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 5, 3]
def baseStart_2932432 : Nat := 118140960795 + 2932432 * 2 ^ 59
def prefixEnd_2932432 : Nat := 4983230072969 + 3 ^ 40 * 2932432 * 2
def baseEnd_2932432 : Nat := 1003831401750250720009331

theorem tailTrace_2932432 : CollatzResearch.WordTrace tailWord_2932432 prefixEnd_2932432 1003831401750250720009331 := by
  unfold tailWord_2932432
  simp only [CollatzResearch.WordTrace]
  refine ⟨53477290856153579179215775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71303054474871438905621033 53477290856153579179215775)
  ·
    refine ⟨80215936284230368768823663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53477290856153579179215775 80215936284230368768823663)
    ·
      refine ⟨120323904426345553153235495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80215936284230368768823663 120323904426345553153235495)
      ·
        refine ⟨180485856639518329729853243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120323904426345553153235495 180485856639518329729853243)
        ·
          refine ⟨270728784959277494594779865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180485856639518329729853243 270728784959277494594779865)
          ·
            refine ⟨203046588719458120946084899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270728784959277494594779865 203046588719458120946084899)
            ·
              refine ⟨304569883079187181419127349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203046588719458120946084899 304569883079187181419127349)
              ·
                refine ⟨28553426538673798258043189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304569883079187181419127349 28553426538673798258043189)
                ·
                  refine ⟨2676883738000668586691549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28553426538673798258043189 2676883738000668586691549)
                  ·
                    refine ⟨1003831401750250720009331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2676883738000668586691549 1003831401750250720009331)
                    ·
                      rfl

theorem cell22_2932432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_2932432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932432 prefixEnd_2932432 := by exact prefixLift 2932432
  have htrace : WordTrace (prefixWord ++ tailWord_2932432) baseStart_2932432 baseEnd_2932432 := by
    simpa [prefixWord, tailWord_2932432, baseEnd_2932432] using wordTrace_append hprefix tailTrace_2932432
  have hstable : (prefixWord ++ tailWord_2932432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932432).length < 2 ^ (prefixWord ++ tailWord_2932432).sum := by decide
  have hdescent : baseEnd_2932432 < baseStart_2932432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932434 : List Nat := [3, 2, 2, 2, 2, 1, 4, 6]
def baseStart_2932434 : Nat := 118140960795 + 2932434 * 2 ^ 59
def prefixEnd_2932434 : Nat := 4983230072969 + 3 ^ 40 * 2932434 * 2
def baseEnd_2932434 : Nat := 111536898487902597939925

theorem tailTrace_2932434 : CollatzResearch.WordTrace tailWord_2932434 prefixEnd_2932434 111536898487902597939925 := by
  unfold tailWord_2932434
  simp only [CollatzResearch.WordTrace]
  refine ⟨26738663664574978175001089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71303103105533275133336237 26738663664574978175001089)
  ·
    refine ⟨20053997748431233631250817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26738663664574978175001089 20053997748431233631250817)
    ·
      refine ⟨15040498311323425223438113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20053997748431233631250817 15040498311323425223438113)
      ·
        refine ⟨11280373733492568917578585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15040498311323425223438113 11280373733492568917578585)
        ·
          refine ⟨8460280300119426688183939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11280373733492568917578585 8460280300119426688183939)
          ·
            refine ⟨12690420450179140032275909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8460280300119426688183939 12690420450179140032275909)
            ·
              refine ⟨2379453834408588756051733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12690420450179140032275909 2379453834408588756051733)
              ·
                refine ⟨111536898487902597939925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2379453834408588756051733 111536898487902597939925)
                ·
                  rfl

theorem cell22_2932434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_2932434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932434 prefixEnd_2932434 := by exact prefixLift 2932434
  have htrace : WordTrace (prefixWord ++ tailWord_2932434) baseStart_2932434 baseEnd_2932434 := by
    simpa [prefixWord, tailWord_2932434, baseEnd_2932434] using wordTrace_append hprefix tailTrace_2932434
  have hstable : (prefixWord ++ tailWord_2932434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932434).length < 2 ^ (prefixWord ++ tailWord_2932434).sum := by decide
  have hdescent : baseEnd_2932434 < baseStart_2932434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932462 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_2932462 : Nat := 118140960795 + 2932462 * 2 ^ 59
def prefixEnd_2932462 : Nat := 4983230072969 + 3 ^ 40 * 2932462 * 2
def baseEnd_2932462 : Nat := 334613890454446880586413

theorem tailTrace_2932462 : CollatzResearch.WordTrace tailWord_2932462 prefixEnd_2932462 334613890454446880586413 := by
  unfold tailWord_2932462
  simp only [CollatzResearch.WordTrace]
  refine ⟨13369459487774809185252955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71303783934798982321349093 13369459487774809185252955)
  ·
    refine ⟨20054189231662213777879433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13369459487774809185252955 20054189231662213777879433)
    ·
      refine ⟨15040641923746660333409575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20054189231662213777879433 15040641923746660333409575)
      ·
        refine ⟨22560962885619990500114363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15040641923746660333409575 22560962885619990500114363)
        ·
          refine ⟨33841444328429985750171545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22560962885619990500114363 33841444328429985750171545)
          ·
            refine ⟨25381083246322489312628659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33841444328429985750171545 25381083246322489312628659)
            ·
              refine ⟨38071624869483733968942989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25381083246322489312628659 38071624869483733968942989)
              ·
                refine ⟨14276859326056400238353621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38071624869483733968942989 14276859326056400238353621)
                ·
                  refine ⟨334613890454446880586413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14276859326056400238353621 334613890454446880586413)
                  ·
                    rfl

theorem cell22_2932462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_2932462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932462 prefixEnd_2932462 := by exact prefixLift 2932462
  have htrace : WordTrace (prefixWord ++ tailWord_2932462) baseStart_2932462 baseEnd_2932462 := by
    simpa [prefixWord, tailWord_2932462, baseEnd_2932462] using wordTrace_append hprefix tailTrace_2932462
  have hstable : (prefixWord ++ tailWord_2932462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932462).length < 2 ^ (prefixWord ++ tailWord_2932462).sum := by decide
  have hdescent : baseEnd_2932462 < baseStart_2932462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932479 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 5]
def baseStart_2932479 : Nat := 118140960795 + 2932479 * 2 ^ 59
def prefixEnd_2932479 : Nat := 4983230072969 + 3 ^ 40 * 2932479 * 2
def baseEnd_2932479 : Nat := 334615830270252754694729

theorem tailTrace_2932479 : CollatzResearch.WordTrace tailWord_2932479 prefixEnd_2932479 334615830270252754694729 := by
  unfold tailWord_2932479
  simp only [CollatzResearch.WordTrace]
  refine ⟨106956295943136885385392491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71304197295424590256928327 106956295943136885385392491)
  ·
    refine ⟨160434443914705328078088737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106956295943136885385392491 160434443914705328078088737)
    ·
      refine ⟨120325832936028996058566553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160434443914705328078088737 120325832936028996058566553)
      ·
        refine ⟨90244374702021747043924915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120325832936028996058566553 90244374702021747043924915)
        ·
          refine ⟨135366562053032620565887373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90244374702021747043924915 135366562053032620565887373)
          ·
            refine ⟨50762460769887232712207765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135366562053032620565887373 50762460769887232712207765)
            ·
              refine ⟨2379490348588464033384739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50762460769887232712207765 2379490348588464033384739)
              ·
                refine ⟨3569235522882696050077109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379490348588464033384739 3569235522882696050077109)
                ·
                  refine ⟨334615830270252754694729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3569235522882696050077109 334615830270252754694729)
                  ·
                    rfl

theorem cell22_2932479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 5].length) (baseStart_2932479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932479 prefixEnd_2932479 := by exact prefixLift 2932479
  have htrace : WordTrace (prefixWord ++ tailWord_2932479) baseStart_2932479 baseEnd_2932479 := by
    simpa [prefixWord, tailWord_2932479, baseEnd_2932479] using wordTrace_append hprefix tailTrace_2932479
  have hstable : (prefixWord ++ tailWord_2932479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932479).length < 2 ^ (prefixWord ++ tailWord_2932479).sum := by decide
  have hdescent : baseEnd_2932479 < baseStart_2932479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932590 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_2932590 : Nat := 118140960795 + 2932590 * 2 ^ 59
def prefixEnd_2932590 : Nat := 4983230072969 + 3 ^ 40 * 2932590 * 2
def baseEnd_2932590 : Nat := 1003885488379190974558847

theorem tailTrace_2932590 : CollatzResearch.WordTrace tailWord_2932590 prefixEnd_2932590 1003885488379190974558847 := by
  unfold tailWord_2932590
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370043055716843917835403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71306896297156500895122149 13370043055716843917835403)
  ·
    refine ⟨20055064583575265876753105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13370043055716843917835403 20055064583575265876753105)
    ·
      refine ⟨15041298437681449407564829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20055064583575265876753105 15041298437681449407564829)
      ·
        refine ⟨5640486914130543527836811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15041298437681449407564829 5640486914130543527836811)
        ·
          refine ⟨8460730371195815291755217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640486914130543527836811 8460730371195815291755217)
          ·
            refine ⟨6345547778396861468816413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8460730371195815291755217 6345547778396861468816413)
            ·
              refine ⟨2379580416898823050806155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6345547778396861468816413 2379580416898823050806155)
              ·
                refine ⟨3569370625348234576209233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379580416898823050806155 3569370625348234576209233)
                ·
                  refine ⟨2677027969011175932156925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3569370625348234576209233 2677027969011175932156925)
                  ·
                    refine ⟨1003885488379190974558847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677027969011175932156925 1003885488379190974558847)
                    ·
                      rfl

theorem cell22_2932590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_2932590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932590 prefixEnd_2932590 := by exact prefixLift 2932590
  have htrace : WordTrace (prefixWord ++ tailWord_2932590) baseStart_2932590 baseEnd_2932590 := by
    simpa [prefixWord, tailWord_2932590, baseEnd_2932590] using wordTrace_append hprefix tailTrace_2932590
  have hstable : (prefixWord ++ tailWord_2932590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932590).length < 2 ^ (prefixWord ++ tailWord_2932590).sum := by decide
  have hdescent : baseEnd_2932590 < baseStart_2932590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932627 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 10]
def baseStart_2932627 : Nat := 118140960795 + 2932627 * 2 ^ 59
def prefixEnd_2932627 : Nat := 4983230072969 + 3 ^ 40 * 2932627 * 2
def baseEnd_2932627 : Nat := 1003898154235335211383733

theorem tailTrace_2932627 : CollatzResearch.WordTrace tailWord_2932627 prefixEnd_2932627 1003898154235335211383733 := by
  unfold tailWord_2932627
  simp only [CollatzResearch.WordTrace]
  refine ⟨106961693946600706661780135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71307795964400471107853423 106961693946600706661780135)
  ·
    refine ⟨160442540919901059992670203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106961693946600706661780135 160442540919901059992670203)
    ·
      refine ⟨240663811379851589989005305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160442540919901059992670203 240663811379851589989005305)
      ·
        refine ⟨180497858534888692491753979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240663811379851589989005305 180497858534888692491753979)
        ·
          refine ⟨270746787802333038737630969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180497858534888692491753979 270746787802333038737630969)
          ·
            refine ⟨203060090851749779053223227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270746787802333038737630969 203060090851749779053223227)
            ·
              refine ⟨304590136277624668579834841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203060090851749779053223227 304590136277624668579834841)
              ·
                refine ⟨228442602208218501434876131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304590136277624668579834841 228442602208218501434876131)
                ·
                  refine ⟨342663903312327752152314197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228442602208218501434876131 342663903312327752152314197)
                  ·
                    refine ⟨1003898154235335211383733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 342663903312327752152314197 1003898154235335211383733)
                    ·
                      rfl

theorem cell22_2932627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_2932627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932627 prefixEnd_2932627 := by exact prefixLift 2932627
  have htrace : WordTrace (prefixWord ++ tailWord_2932627) baseStart_2932627 baseEnd_2932627 := by
    simpa [prefixWord, tailWord_2932627, baseEnd_2932627] using wordTrace_append hprefix tailTrace_2932627
  have hstable : (prefixWord ++ tailWord_2932627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932627).length < 2 ^ (prefixWord ++ tailWord_2932627).sum := by decide
  have hdescent : baseEnd_2932627 < baseStart_2932627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932661 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2932661 : Nat := 118140960795 + 2932661 * 2 ^ 59
def prefixEnd_2932661 : Nat := 4983230072969 + 3 ^ 40 * 2932661 * 2
def baseEnd_2932661 : Nat := 1003909793130170456033629

theorem tailTrace_2932661 : CollatzResearch.WordTrace tailWord_2932661 prefixEnd_2932661 1003909793130170456033629 := by
  unfold tailWord_2932661
  simp only [CollatzResearch.WordTrace]
  refine ⟨106962934028477530468517837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71308622685651686979011891 106962934028477530468517837)
  ·
    refine ⟨40111100260679073925694189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106962934028477530468517837 40111100260679073925694189)
    ·
      refine ⟨15041662597754652722135321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40111100260679073925694189 15041662597754652722135321)
      ·
        refine ⟨11281246948315989541601491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15041662597754652722135321 11281246948315989541601491)
        ·
          refine ⟨16921870422473984312402237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11281246948315989541601491 16921870422473984312402237)
          ·
            refine ⟨6345701408427744117150839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16921870422473984312402237 6345701408427744117150839)
            ·
              refine ⟨9518552112641616175726259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345701408427744117150839 9518552112641616175726259)
              ·
                refine ⟨14277828168962424263589389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518552112641616175726259 14277828168962424263589389)
                ·
                  refine ⟨5354185563360909098846021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14277828168962424263589389 5354185563360909098846021)
                  ·
                    refine ⟨1003909793130170456033629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354185563360909098846021 1003909793130170456033629)
                    ·
                      rfl

theorem cell22_2932661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2932661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932661 prefixEnd_2932661 := by exact prefixLift 2932661
  have htrace : WordTrace (prefixWord ++ tailWord_2932661) baseStart_2932661 baseEnd_2932661 := by
    simpa [prefixWord, tailWord_2932661, baseEnd_2932661] using wordTrace_append hprefix tailTrace_2932661
  have hstable : (prefixWord ++ tailWord_2932661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932661).length < 2 ^ (prefixWord ++ tailWord_2932661).sum := by decide
  have hdescent : baseEnd_2932661 < baseStart_2932661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932689 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_2932689 : Nat := 118140960795 + 2932689 * 2 ^ 59
def prefixEnd_2932689 : Nat := 4983230072969 + 3 ^ 40 * 2932689 * 2
def baseEnd_2932689 : Nat := 1003919378102387716333543

theorem tailTrace_2932689 : CollatzResearch.WordTrace tailWord_2932689 prefixEnd_2932689 1003919378102387716333543 := by
  unfold tailWord_2932689
  simp only [CollatzResearch.WordTrace]
  refine ⟨106963955272376091250537121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71309303514917394167024747 106963955272376091250537121)
  ·
    refine ⟨80222966454282068437902841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106963955272376091250537121 80222966454282068437902841)
    ·
      refine ⟨60167224840711551328427131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80222966454282068437902841 60167224840711551328427131)
      ·
        refine ⟨90250837261067326992640697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60167224840711551328427131 90250837261067326992640697)
        ·
          refine ⟨67688127945800495244480523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90250837261067326992640697 67688127945800495244480523)
          ·
            refine ⟨101532191918700742866720785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67688127945800495244480523 101532191918700742866720785)
            ·
              refine ⟨76149143939025557150040589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101532191918700742866720785 76149143939025557150040589)
              ·
                refine ⟨28555928977134583931265221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76149143939025557150040589 28555928977134583931265221)
                ·
                  refine ⟨5354236683212734487112229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28555928977134583931265221 5354236683212734487112229)
                  ·
                    refine ⟨1003919378102387716333543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354236683212734487112229 1003919378102387716333543)
                    ·
                      rfl

theorem cell22_2932689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_2932689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932689 prefixEnd_2932689 := by exact prefixLift 2932689
  have htrace : WordTrace (prefixWord ++ tailWord_2932689) baseStart_2932689 baseEnd_2932689 := by
    simpa [prefixWord, tailWord_2932689, baseEnd_2932689] using wordTrace_append hprefix tailTrace_2932689
  have hstable : (prefixWord ++ tailWord_2932689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932689).length < 2 ^ (prefixWord ++ tailWord_2932689).sum := by decide
  have hdescent : baseEnd_2932689 < baseStart_2932689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932693 : List Nat := [1, 3, 2, 3, 2, 2, 1, 4, 4]
def baseStart_2932693 : Nat := 118140960795 + 2932693 * 2 ^ 59
def prefixEnd_2932693 : Nat := 4983230072969 + 3 ^ 40 * 2932693 * 2
def baseEnd_2932693 : Nat := 334640249128044346411177

theorem tailTrace_2932693 : CollatzResearch.WordTrace tailWord_2932693 prefixEnd_2932693 334640249128044346411177 := by
  unfold tailWord_2932693
  simp only [CollatzResearch.WordTrace]
  refine ⟨106964101164361599933682733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71309400776241066622455155 106964101164361599933682733)
  ·
    refine ⟨40111537936635599975131025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106964101164361599933682733 40111537936635599975131025)
    ·
      refine ⟨30083653452476699981348269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40111537936635599975131025 30083653452476699981348269)
      ·
        refine ⟨11281370044678762493005601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30083653452476699981348269 11281370044678762493005601)
        ·
          refine ⟨8461027533509071869754201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11281370044678762493005601 8461027533509071869754201)
          ·
            refine ⟨6345770650131803902315651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8461027533509071869754201 6345770650131803902315651)
            ·
              refine ⟨9518655975197705853473477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345770650131803902315651 9518655975197705853473477)
              ·
                refine ⟨1784747995349569847526277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9518655975197705853473477 1784747995349569847526277)
                ·
                  refine ⟨334640249128044346411177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784747995349569847526277 334640249128044346411177)
                  ·
                    rfl

theorem cell22_2932693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_2932693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932693 prefixEnd_2932693 := by exact prefixLift 2932693
  have htrace : WordTrace (prefixWord ++ tailWord_2932693) baseStart_2932693 baseEnd_2932693 := by
    simpa [prefixWord, tailWord_2932693, baseEnd_2932693] using wordTrace_append hprefix tailTrace_2932693
  have hstable : (prefixWord ++ tailWord_2932693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932693).length < 2 ^ (prefixWord ++ tailWord_2932693).sum := by decide
  have hdescent : baseEnd_2932693 < baseStart_2932693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932813 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2932813 : Nat := 118140960795 + 2932813 * 2 ^ 59
def prefixEnd_2932813 : Nat := 4983230072969 + 3 ^ 40 * 2932813 * 2
def baseEnd_2932813 : Nat := 1003961825836492726233163

theorem tailTrace_2932813 : CollatzResearch.WordTrace tailWord_2932813 prefixEnd_2932813 1003961825836492726233163 := by
  unfold tailWord_2932813
  simp only [CollatzResearch.WordTrace]
  refine ⟨106968477923926860428051093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71312318615951240285367395 106968477923926860428051093)
  ·
    refine ⟨5014147402684071582564895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106968477923926860428051093 5014147402684071582564895)
    ·
      refine ⟨7521221104026107373847343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5014147402684071582564895 7521221104026107373847343)
      ·
        refine ⟨11281831656039161060771015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7521221104026107373847343 11281831656039161060771015)
        ·
          refine ⟨16922747484058741591156523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11281831656039161060771015 16922747484058741591156523)
          ·
            refine ⟨25384121226088112386734785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16922747484058741591156523 25384121226088112386734785)
            ·
              refine ⟨19038090919566084290051089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25384121226088112386734785 19038090919566084290051089)
              ·
                refine ⟨14278568189674563217538317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19038090919566084290051089 14278568189674563217538317)
                ·
                  refine ⟨5354463071127961206576869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14278568189674563217538317 5354463071127961206576869)
                  ·
                    refine ⟨1003961825836492726233163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354463071127961206576869 1003961825836492726233163)
                    ·
                      rfl

theorem cell22_2932813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2932813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932813 prefixEnd_2932813 := by exact prefixLift 2932813
  have htrace : WordTrace (prefixWord ++ tailWord_2932813) baseStart_2932813 baseEnd_2932813 := by
    simpa [prefixWord, tailWord_2932813, baseEnd_2932813] using wordTrace_append hprefix tailTrace_2932813
  have hstable : (prefixWord ++ tailWord_2932813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932813).length < 2 ^ (prefixWord ++ tailWord_2932813).sum := by decide
  have hdescent : baseEnd_2932813 < baseStart_2932813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932826 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_2932826 : Nat := 118140960795 + 2932826 * 2 ^ 59
def prefixEnd_2932826 : Nat := 4983230072969 + 3 ^ 40 * 2932826 * 2
def baseEnd_2932826 : Nat := 1003966276002165025658123

theorem tailTrace_2932826 : CollatzResearch.WordTrace tailWord_2932826 prefixEnd_2932826 1003966276002165025658123 := by
  unfold tailWord_2932826
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742238018219940912068583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71312634715253175765516221 26742238018219940912068583)
  ·
    refine ⟨40113357027329911368102875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26742238018219940912068583 40113357027329911368102875)
    ·
      refine ⟨60170035540994867052154313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40113357027329911368102875 60170035540994867052154313)
      ·
        refine ⟨45127526655746150289115735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60170035540994867052154313 45127526655746150289115735)
        ·
          refine ⟨67691289983619225433673603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45127526655746150289115735 67691289983619225433673603)
          ·
            refine ⟨101536934975428838150510405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67691289983619225433673603 101536934975428838150510405)
            ·
              refine ⟨19038175307892907153220701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101536934975428838150510405 19038175307892907153220701)
              ·
                refine ⟨7139315740459840182457763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19038175307892907153220701 7139315740459840182457763)
                ·
                  refine ⟨10708973610689760273686645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7139315740459840182457763 10708973610689760273686645)
                  ·
                    refine ⟨1003966276002165025658123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10708973610689760273686645 1003966276002165025658123)
                    ·
                      rfl

theorem cell22_2932826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_2932826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932826 prefixEnd_2932826 := by exact prefixLift 2932826
  have htrace : WordTrace (prefixWord ++ tailWord_2932826) baseStart_2932826 baseEnd_2932826 := by
    simpa [prefixWord, tailWord_2932826, baseEnd_2932826] using wordTrace_append hprefix tailTrace_2932826
  have hstable : (prefixWord ++ tailWord_2932826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932826).length < 2 ^ (prefixWord ++ tailWord_2932826).sum := by decide
  have hdescent : baseEnd_2932826 < baseStart_2932826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932860 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_2932860 : Nat := 118140960795 + 2932860 * 2 ^ 59
def prefixEnd_2932860 : Nat := 4983230072969 + 3 ^ 40 * 2932860 * 2
def baseEnd_2932860 : Nat := 1003977914897000270308019

theorem tailTrace_2932860 : CollatzResearch.WordTrace tailWord_2932860 prefixEnd_2932860 1003977914897000270308019 := by
  unfold tailWord_2932860
  simp only [CollatzResearch.WordTrace]
  refine ⟨53485096077378293727506017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71313461436504391636674689 53485096077378293727506017)
  ·
    refine ⟨40113822058033720295629513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53485096077378293727506017 40113822058033720295629513)
    ·
      refine ⟨30085366543525290221722135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40113822058033720295629513 30085366543525290221722135)
      ·
        refine ⟨45128049815287935332583203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30085366543525290221722135 45128049815287935332583203)
        ·
          refine ⟨67692074722931902998874805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45128049815287935332583203 67692074722931902998874805)
          ·
            refine ⟨6346132005274865906144513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67692074722931902998874805 6346132005274865906144513)
            ·
              refine ⟨4759599003956149429608385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6346132005274865906144513 4759599003956149429608385)
              ·
                refine ⟨3569699252967112072206289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4759599003956149429608385 3569699252967112072206289)
                ·
                  refine ⟨2677274439725334054154717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3569699252967112072206289 2677274439725334054154717)
                  ·
                    refine ⟨1003977914897000270308019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677274439725334054154717 1003977914897000270308019)
                    ·
                      rfl

theorem cell22_2932860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_2932860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932860 prefixEnd_2932860 := by exact prefixLift 2932860
  have htrace : WordTrace (prefixWord ++ tailWord_2932860) baseStart_2932860 baseEnd_2932860 := by
    simpa [prefixWord, tailWord_2932860, baseEnd_2932860] using wordTrace_append hprefix tailTrace_2932860
  have hstable : (prefixWord ++ tailWord_2932860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932860).length < 2 ^ (prefixWord ++ tailWord_2932860).sum := by decide
  have hdescent : baseEnd_2932860 < baseStart_2932860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932890 : List Nat := [3, 1, 1, 5, 2, 1, 3, 6]
def baseStart_2932890 : Nat := 118140960795 + 2932890 * 2 ^ 59
def prefixEnd_2932890 : Nat := 4983230072969 + 3 ^ 40 * 2932890 * 2
def baseEnd_2932890 : Nat := 111554242723343354673103

theorem tailTrace_2932890 : CollatzResearch.WordTrace tailWord_2932890 prefixEnd_2932890 111554242723343354673103 := by
  unfold tailWord_2932890
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742821586161975644651031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71314190896431935052402749 26742821586161975644651031)
  ·
    refine ⟨40114232379242963466976547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26742821586161975644651031 40114232379242963466976547)
    ·
      refine ⟨60171348568864445200464821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40114232379242963466976547 60171348568864445200464821)
      ·
        refine ⟨5641063928331041737543577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60171348568864445200464821 5641063928331041737543577)
        ·
          refine ⟨4230797946248281303157683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5641063928331041737543577 4230797946248281303157683)
          ·
            refine ⟨6346196919372421954736525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230797946248281303157683 6346196919372421954736525)
            ·
              refine ⟨2379823844764658233026197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6346196919372421954736525 2379823844764658233026197)
              ·
                refine ⟨111554242723343354673103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2379823844764658233026197 111554242723343354673103)
                ·
                  rfl

theorem cell22_2932890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_2932890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932890 prefixEnd_2932890 := by exact prefixLift 2932890
  have htrace : WordTrace (prefixWord ++ tailWord_2932890) baseStart_2932890 baseEnd_2932890 := by
    simpa [prefixWord, tailWord_2932890, baseEnd_2932890] using wordTrace_append hprefix tailTrace_2932890
  have hstable : (prefixWord ++ tailWord_2932890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932890).length < 2 ^ (prefixWord ++ tailWord_2932890).sum := by decide
  have hdescent : baseEnd_2932890 < baseStart_2932890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932901 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 7]
def baseStart_2932901 : Nat := 118140960795 + 2932901 * 2 ^ 59
def prefixEnd_2932901 : Nat := 4983230072969 + 3 ^ 40 * 2932901 * 2
def baseEnd_2932901 : Nat := 334663983344963276677631

theorem tailTrace_2932901 : CollatzResearch.WordTrace tailWord_2932901 prefixEnd_2932901 334663983344963276677631 := by
  unfold tailWord_2932901
  simp only [CollatzResearch.WordTrace]
  refine ⟨106971687547608051457254557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71314458365072034304836371 106971687547608051457254557)
  ·
    refine ⟨40114382830353019296470459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106971687547608051457254557 40114382830353019296470459)
    ·
      refine ⟨60171574245529528944705689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40114382830353019296470459 60171574245529528944705689)
      ·
        refine ⟨45128680684147146708529267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60171574245529528944705689 45128680684147146708529267)
        ·
          refine ⟨67693021026220720062793901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45128680684147146708529267 67693021026220720062793901)
          ·
            refine ⟨25384882884832770023547713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67693021026220720062793901 25384882884832770023547713)
            ·
              refine ⟨19038662163624577517660785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25384882884832770023547713 19038662163624577517660785)
              ·
                refine ⟨14278996622718433138245589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19038662163624577517660785 14278996622718433138245589)
                ·
                  refine ⟨334663983344963276677631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14278996622718433138245589 334663983344963276677631)
                  ·
                    rfl

theorem cell22_2932901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_2932901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932901 prefixEnd_2932901 := by exact prefixLift 2932901
  have htrace : WordTrace (prefixWord ++ tailWord_2932901) baseStart_2932901 baseEnd_2932901 := by
    simpa [prefixWord, tailWord_2932901, baseEnd_2932901] using wordTrace_append hprefix tailTrace_2932901
  have hstable : (prefixWord ++ tailWord_2932901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932901).length < 2 ^ (prefixWord ++ tailWord_2932901).sum := by decide
  have hdescent : baseEnd_2932901 < baseStart_2932901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932965 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_2932965 : Nat := 118140960795 + 2932965 * 2 ^ 59
def prefixEnd_2932965 : Nat := 4983230072969 + 3 ^ 40 * 2932965 * 2
def baseEnd_2932965 : Nat := 1004013858542814996432697

theorem tailTrace_2932965 : CollatzResearch.WordTrace tailWord_2932965 prefixEnd_2932965 1004013858542814996432697 := by
  unfold tailWord_2932965
  simp only [CollatzResearch.WordTrace]
  refine ⟨106974021819376190387584349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71316014546250793591722899 106974021819376190387584349)
  ·
    refine ⟨40115258182266071395344131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106974021819376190387584349 40115258182266071395344131)
    ·
      refine ⟨60172887273399107093016197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40115258182266071395344131 60172887273399107093016197)
      ·
        refine ⟨11282416363762332579940537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60172887273399107093016197 11282416363762332579940537)
        ·
          refine ⟨8461812272821749434955403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11282416363762332579940537 8461812272821749434955403)
          ·
            refine ⟨12692718409232624152433105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8461812272821749434955403 12692718409232624152433105)
            ·
              refine ⟨9519538806924468114324829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12692718409232624152433105 9519538806924468114324829)
              ·
                refine ⟨3569827052596675542871811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9519538806924468114324829 3569827052596675542871811)
                ·
                  refine ⟨5354740578895013314307717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569827052596675542871811 5354740578895013314307717)
                  ·
                    refine ⟨1004013858542814996432697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354740578895013314307717 1004013858542814996432697)
                    ·
                      rfl

theorem cell22_2932965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_2932965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932965 prefixEnd_2932965 := by exact prefixLift 2932965
  have htrace : WordTrace (prefixWord ++ tailWord_2932965) baseStart_2932965 baseEnd_2932965 := by
    simpa [prefixWord, tailWord_2932965, baseEnd_2932965] using wordTrace_append hprefix tailTrace_2932965
  have hstable : (prefixWord ++ tailWord_2932965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932965).length < 2 ^ (prefixWord ++ tailWord_2932965).sum := by decide
  have hdescent : baseEnd_2932965 < baseStart_2932965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932993 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2932993 : Nat := 118140960795 + 2932993 * 2 ^ 59
def prefixEnd_2932993 : Nat := 4983230072969 + 3 ^ 40 * 2932993 * 2
def baseEnd_2932993 : Nat := 1004023443515032256732611

theorem tailTrace_2932993 : CollatzResearch.WordTrace tailWord_2932993 prefixEnd_2932993 1004023443515032256732611 := by
  unfold tailWord_2932993
  simp only [CollatzResearch.WordTrace]
  refine ⟨106975043063274751169603633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71316695375516500779735755 106975043063274751169603633)
  ·
    refine ⟨80231282297456063377202725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106975043063274751169603633 80231282297456063377202725)
    ·
      refine ⟨15043365430773011883225511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80231282297456063377202725 15043365430773011883225511)
      ·
        refine ⟨22565048146159517824838267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15043365430773011883225511 22565048146159517824838267)
        ·
          refine ⟨33847572219239276737257401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22565048146159517824838267 33847572219239276737257401)
          ·
            refine ⟨25385679164429457552943051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33847572219239276737257401 25385679164429457552943051)
            ·
              refine ⟨38078518746644186329414577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25385679164429457552943051 38078518746644186329414577)
              ·
                refine ⟨28558889059983139747060933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38078518746644186329414577 28558889059983139747060933)
                ·
                  refine ⟨5354791698746838702573925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28558889059983139747060933 5354791698746838702573925)
                  ·
                    refine ⟨1004023443515032256732611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354791698746838702573925 1004023443515032256732611)
                    ·
                      rfl

theorem cell22_2932993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2932993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932993 prefixEnd_2932993 := by exact prefixLift 2932993
  have htrace : WordTrace (prefixWord ++ tailWord_2932993) baseStart_2932993 baseEnd_2932993 := by
    simpa [prefixWord, tailWord_2932993, baseEnd_2932993] using wordTrace_append hprefix tailTrace_2932993
  have hstable : (prefixWord ++ tailWord_2932993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932993).length < 2 ^ (prefixWord ++ tailWord_2932993).sum := by decide
  have hdescent : baseEnd_2932993 < baseStart_2932993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932995 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 2, 3]
def baseStart_2932995 : Nat := 118140960795 + 2932995 * 2 ^ 59
def prefixEnd_2932995 : Nat := 4983230072969 + 3 ^ 40 * 2932995 * 2
def baseEnd_2932995 : Nat := 1004024128155904918182605

theorem tailTrace_2932995 : CollatzResearch.WordTrace tailWord_2932995 prefixEnd_2932995 1004024128155904918182605 := by
  unfold tailWord_2932995
  simp only [CollatzResearch.WordTrace]
  refine ⟨106975116009267505511176439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71316744006178337007450959 106975116009267505511176439)
  ·
    refine ⟨160462674013901258266764659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106975116009267505511176439 160462674013901258266764659)
    ·
      refine ⟨240694011020851887400146989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160462674013901258266764659 240694011020851887400146989)
      ·
        refine ⟨90260254132819457775055121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240694011020851887400146989 90260254132819457775055121)
        ·
          refine ⟨67695190599614593331291341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90260254132819457775055121 67695190599614593331291341)
          ·
            refine ⟨25385696474855472499234253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67695190599614593331291341 25385696474855472499234253)
            ·
              refine ⟨9519636178070802187212845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25385696474855472499234253 9519636178070802187212845)
              ·
                refine ⟨3569863566776550820204817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9519636178070802187212845 3569863566776550820204817)
                ·
                  refine ⟨2677397675082413115153613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3569863566776550820204817 2677397675082413115153613)
                  ·
                    refine ⟨1004024128155904918182605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677397675082413115153613 1004024128155904918182605)
                    ·
                      rfl

theorem cell22_2932995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 3].length) (baseStart_2932995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932995 prefixEnd_2932995 := by exact prefixLift 2932995
  have htrace : WordTrace (prefixWord ++ tailWord_2932995) baseStart_2932995 baseEnd_2932995 := by
    simpa [prefixWord, tailWord_2932995, baseEnd_2932995] using wordTrace_append hprefix tailTrace_2932995
  have hstable : (prefixWord ++ tailWord_2932995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932995).length < 2 ^ (prefixWord ++ tailWord_2932995).sum := by decide
  have hdescent : baseEnd_2932995 < baseStart_2932995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932999 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 1, 4]
def baseStart_2932999 : Nat := 118140960795 + 2932999 * 2 ^ 59
def prefixEnd_2932999 : Nat := 4983230072969 + 3 ^ 40 * 2932999 * 2
def baseEnd_2932999 : Nat := 1004025497437650241082593

theorem tailTrace_2932999 : CollatzResearch.WordTrace tailWord_2932999 prefixEnd_2932999 1004025497437650241082593 := by
  unfold tailWord_2932999
  simp only [CollatzResearch.WordTrace]
  refine ⟨106975261901253014194322051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71316841267502009462881367 106975261901253014194322051)
  ·
    refine ⟨160462892851879521291483077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106975261901253014194322051 160462892851879521291483077)
    ·
      refine ⟨30086792409727410242153077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160462892851879521291483077 30086792409727410242153077)
      ·
        refine ⟨2820636788411944710201851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30086792409727410242153077 2820636788411944710201851)
        ·
          refine ⟨4230955182617917065302777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820636788411944710201851 4230955182617917065302777)
          ·
            refine ⟨3173216386963437798977083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4230955182617917065302777 3173216386963437798977083)
            ·
              refine ⟨4759824580445156698465625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173216386963437798977083 4759824580445156698465625)
              ·
                refine ⟨3569868435333867523849219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4759824580445156698465625 3569868435333867523849219)
                ·
                  refine ⟨5354802653000801285773829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569868435333867523849219 5354802653000801285773829)
                  ·
                    refine ⟨1004025497437650241082593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354802653000801285773829 1004025497437650241082593)
                    ·
                      rfl

theorem cell22_2932999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_2932999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2932999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2932999 prefixEnd_2932999 := by exact prefixLift 2932999
  have htrace : WordTrace (prefixWord ++ tailWord_2932999) baseStart_2932999 baseEnd_2932999 := by
    simpa [prefixWord, tailWord_2932999, baseEnd_2932999] using wordTrace_append hprefix tailTrace_2932999
  have hstable : (prefixWord ++ tailWord_2932999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932999).length < 2 ^ (prefixWord ++ tailWord_2932999).sum := by decide
  have hdescent : baseEnd_2932999 < baseStart_2932999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933031 : List Nat := [1, 1, 8, 1, 1, 1, 1, 4, 4]
def baseStart_2933031 : Nat := 118140960795 + 2933031 * 2 ^ 59
def prefixEnd_2933031 : Nat := 4983230072969 + 3 ^ 40 * 2933031 * 2
def baseEnd_2933031 : Nat := 334678817230537608094165

theorem tailTrace_2933031 : CollatzResearch.WordTrace tailWord_2933031 prefixEnd_2933031 334678817230537608094165 := by
  unfold tailWord_2933031
  simp only [CollatzResearch.WordTrace]
  refine ⟨106976429037137083659486947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71317619358091389106324631 106976429037137083659486947)
  ·
    refine ⟨160464643555705625489230421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106976429037137083659486947 160464643555705625489230421)
    ·
      refine ⟨1880445041668425298701919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 160464643555705625489230421 1880445041668425298701919)
      ·
        refine ⟨2820667562502637948052879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880445041668425298701919 2820667562502637948052879)
        ·
          refine ⟨4231001343753956922079319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820667562502637948052879 4231001343753956922079319)
          ·
            refine ⟨6346502015630935383118979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231001343753956922079319 6346502015630935383118979)
            ·
              refine ⟨9519753023446403074678469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6346502015630935383118979 9519753023446403074678469)
              ·
                refine ⟨1784953691896200576502213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9519753023446403074678469 1784953691896200576502213)
                ·
                  refine ⟨334678817230537608094165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784953691896200576502213 334678817230537608094165)
                  ·
                    rfl

theorem cell22_2933031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 4].length) (baseStart_2933031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933031 prefixEnd_2933031 := by exact prefixLift 2933031
  have htrace : WordTrace (prefixWord ++ tailWord_2933031) baseStart_2933031 baseEnd_2933031 := by
    simpa [prefixWord, tailWord_2933031, baseEnd_2933031] using wordTrace_append hprefix tailTrace_2933031
  have hstable : (prefixWord ++ tailWord_2933031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933031).length < 2 ^ (prefixWord ++ tailWord_2933031).sum := by decide
  have hdescent : baseEnd_2933031 < baseStart_2933031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933042 : List Nat := [3, 2, 1, 1, 6, 1, 1, 7]
def baseStart_2933042 : Nat := 118140960795 + 2933042 * 2 ^ 59
def prefixEnd_2933042 : Nat := 4983230072969 + 3 ^ 40 * 2933042 * 2
def baseEnd_2933042 : Nat := 111560024135156940250829

theorem tailTrace_2933042 : CollatzResearch.WordTrace tailWord_2933042 prefixEnd_2933042 111560024135156940250829 := by
  unfold tailWord_2933042
  simp only [CollatzResearch.WordTrace]
  refine ⟨26744207560024308134534345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71317886826731488358758253 26744207560024308134534345)
  ·
    refine ⟨20058155670018231100900759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26744207560024308134534345 20058155670018231100900759)
    ·
      refine ⟨30087233505027346651351139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20058155670018231100900759 30087233505027346651351139)
      ·
        refine ⟨45130850257541019977026709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30087233505027346651351139 45130850257541019977026709)
        ·
          refine ⟨2115508605822235311423127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45130850257541019977026709 2115508605822235311423127)
          ·
            refine ⟨3173262908733352967134691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115508605822235311423127 3173262908733352967134691)
            ·
              refine ⟨4759894363100029450702037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173262908733352967134691 4759894363100029450702037)
              ·
                refine ⟨111560024135156940250829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4759894363100029450702037 111560024135156940250829)
                ·
                  rfl

theorem cell22_2933042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_2933042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933042 prefixEnd_2933042 := by exact prefixLift 2933042
  have htrace : WordTrace (prefixWord ++ tailWord_2933042) baseStart_2933042 baseEnd_2933042 := by
    simpa [prefixWord, tailWord_2933042, baseEnd_2933042] using wordTrace_append hprefix tailTrace_2933042
  have hstable : (prefixWord ++ tailWord_2933042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933042).length < 2 ^ (prefixWord ++ tailWord_2933042).sum := by decide
  have hdescent : baseEnd_2933042 < baseStart_2933042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933068 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_2933068 : Nat := 118140960795 + 2933068 * 2 ^ 59
def prefixEnd_2933068 : Nat := 4983230072969 + 3 ^ 40 * 2933068 * 2
def baseEnd_2933068 : Nat := 1004049117547757061107381

theorem tailTrace_2933068 : CollatzResearch.WordTrace tailWord_2933068 prefixEnd_2933068 1004049117547757061107381 := by
  unfold tailWord_2933068
  simp only [CollatzResearch.WordTrace]
  refine ⟨53488889269001519489291929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71318519025335359319055905 53488889269001519489291929)
  ·
    refine ⟨40116666951751139616968947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53488889269001519489291929 40116666951751139616968947)
    ·
      refine ⟨60175000427626709425453421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40116666951751139616968947 60175000427626709425453421)
      ·
        refine ⟨22565625160360016034545033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60175000427626709425453421 22565625160360016034545033)
        ·
          refine ⟨16924218870270012025908775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22565625160360016034545033 16924218870270012025908775)
          ·
            refine ⟨25386328305405018038863163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16924218870270012025908775 25386328305405018038863163)
            ·
              refine ⟨38079492458107527058294745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25386328305405018038863163 38079492458107527058294745)
              ·
                refine ⟨28559619343580645293721059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38079492458107527058294745 28559619343580645293721059)
                ·
                  refine ⟨42839429015370967940581589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28559619343580645293721059 42839429015370967940581589)
                  ·
                    refine ⟨1004049117547757061107381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42839429015370967940581589 1004049117547757061107381)
                    ·
                      rfl

theorem cell22_2933068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_2933068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933068 prefixEnd_2933068 := by exact prefixLift 2933068
  have htrace : WordTrace (prefixWord ++ tailWord_2933068) baseStart_2933068 baseEnd_2933068 := by
    simpa [prefixWord, tailWord_2933068, baseEnd_2933068] using wordTrace_append hprefix tailTrace_2933068
  have hstable : (prefixWord ++ tailWord_2933068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933068).length < 2 ^ (prefixWord ++ tailWord_2933068).sum := by decide
  have hdescent : baseEnd_2933068 < baseStart_2933068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933117 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_2933117 : Nat := 118140960795 + 2933117 * 2 ^ 59
def prefixEnd_2933117 : Nat := 4983230072969 + 3 ^ 40 * 2933117 * 2
def baseEnd_2933117 : Nat := 1004065891249137266632231

theorem tailTrace_2933117 : CollatzResearch.WordTrace tailWord_2933117 prefixEnd_2933117 1004065891249137266632231 := by
  unfold tailWord_2933117
  simp only [CollatzResearch.WordTrace]
  refine ⟨106979565714825520347117605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71319710476550346898078403 106979565714825520347117605)
  ·
    refine ⟨20058668571529785065084551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106979565714825520347117605 20058668571529785065084551)
    ·
      refine ⟨30088002857294677597626827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20058668571529785065084551 30088002857294677597626827)
      ·
        refine ⟨45132004285942016396440241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30088002857294677597626827 45132004285942016396440241)
        ·
          refine ⟨33849003214456512297330181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45132004285942016396440241 33849003214456512297330181)
          ·
            refine ⟨6346688102710596055749409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33849003214456512297330181 6346688102710596055749409)
            ·
              refine ⟨4760016077032947041812057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6346688102710596055749409 4760016077032947041812057)
              ·
                refine ⟨3570012057774710281359043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4760016077032947041812057 3570012057774710281359043)
                ·
                  refine ⟨5355018086662065422038565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570012057774710281359043 5355018086662065422038565)
                  ·
                    refine ⟨1004065891249137266632231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5355018086662065422038565 1004065891249137266632231)
                    ·
                      rfl

theorem cell22_2933117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_2933117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933117 prefixEnd_2933117 := by exact prefixLift 2933117
  have htrace : WordTrace (prefixWord ++ tailWord_2933117) baseStart_2933117 baseEnd_2933117 := by
    simpa [prefixWord, tailWord_2933117, baseEnd_2933117] using wordTrace_append hprefix tailTrace_2933117
  have hstable : (prefixWord ++ tailWord_2933117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933117).length < 2 ^ (prefixWord ++ tailWord_2933117).sum := by decide
  have hdescent : baseEnd_2933117 < baseStart_2933117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933132 : List Nat := [2, 2, 1, 2, 1, 4, 3, 3, 4]
def baseStart_2933132 : Nat := 118140960795 + 2933132 * 2 ^ 59
def prefixEnd_2933132 : Nat := 4983230072969 + 3 ^ 40 * 2933132 * 2
def baseEnd_2933132 : Nat := 334690342018560742502395

theorem tailTrace_2933132 : CollatzResearch.WordTrace tailWord_2933132 prefixEnd_2933132 334690342018560742502395 := by
  unfold tailWord_2933132
  simp only [CollatzResearch.WordTrace]
  refine ⟨53490056404885588954456825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71320075206514118605942433 53490056404885588954456825)
  ·
    refine ⟨40117542303664191715842619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53490056404885588954456825 40117542303664191715842619)
    ·
      refine ⟨60176313455496287573763929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40117542303664191715842619 60176313455496287573763929)
      ·
        refine ⟨45132235091622215680322947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60176313455496287573763929 45132235091622215680322947)
        ·
          refine ⟨67698352637433323520484421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45132235091622215680322947 67698352637433323520484421)
          ·
            refine ⟨12693441119518748160090829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67698352637433323520484421 12693441119518748160090829)
            ·
              refine ⟨4760040419819530560034061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12693441119518748160090829 4760040419819530560034061)
              ·
                refine ⟨1785015157432323960012773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4760040419819530560034061 1785015157432323960012773)
                ·
                  refine ⟨334690342018560742502395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785015157432323960012773 334690342018560742502395)
                  ·
                    rfl

theorem cell22_2933132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_2933132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933132 prefixEnd_2933132 := by exact prefixLift 2933132
  have htrace : WordTrace (prefixWord ++ tailWord_2933132) baseStart_2933132 baseEnd_2933132 := by
    simpa [prefixWord, tailWord_2933132, baseEnd_2933132] using wordTrace_append hprefix tailTrace_2933132
  have hstable : (prefixWord ++ tailWord_2933132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933132).length < 2 ^ (prefixWord ++ tailWord_2933132).sum := by decide
  have hdescent : baseEnd_2933132 < baseStart_2933132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933142 : List Nat := [5, 3, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2933142 : Nat := 118140960795 + 2933142 * 2 ^ 59
def prefixEnd_2933142 : Nat := 4983230072969 + 3 ^ 40 * 2933142 * 2
def baseEnd_2933142 : Nat := 1004074449260045534757155

theorem tailTrace_2933142 : CollatzResearch.WordTrace tailWord_2933142 prefixEnd_2933142 1004074449260045534757155 := by
  unfold tailWord_2933142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6686279846233434351048605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71320318359823299744518453 6686279846233434351048605)
  ·
    refine ⟨2507354942337537881643227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6686279846233434351048605 2507354942337537881643227)
    ·
      refine ⟨3761032413506306822464841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507354942337537881643227 3761032413506306822464841)
      ·
        refine ⟨2820774310129730116848631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3761032413506306822464841 2820774310129730116848631)
        ·
          refine ⟨4231161465194595175272947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820774310129730116848631 4231161465194595175272947)
          ·
            refine ⟨6346742197791892762909421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231161465194595175272947 6346742197791892762909421)
            ·
              refine ⟨2380028324171959786091033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6346742197791892762909421 2380028324171959786091033)
              ·
                refine ⟨1785021243128969839568275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2380028324171959786091033 1785021243128969839568275)
                ·
                  refine ⟨2677531864693454759352413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785021243128969839568275 2677531864693454759352413)
                  ·
                    refine ⟨1004074449260045534757155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677531864693454759352413 1004074449260045534757155)
                    ·
                      rfl

theorem cell22_2933142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2933142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933142 prefixEnd_2933142 := by exact prefixLift 2933142
  have htrace : WordTrace (prefixWord ++ tailWord_2933142) baseStart_2933142 baseEnd_2933142 := by
    simpa [prefixWord, tailWord_2933142, baseEnd_2933142] using wordTrace_append hprefix tailTrace_2933142
  have hstable : (prefixWord ++ tailWord_2933142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933142).length < 2 ^ (prefixWord ++ tailWord_2933142).sum := by decide
  have hdescent : baseEnd_2933142 < baseStart_2933142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933143 : List Nat := [1, 1, 3, 3, 1, 1, 12]
def baseStart_2933143 : Nat := 118140960795 + 2933143 * 2 ^ 59
def prefixEnd_2933143 : Nat := 4983230072969 + 3 ^ 40 * 2933143 * 2
def baseEnd_2933143 : Nat := 37187955243721550573413

theorem tailTrace_2933143 : CollatzResearch.WordTrace tailWord_2933143 prefixEnd_2933143 37187955243721550573413 := by
  unfold tailWord_2933143
  simp only [CollatzResearch.WordTrace]
  refine ⟨106980514012731326787564083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71320342675154217858376055 106980514012731326787564083)
  ·
    refine ⟨160470771019096990181346125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106980514012731326787564083 160470771019096990181346125)
    ·
      refine ⟨60176539132161371318004797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160470771019096990181346125 60176539132161371318004797)
      ·
        refine ⟨22566202174560514244251799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60176539132161371318004797 22566202174560514244251799)
        ·
          refine ⟨33849303261840771366377699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22566202174560514244251799 33849303261840771366377699)
          ·
            refine ⟨50773954892761157049566549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33849303261840771366377699 50773954892761157049566549)
            ·
              refine ⟨37187955243721550573413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 50773954892761157049566549 37187955243721550573413)
              ·
                rfl

theorem cell22_2933143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 12].length) (baseStart_2933143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933143 prefixEnd_2933143 := by exact prefixLift 2933143
  have htrace : WordTrace (prefixWord ++ tailWord_2933143) baseStart_2933143 baseEnd_2933143 := by
    simpa [prefixWord, tailWord_2933143, baseEnd_2933143] using wordTrace_append hprefix tailTrace_2933143
  have hstable : (prefixWord ++ tailWord_2933143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933143).length < 2 ^ (prefixWord ++ tailWord_2933143).sum := by decide
  have hdescent : baseEnd_2933143 < baseStart_2933143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933145 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_2933145 : Nat := 118140960795 + 2933145 * 2 ^ 59
def prefixEnd_2933145 : Nat := 4983230072969 + 3 ^ 40 * 2933145 * 2
def baseEnd_2933145 : Nat := 1004075476221354526932145

theorem tailTrace_2933145 : CollatzResearch.WordTrace tailWord_2933145 prefixEnd_2933145 1004075476221354526932145 := by
  unfold tailWord_2933145
  simp only [CollatzResearch.WordTrace]
  refine ⟨106980586958724081129136889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71320391305816054086091259 106980586958724081129136889)
  ·
    refine ⟨80235440219043060846852667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106980586958724081129136889 80235440219043060846852667)
    ·
      refine ⟨120353160328564591270279001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80235440219043060846852667 120353160328564591270279001)
      ·
        refine ⟨90264870246423443452709251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120353160328564591270279001 90264870246423443452709251)
        ·
          refine ⟨135397305369635165179063877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90264870246423443452709251 135397305369635165179063877)
          ·
            refine ⟨25386994756806593471074477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135397305369635165179063877 25386994756806593471074477)
            ·
              refine ⟨9520123033802472551652929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25386994756806593471074477 9520123033802472551652929)
              ·
                refine ⟨7140092275351854413739697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9520123033802472551652929 7140092275351854413739697)
                ·
                  refine ⟨5355069206513890810304773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7140092275351854413739697 5355069206513890810304773)
                  ·
                    refine ⟨1004075476221354526932145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5355069206513890810304773 1004075476221354526932145)
                    ·
                      rfl

theorem cell22_2933145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_2933145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933145 prefixEnd_2933145 := by exact prefixLift 2933145
  have htrace : WordTrace (prefixWord ++ tailWord_2933145) baseStart_2933145 baseEnd_2933145 := by
    simpa [prefixWord, tailWord_2933145, baseEnd_2933145] using wordTrace_append hprefix tailTrace_2933145
  have hstable : (prefixWord ++ tailWord_2933145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933145).length < 2 ^ (prefixWord ++ tailWord_2933145).sum := by decide
  have hdescent : baseEnd_2933145 < baseStart_2933145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933149 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 6]
def baseStart_2933149 : Nat := 118140960795 + 2933149 * 2 ^ 59
def prefixEnd_2933149 : Nat := 4983230072969 + 3 ^ 40 * 2933149 * 2
def baseEnd_2933149 : Nat := 334692281834366616610711

theorem tailTrace_2933149 : CollatzResearch.WordTrace tailWord_2933149 prefixEnd_2933149 334692281834366616610711 := by
  unfold tailWord_2933149
  simp only [CollatzResearch.WordTrace]
  refine ⟨106980732850709589812282501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71320488567139726541521667 106980732850709589812282501)
  ·
    refine ⟨20058887409508048089802969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106980732850709589812282501 20058887409508048089802969)
    ·
      refine ⟨15044165557131036067352227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20058887409508048089802969 15044165557131036067352227)
      ·
        refine ⟨22566248335696554101028341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15044165557131036067352227 22566248335696554101028341)
        ·
          refine ⟨2115585781471551946971407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22566248335696554101028341 2115585781471551946971407)
          ·
            refine ⟨3173378672207327920457111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115585781471551946971407 3173378672207327920457111)
            ·
              refine ⟨4760068008310991880685667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173378672207327920457111 4760068008310991880685667)
              ·
                refine ⟨7140102012466487821028501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760068008310991880685667 7140102012466487821028501)
                ·
                  refine ⟨334692281834366616610711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7140102012466487821028501 334692281834366616610711)
                  ·
                    rfl

theorem cell22_2933149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_2933149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933149 prefixEnd_2933149 := by exact prefixLift 2933149
  have htrace : WordTrace (prefixWord ++ tailWord_2933149) baseStart_2933149 baseEnd_2933149 := by
    simpa [prefixWord, tailWord_2933149, baseEnd_2933149] using wordTrace_append hprefix tailTrace_2933149
  have hstable : (prefixWord ++ tailWord_2933149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933149).length < 2 ^ (prefixWord ++ tailWord_2933149).sum := by decide
  have hdescent : baseEnd_2933149 < baseStart_2933149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933209 : List Nat := [1, 2, 1, 2, 4, 1, 3, 4, 1, 3]
def baseStart_2933209 : Nat := 118140960795 + 2933209 * 2 ^ 59
def prefixEnd_2933209 : Nat := 4983230072969 + 3 ^ 40 * 2933209 * 2
def baseEnd_2933209 : Nat := 1004097384729279693331949

theorem tailTrace_2933209 : CollatzResearch.WordTrace tailWord_2933209 prefixEnd_2933209 1004097384729279693331949 := by
  unfold tailWord_2933209
  simp only [CollatzResearch.WordTrace]
  refine ⟨106982921230492220059466681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71321947486994813372977787 106982921230492220059466681)
  ·
    refine ⟨80237190922869165044600011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106982921230492220059466681 80237190922869165044600011)
    ·
      refine ⟨120355786384303747566900017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80237190922869165044600011 120355786384303747566900017)
      ·
        refine ⟨90266839788227810675175013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120355786384303747566900017 90266839788227810675175013)
        ·
          refine ⟨16925032460292714501595315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90266839788227810675175013 16925032460292714501595315)
          ·
            refine ⟨25387548690439071752392973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16925032460292714501595315 25387548690439071752392973)
            ·
              refine ⟨9520330758914651907147365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25387548690439071752392973 9520330758914651907147365)
              ·
                refine ⟨1785062017296497232590131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9520330758914651907147365 1785062017296497232590131)
                ·
                  refine ⟨2677593025944745848885197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785062017296497232590131 2677593025944745848885197)
                  ·
                    refine ⟨1004097384729279693331949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677593025944745848885197 1004097384729279693331949)
                    ·
                      rfl

theorem cell22_2933209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 3].length) (baseStart_2933209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933209 prefixEnd_2933209 := by exact prefixLift 2933209
  have htrace : WordTrace (prefixWord ++ tailWord_2933209) baseStart_2933209 baseEnd_2933209 := by
    simpa [prefixWord, tailWord_2933209, baseEnd_2933209] using wordTrace_append hprefix tailTrace_2933209
  have hstable : (prefixWord ++ tailWord_2933209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933209).length < 2 ^ (prefixWord ++ tailWord_2933209).sum := by decide
  have hdescent : baseEnd_2933209 < baseStart_2933209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933235 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 4]
def baseStart_2933235 : Nat := 118140960795 + 2933235 * 2 ^ 59
def prefixEnd_2933235 : Nat := 4983230072969 + 3 ^ 40 * 2933235 * 2
def baseEnd_2933235 : Nat := 1004106285060624292181869

theorem tailTrace_2933235 : CollatzResearch.WordTrace tailWord_2933235 prefixEnd_2933235 1004106285060624292181869 := by
  unfold tailWord_2933235
  simp only [CollatzResearch.WordTrace]
  refine ⟨106983869528398026499913159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71322579685598684333275439 106983869528398026499913159)
  ·
    refine ⟨160475804292597039749869739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106983869528398026499913159 160475804292597039749869739)
    ·
      refine ⟨240713706438895559624804609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160475804292597039749869739 240713706438895559624804609)
      ·
        refine ⟨180535279829171669718603457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240713706438895559624804609 180535279829171669718603457)
        ·
          refine ⟨135401459871878752288952593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180535279829171669718603457 135401459871878752288952593)
          ·
            refine ⟨101551094903909064216714445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135401459871878752288952593 101551094903909064216714445)
            ·
              refine ⟨38081660588965899081267917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101551094903909064216714445 38081660588965899081267917)
              ·
                refine ⟨14280622720862212155475469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38081660588965899081267917 14280622720862212155475469)
                ·
                  refine ⟨5355233520323329558303301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14280622720862212155475469 5355233520323329558303301)
                  ·
                    refine ⟨1004106285060624292181869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5355233520323329558303301 1004106285060624292181869)
                    ·
                      rfl

theorem cell22_2933235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4].length) (baseStart_2933235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933235 prefixEnd_2933235 := by exact prefixLift 2933235
  have htrace : WordTrace (prefixWord ++ tailWord_2933235) baseStart_2933235 baseEnd_2933235 := by
    simpa [prefixWord, tailWord_2933235, baseEnd_2933235] using wordTrace_append hprefix tailTrace_2933235
  have hstable : (prefixWord ++ tailWord_2933235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933235).length < 2 ^ (prefixWord ++ tailWord_2933235).sum := by decide
  have hdescent : baseEnd_2933235 < baseStart_2933235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933267 : List Nat := [1, 1, 1, 2, 1, 5, 1, 6, 4]
def baseStart_2933267 : Nat := 118140960795 + 2933267 * 2 ^ 59
def prefixEnd_2933267 : Nat := 4983230072969 + 3 ^ 40 * 2933267 * 2
def baseEnd_2933267 : Nat := 334705746438195625127257

theorem tailTrace_2933267 : CollatzResearch.WordTrace tailWord_2933267 prefixEnd_2933267 334705746438195625127257 := by
  unfold tailWord_2933267
  simp only [CollatzResearch.WordTrace]
  refine ⟨106985036664282095965078055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71323357776188063976718703 106985036664282095965078055)
  ·
    refine ⟨160477554996423143947617083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106985036664282095965078055 160477554996423143947617083)
    ·
      refine ⟨240716332494634715921425625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160477554996423143947617083 240716332494634715921425625)
      ·
        refine ⟨180537249370976036941069219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240716332494634715921425625 180537249370976036941069219)
        ·
          refine ⟨270805874056464055411603829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180537249370976036941069219 270805874056464055411603829)
          ·
            refine ⟨25388050692793505194837859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270805874056464055411603829 25388050692793505194837859)
            ·
              refine ⟨38082076039190257792256789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25388050692793505194837859 38082076039190257792256789)
              ·
                refine ⟨1785097314337043334012037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38082076039190257792256789 1785097314337043334012037)
                ·
                  refine ⟨334705746438195625127257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785097314337043334012037 334705746438195625127257)
                  ·
                    rfl

theorem cell22_2933267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 4].length) (baseStart_2933267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933267 prefixEnd_2933267 := by exact prefixLift 2933267
  have htrace : WordTrace (prefixWord ++ tailWord_2933267) baseStart_2933267 baseEnd_2933267 := by
    simpa [prefixWord, tailWord_2933267, baseEnd_2933267] using wordTrace_append hprefix tailTrace_2933267
  have hstable : (prefixWord ++ tailWord_2933267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933267).length < 2 ^ (prefixWord ++ tailWord_2933267).sum := by decide
  have hdescent : baseEnd_2933267 < baseStart_2933267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933355 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 3, 7]
def baseStart_2933355 : Nat := 118140960795 + 2933355 * 2 ^ 59
def prefixEnd_2933355 : Nat := 4983230072969 + 3 ^ 40 * 2933355 * 2
def baseEnd_2933355 : Nat := 1004147363512983979181501

theorem tailTrace_2933355 : CollatzResearch.WordTrace tailWord_2933355 prefixEnd_2933355 1004147363512983979181501 := by
  unfold tailWord_2933355
  simp only [CollatzResearch.WordTrace]
  refine ⟨106988246287963286994281519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71325497525308857996187679 106988246287963286994281519)
  ·
    refine ⟨160482369431944930491422279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106988246287963286994281519 160482369431944930491422279)
    ·
      refine ⟨240723554147917395737133419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160482369431944930491422279 240723554147917395737133419)
      ·
        refine ⟨361085331221876093605700129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240723554147917395737133419 361085331221876093605700129)
        ·
          refine ⟨270813998416407070204275097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361085331221876093605700129 270813998416407070204275097)
          ·
            refine ⟨203110498812305302653206323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270813998416407070204275097 203110498812305302653206323)
            ·
              refine ⟨304665748218457953979809485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203110498812305302653206323 304665748218457953979809485)
              ·
                refine ⟨114249655581921732742428557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304665748218457953979809485 114249655581921732742428557)
                ·
                  refine ⟨42843620843220649778410709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114249655581921732742428557 42843620843220649778410709)
                  ·
                    refine ⟨1004147363512983979181501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42843620843220649778410709 1004147363512983979181501)
                    ·
                      rfl

theorem cell22_2933355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_2933355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933355 prefixEnd_2933355 := by exact prefixLift 2933355
  have htrace : WordTrace (prefixWord ++ tailWord_2933355) baseStart_2933355 baseEnd_2933355 := by
    simpa [prefixWord, tailWord_2933355, baseEnd_2933355] using wordTrace_append hprefix tailTrace_2933355
  have hstable : (prefixWord ++ tailWord_2933355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933355).length < 2 ^ (prefixWord ++ tailWord_2933355).sum := by decide
  have hdescent : baseEnd_2933355 < baseStart_2933355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933404 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_2933404 : Nat := 118140960795 + 2933404 * 2 ^ 59
def prefixEnd_2933404 : Nat := 4983230072969 + 3 ^ 40 * 2933404 * 2
def baseEnd_2933404 : Nat := 1004164137214364184706351

theorem tailTrace_2933404 : CollatzResearch.WordTrace tailWord_2933404 prefixEnd_2933404 1004164137214364184706351 := by
  unfold tailWord_2933404
  simp only [CollatzResearch.WordTrace]
  refine ⟨53495016732392884181407633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71326688976523845575210177 53495016732392884181407633)
  ·
    refine ⟨40121262549294663136055725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53495016732392884181407633 40121262549294663136055725)
    ·
      refine ⟨15045473455985498676020897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40121262549294663136055725 15045473455985498676020897)
      ·
        refine ⟨11284105091989124007015673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15045473455985498676020897 11284105091989124007015673)
        ·
          refine ⟨8463078818991843005261755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11284105091989124007015673 8463078818991843005261755)
          ·
            refine ⟨12694618228487764507892633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463078818991843005261755 12694618228487764507892633)
            ·
              refine ⟨9520963671365823380919475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12694618228487764507892633 9520963671365823380919475)
              ·
                refine ⟨14281445507048735071379213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9520963671365823380919475 14281445507048735071379213)
                ·
                  refine ⟨5355542065143275651767205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14281445507048735071379213 5355542065143275651767205)
                  ·
                    refine ⟨1004164137214364184706351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5355542065143275651767205 1004164137214364184706351)
                    ·
                      rfl

theorem cell22_2933404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_2933404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933404 prefixEnd_2933404 := by exact prefixLift 2933404
  have htrace : WordTrace (prefixWord ++ tailWord_2933404) baseStart_2933404 baseEnd_2933404 := by
    simpa [prefixWord, tailWord_2933404, baseEnd_2933404] using wordTrace_append hprefix tailTrace_2933404
  have hstable : (prefixWord ++ tailWord_2933404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933404).length < 2 ^ (prefixWord ++ tailWord_2933404).sum := by decide
  have hdescent : baseEnd_2933404 < baseStart_2933404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933421 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2933421 : Nat := 118140960795 + 2933421 * 2 ^ 59
def prefixEnd_2933421 : Nat := 4983230072969 + 3 ^ 40 * 2933421 * 2
def baseEnd_2933421 : Nat := 1004169956661781807031299

theorem tailTrace_2933421 : CollatzResearch.WordTrace tailWord_2933421 prefixEnd_2933421 1004169956661781807031299 := by
  unfold tailWord_2933421
  simp only [CollatzResearch.WordTrace]
  refine ⟨106990653505724180266184117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71327102337149453510789411 106990653505724180266184117)
  ·
    refine ⟨10030373766161641899954761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106990653505724180266184117 10030373766161641899954761)
    ·
      refine ⟨7522780324621231424966071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10030373766161641899954761 7522780324621231424966071)
      ·
        refine ⟨11284170486931847137449107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7522780324621231424966071 11284170486931847137449107)
        ·
          refine ⟨16926255730397770706173661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11284170486931847137449107 16926255730397770706173661)
          ·
            refine ⟨6347345898899164014815123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16926255730397770706173661 6347345898899164014815123)
            ·
              refine ⟨9521018848348746022222685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347345898899164014815123 9521018848348746022222685)
              ·
                refine ⟨3570382068130779758333507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9521018848348746022222685 3570382068130779758333507)
                ·
                  refine ⟨5355573102196169637500261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570382068130779758333507 5355573102196169637500261)
                  ·
                    refine ⟨1004169956661781807031299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5355573102196169637500261 1004169956661781807031299)
                    ·
                      rfl

theorem cell22_2933421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2933421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933421 prefixEnd_2933421 := by exact prefixLift 2933421
  have htrace : WordTrace (prefixWord ++ tailWord_2933421) baseStart_2933421 baseEnd_2933421 := by
    simpa [prefixWord, tailWord_2933421, baseEnd_2933421] using wordTrace_append hprefix tailTrace_2933421
  have hstable : (prefixWord ++ tailWord_2933421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933421).length < 2 ^ (prefixWord ++ tailWord_2933421).sum := by decide
  have hdescent : baseEnd_2933421 < baseStart_2933421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933434 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_2933434 : Nat := 118140960795 + 2933434 * 2 ^ 59
def prefixEnd_2933434 : Nat := 4983230072969 + 3 ^ 40 * 2933434 * 2
def baseEnd_2933434 : Nat := 1004174406827454106456259

theorem tailTrace_2933434 : CollatzResearch.WordTrace tailWord_2933434 prefixEnd_2933434 1004174406827454106456259 := by
  unfold tailWord_2933434
  simp only [CollatzResearch.WordTrace]
  refine ⟨26747781913669270871601839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71327418436451388990938237 26747781913669270871601839)
  ·
    refine ⟨40121672870503906307402759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26747781913669270871601839 40121672870503906307402759)
    ·
      refine ⟨60182509305755859461104139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40121672870503906307402759 60182509305755859461104139)
      ·
        refine ⟨90273763958633789191656209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60182509305755859461104139 90273763958633789191656209)
        ·
          refine ⟨67705322968975341893742157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90273763958633789191656209 67705322968975341893742157)
          ·
            refine ⟨25389496113365753210153309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67705322968975341893742157 25389496113365753210153309)
            ·
              refine ⟨9521061042512157453807491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25389496113365753210153309 9521061042512157453807491)
              ·
                refine ⟨14281591563768236180711237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9521061042512157453807491 14281591563768236180711237)
                ·
                  refine ⟨2677798418206544283883357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14281591563768236180711237 2677798418206544283883357)
                  ·
                    refine ⟨1004174406827454106456259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677798418206544283883357 1004174406827454106456259)
                    ·
                      rfl

theorem cell22_2933434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_2933434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933434 prefixEnd_2933434 := by exact prefixLift 2933434
  have htrace : WordTrace (prefixWord ++ tailWord_2933434) baseStart_2933434 baseEnd_2933434 := by
    simpa [prefixWord, tailWord_2933434, baseEnd_2933434] using wordTrace_append hprefix tailTrace_2933434
  have hstable : (prefixWord ++ tailWord_2933434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933434).length < 2 ^ (prefixWord ++ tailWord_2933434).sum := by decide
  have hdescent : baseEnd_2933434 < baseStart_2933434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933464 : List Nat := [2, 1, 2, 2, 3, 2, 4, 6]
def baseStart_2933464 : Nat := 118140960795 + 2933464 * 2 ^ 59
def prefixEnd_2933464 : Nat := 4983230072969 + 3 ^ 40 * 2933464 * 2
def baseEnd_2933464 : Nat := 111576075160060447578463

theorem tailTrace_2933464 : CollatzResearch.WordTrace tailWord_2933464 prefixEnd_2933464 111576075160060447578463 := by
  unfold tailWord_2933464
  simp only [CollatzResearch.WordTrace]
  refine ⟨53496110922284199304999723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71328147896378932406666297 53496110922284199304999723)
  ·
    refine ⟨80244166383426298957499585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53496110922284199304999723 80244166383426298957499585)
    ·
      refine ⟨60183124787569724218124689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80244166383426298957499585 60183124787569724218124689)
      ·
        refine ⟨45137343590677293163593517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60183124787569724218124689 45137343590677293163593517)
        ·
          refine ⟨16926503846503984936347569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45137343590677293163593517 16926503846503984936347569)
          ·
            refine ⟨12694877884877988702260677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16926503846503984936347569 12694877884877988702260677)
            ·
              refine ⟨2380289603414622881673877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12694877884877988702260677 2380289603414622881673877)
              ·
                refine ⟨111576075160060447578463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2380289603414622881673877 111576075160060447578463)
                ·
                  rfl

theorem cell22_2933464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 6].length) (baseStart_2933464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933464 prefixEnd_2933464 := by exact prefixLift 2933464
  have htrace : WordTrace (prefixWord ++ tailWord_2933464) baseStart_2933464 baseEnd_2933464 := by
    simpa [prefixWord, tailWord_2933464, baseEnd_2933464] using wordTrace_append hprefix tailTrace_2933464
  have hstable : (prefixWord ++ tailWord_2933464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933464).length < 2 ^ (prefixWord ++ tailWord_2933464).sum := by decide
  have hdescent : baseEnd_2933464 < baseStart_2933464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933494 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2933494 : Nat := 118140960795 + 2933494 * 2 ^ 59
def prefixEnd_2933494 : Nat := 4983230072969 + 3 ^ 40 * 2933494 * 2
def baseEnd_2933494 : Nat := 1004194946053633949956075

theorem tailTrace_2933494 : CollatzResearch.WordTrace tailWord_2933494 prefixEnd_2933494 1004194946053633949956075 := by
  unfold tailWord_2933494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687082252153732108349471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71328877356306475822394357 6687082252153732108349471)
  ·
    refine ⟨10030623378230598162524207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6687082252153732108349471 10030623378230598162524207)
    ·
      refine ⟨15045935067345897243786311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10030623378230598162524207 15045935067345897243786311)
      ·
        refine ⟨22568902601018845865679467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15045935067345897243786311 22568902601018845865679467)
        ·
          refine ⟨33853353901528268798519201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22568902601018845865679467 33853353901528268798519201)
          ·
            refine ⟨25390015426146201598889401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33853353901528268798519201 25390015426146201598889401)
            ·
              refine ⟨19042511569609651199167051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25390015426146201598889401 19042511569609651199167051)
              ·
                refine ⟨28563767354414476798750577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19042511569609651199167051 28563767354414476798750577)
                ·
                  refine ⟨21422825515810857599062933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28563767354414476798750577 21422825515810857599062933)
                  ·
                    refine ⟨1004194946053633949956075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21422825515810857599062933 1004194946053633949956075)
                    ·
                      rfl

theorem cell22_2933494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2933494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933494 prefixEnd_2933494 := by exact prefixLift 2933494
  have htrace : WordTrace (prefixWord ++ tailWord_2933494) baseStart_2933494 baseEnd_2933494 := by
    simpa [prefixWord, tailWord_2933494, baseEnd_2933494] using wordTrace_append hprefix tailTrace_2933494
  have hstable : (prefixWord ++ tailWord_2933494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933494).length < 2 ^ (prefixWord ++ tailWord_2933494).sum := by decide
  have hdescent : baseEnd_2933494 < baseStart_2933494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933507 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 1, 7]
def baseStart_2933507 : Nat := 118140960795 + 2933507 * 2 ^ 59
def prefixEnd_2933507 : Nat := 4983230072969 + 3 ^ 40 * 2933507 * 2
def baseEnd_2933507 : Nat := 1004199396219306249381035

theorem tailTrace_2933507 : CollatzResearch.WordTrace tailWord_2933507 prefixEnd_2933507 1004199396219306249381035 := by
  unfold tailWord_2933507
  simp only [CollatzResearch.WordTrace]
  refine ⟨106993790183412616953814775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71329193455608411302543183 106993790183412616953814775)
  ·
    refine ⟨160490685275118925430722163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106993790183412616953814775 160490685275118925430722163)
    ·
      refine ⟨240736027912678388146083245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160490685275118925430722163 240736027912678388146083245)
      ·
        refine ⟨90276010467254395554781217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240736027912678388146083245 90276010467254395554781217)
        ·
          refine ⟨67707007850440796666085913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90276010467254395554781217 67707007850440796666085913)
          ·
            refine ⟨50780255887830597499564435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67707007850440796666085913 50780255887830597499564435)
            ·
              refine ⟨76170383831745896249346653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50780255887830597499564435 76170383831745896249346653)
              ·
                refine ⟨28563893936904711093504995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76170383831745896249346653 28563893936904711093504995)
                ·
                  refine ⟨42845840905357066640257493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28563893936904711093504995 42845840905357066640257493)
                  ·
                    refine ⟨1004199396219306249381035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42845840905357066640257493 1004199396219306249381035)
                    ·
                      rfl

theorem cell22_2933507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_2933507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933507 prefixEnd_2933507 := by exact prefixLift 2933507
  have htrace : WordTrace (prefixWord ++ tailWord_2933507) baseStart_2933507 baseEnd_2933507 := by
    simpa [prefixWord, tailWord_2933507, baseEnd_2933507] using wordTrace_append hprefix tailTrace_2933507
  have hstable : (prefixWord ++ tailWord_2933507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933507).length < 2 ^ (prefixWord ++ tailWord_2933507).sum := by decide
  have hdescent : baseEnd_2933507 < baseStart_2933507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933554 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_2933554 : Nat := 118140960795 + 2933554 * 2 ^ 59
def prefixEnd_2933554 : Nat := 4983230072969 + 3 ^ 40 * 2933554 * 2
def baseEnd_2933554 : Nat := 334738495093271264485297

theorem tailTrace_2933554 : CollatzResearch.WordTrace tailWord_2933554 prefixEnd_2933554 334738495093271264485297 := by
  unfold tailWord_2933554
  simp only [CollatzResearch.WordTrace]
  refine ⟨26748876103560585995193929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71330336276161562653850477 26748876103560585995193929)
  ·
    refine ⟨20061657077670439496395447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26748876103560585995193929 20061657077670439496395447)
    ·
      refine ⟨30092485616505659244593171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20061657077670439496395447 30092485616505659244593171)
      ·
        refine ⟨45138728424758488866889757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30092485616505659244593171 45138728424758488866889757)
        ·
          refine ⟨16927023159284433325083659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45138728424758488866889757 16927023159284433325083659)
          ·
            refine ⟨25390534738926649987625489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16927023159284433325083659 25390534738926649987625489)
            ·
              refine ⟨19042901054194987490719117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25390534738926649987625489 19042901054194987490719117)
              ·
                refine ⟨7141087895323120309019669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19042901054194987490719117 7141087895323120309019669)
                ·
                  refine ⟨334738495093271264485297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7141087895323120309019669 334738495093271264485297)
                  ·
                    rfl

theorem cell22_2933554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_2933554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933554 prefixEnd_2933554 := by exact prefixLift 2933554
  have htrace : WordTrace (prefixWord ++ tailWord_2933554) baseStart_2933554 baseEnd_2933554 := by
    simpa [prefixWord, tailWord_2933554, baseEnd_2933554] using wordTrace_append hprefix tailTrace_2933554
  have hstable : (prefixWord ++ tailWord_2933554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933554).length < 2 ^ (prefixWord ++ tailWord_2933554).sum := by decide
  have hdescent : baseEnd_2933554 < baseStart_2933554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933558 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2933558 : Nat := 118140960795 + 2933558 * 2 ^ 59
def prefixEnd_2933558 : Nat := 4983230072969 + 3 ^ 40 * 2933558 * 2
def baseEnd_2933558 : Nat := 1004216854561559116355879

theorem tailTrace_2933558 : CollatzResearch.WordTrace tailWord_2933558 prefixEnd_2933558 1004216854561559116355879 := by
  unfold tailWord_2933558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687228144139240791495083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71330433537485235109280885 6687228144139240791495083)
  ·
    refine ⟨10030842216208861187242625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6687228144139240791495083 10030842216208861187242625)
    ·
      refine ⟨7523131662156645890431969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10030842216208861187242625 7523131662156645890431969)
      ·
        refine ⟨5642348746617484417823977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7523131662156645890431969 5642348746617484417823977)
        ·
          refine ⟨4231761559963113313367983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5642348746617484417823977 4231761559963113313367983)
          ·
            refine ⟨6347642339944669970051975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231761559963113313367983 6347642339944669970051975)
            ·
              refine ⟨9521463509917004955077963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347642339944669970051975 9521463509917004955077963)
              ·
                refine ⟨14282195264875507432616945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9521463509917004955077963 14282195264875507432616945)
                ·
                  refine ⟨10711646448656630574462709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14282195264875507432616945 10711646448656630574462709)
                  ·
                    refine ⟨1004216854561559116355879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10711646448656630574462709 1004216854561559116355879)
                    ·
                      rfl

theorem cell22_2933558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2933558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933558 prefixEnd_2933558 := by exact prefixLift 2933558
  have htrace : WordTrace (prefixWord ++ tailWord_2933558) baseStart_2933558 baseEnd_2933558 := by
    simpa [prefixWord, tailWord_2933558, baseEnd_2933558] using wordTrace_append hprefix tailTrace_2933558
  have hstable : (prefixWord ++ tailWord_2933558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933558).length < 2 ^ (prefixWord ++ tailWord_2933558).sum := by decide
  have hdescent : baseEnd_2933558 < baseStart_2933558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933586 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_2933586 : Nat := 118140960795 + 2933586 * 2 ^ 59
def prefixEnd_2933586 : Nat := 4983230072969 + 3 ^ 40 * 2933586 * 2
def baseEnd_2933586 : Nat := 1004226439533776376655793

theorem tailTrace_2933586 : CollatzResearch.WordTrace tailWord_2933586 prefixEnd_2933586 1004226439533776376655793 := by
  unfold tailWord_2933586
  simp only [CollatzResearch.WordTrace]
  refine ⟨26749167887531603361485153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71331114366750942297293741 26749167887531603361485153)
  ·
    refine ⟨20061875915648702521113865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26749167887531603361485153 20061875915648702521113865)
    ·
      refine ⟨15046406936736526890835399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20061875915648702521113865 15046406936736526890835399)
      ·
        refine ⟨22569610405104790336253099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15046406936736526890835399 22569610405104790336253099)
        ·
          refine ⟨33854415607657185504379649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22569610405104790336253099 33854415607657185504379649)
          ·
            refine ⟨25390811705742889128284737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33854415607657185504379649 25390811705742889128284737)
            ·
              refine ⟨19043108779307166846213553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25390811705742889128284737 19043108779307166846213553)
              ·
                refine ⟨14282331584480375134660165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19043108779307166846213553 14282331584480375134660165)
                ·
                  refine ⟨2677937172090070337748781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14282331584480375134660165 2677937172090070337748781)
                  ·
                    refine ⟨1004226439533776376655793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677937172090070337748781 1004226439533776376655793)
                    ·
                      rfl

theorem cell22_2933586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_2933586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933586 prefixEnd_2933586 := by exact prefixLift 2933586
  have htrace : WordTrace (prefixWord ++ tailWord_2933586) baseStart_2933586 baseEnd_2933586 := by
    simpa [prefixWord, tailWord_2933586, baseEnd_2933586] using wordTrace_append hprefix tailTrace_2933586
  have hstable : (prefixWord ++ tailWord_2933586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933586).length < 2 ^ (prefixWord ++ tailWord_2933586).sum := by decide
  have hdescent : baseEnd_2933586 < baseStart_2933586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933603 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 2, 3]
def baseStart_2933603 : Nat := 118140960795 + 2933603 * 2 ^ 59
def prefixEnd_2933603 : Nat := 4983230072969 + 3 ^ 40 * 2933603 * 2
def baseEnd_2933603 : Nat := 1004232258981193998980741

theorem tailTrace_2933603 : CollatzResearch.WordTrace tailWord_2933603 prefixEnd_2933603 1004232258981193998980741 := by
  unfold tailWord_2933603
  simp only [CollatzResearch.WordTrace]
  refine ⟨106997291591064825349309463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71331527727376550232872975 106997291591064825349309463)
  ·
    refine ⟨160495937386597238023964195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106997291591064825349309463 160495937386597238023964195)
    ·
      refine ⟨240743906079895857035946293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160495937386597238023964195 240743906079895857035946293)
      ·
        refine ⟨22569741194990236597119965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240743906079895857035946293 22569741194990236597119965)
        ·
          refine ⟨8463652948121338723919987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22569741194990236597119965 8463652948121338723919987)
          ·
            refine ⟨12695479422182008085879981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463652948121338723919987 12695479422182008085879981)
            ·
              refine ⟨4760804783318253032204993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12695479422182008085879981 4760804783318253032204993)
              ·
                refine ⟨3570603587488689774153745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4760804783318253032204993 3570603587488689774153745)
                ·
                  refine ⟨2677952690616517330615309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3570603587488689774153745 2677952690616517330615309)
                  ·
                    refine ⟨1004232258981193998980741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677952690616517330615309 1004232258981193998980741)
                    ·
                      rfl

theorem cell22_2933603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 3].length) (baseStart_2933603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933603 prefixEnd_2933603 := by exact prefixLift 2933603
  have htrace : WordTrace (prefixWord ++ tailWord_2933603) baseStart_2933603 baseEnd_2933603 := by
    simpa [prefixWord, tailWord_2933603, baseEnd_2933603] using wordTrace_append hprefix tailTrace_2933603
  have hstable : (prefixWord ++ tailWord_2933603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933603).length < 2 ^ (prefixWord ++ tailWord_2933603).sum := by decide
  have hdescent : baseEnd_2933603 < baseStart_2933603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933629 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2933629 : Nat := 118140960795 + 2933629 * 2 ^ 59
def prefixEnd_2933629 : Nat := 4983230072969 + 3 ^ 40 * 2933629 * 2
def baseEnd_2933629 : Nat := 1004241159312538597830661

theorem tailTrace_2933629 : CollatzResearch.WordTrace tailWord_2933629 prefixEnd_2933629 1004241159312538597830661 := by
  unfold tailWord_2933629
  simp only [CollatzResearch.WordTrace]
  refine ⟨106998239888970631789755941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71332159925980421193170627 106998239888970631789755941)
  ·
    refine ⟨20062169979181993460579239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106998239888970631789755941 20062169979181993460579239)
    ·
      refine ⟨30093254968772990190868859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20062169979181993460579239 30093254968772990190868859)
      ·
        refine ⟨45139882453159485286303289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30093254968772990190868859 45139882453159485286303289)
        ·
          refine ⟨33854911839869613964727467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45139882453159485286303289 33854911839869613964727467)
          ·
            refine ⟨50782367759804420947091201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33854911839869613964727467 50782367759804420947091201)
            ·
              refine ⟨38086775819853315710318401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50782367759804420947091201 38086775819853315710318401)
              ·
                refine ⟨28565081864889986782738801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38086775819853315710318401 28565081864889986782738801)
                ·
                  refine ⟨21423811398667490087054101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28565081864889986782738801 21423811398667490087054101)
                  ·
                    refine ⟨1004241159312538597830661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21423811398667490087054101 1004241159312538597830661)
                    ·
                      rfl

theorem cell22_2933629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2933629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933629 prefixEnd_2933629 := by exact prefixLift 2933629
  have htrace : WordTrace (prefixWord ++ tailWord_2933629) baseStart_2933629 baseEnd_2933629 := by
    simpa [prefixWord, tailWord_2933629, baseEnd_2933629] using wordTrace_append hprefix tailTrace_2933629
  have hstable : (prefixWord ++ tailWord_2933629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933629).length < 2 ^ (prefixWord ++ tailWord_2933629).sum := by decide
  have hdescent : baseEnd_2933629 < baseStart_2933629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933631 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 3, 3]
def baseStart_2933631 : Nat := 118140960795 + 2933631 * 2 ^ 59
def prefixEnd_2933631 : Nat := 4983230072969 + 3 ^ 40 * 2933631 * 2
def baseEnd_2933631 : Nat := 1004241843953411259280655

theorem tailTrace_2933631 : CollatzResearch.WordTrace tailWord_2933631 prefixEnd_2933631 1004241843953411259280655 := by
  unfold tailWord_2933631
  simp only [CollatzResearch.WordTrace]
  refine ⟨106998312834963386131328747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71332208556642257420885831 106998312834963386131328747)
  ·
    refine ⟨160497469252445079196993121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106998312834963386131328747 160497469252445079196993121)
    ·
      refine ⟨120373101939333809397744841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160497469252445079196993121 120373101939333809397744841)
      ·
        refine ⟨90279826454500357048308631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120373101939333809397744841 90279826454500357048308631)
        ·
          refine ⟨135419739681750535572462947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90279826454500357048308631 135419739681750535572462947)
          ·
            refine ⟨203129609522625803358694421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135419739681750535572462947 203129609522625803358694421)
            ·
              refine ⟨9521700446373084532438801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 203129609522625803358694421 9521700446373084532438801)
              ·
                refine ⟨7141275334779813399329101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9521700446373084532438801 7141275334779813399329101)
                ·
                  refine ⟨2677978250542430024748413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7141275334779813399329101 2677978250542430024748413)
                  ·
                    refine ⟨1004241843953411259280655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2677978250542430024748413 1004241843953411259280655)
                    ·
                      rfl

theorem cell22_2933631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_2933631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933631 prefixEnd_2933631 := by exact prefixLift 2933631
  have htrace : WordTrace (prefixWord ++ tailWord_2933631) baseStart_2933631 baseEnd_2933631 := by
    simpa [prefixWord, tailWord_2933631, baseEnd_2933631] using wordTrace_append hprefix tailTrace_2933631
  have hstable : (prefixWord ++ tailWord_2933631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933631).length < 2 ^ (prefixWord ++ tailWord_2933631).sum := by decide
  have hdescent : baseEnd_2933631 < baseStart_2933631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933644 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 7]
def baseStart_2933644 : Nat := 118140960795 + 2933644 * 2 ^ 59
def prefixEnd_2933644 : Nat := 4983230072969 + 3 ^ 40 * 2933644 * 2
def baseEnd_2933644 : Nat := 334748764706361186235205

theorem tailTrace_2933644 : CollatzResearch.WordTrace tailWord_2933644 prefixEnd_2933644 334748764706361186235205 := by
  unfold tailWord_2933644
  simp only [CollatzResearch.WordTrace]
  refine ⟨53499393491958144675775993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71332524655944192901034657 53499393491958144675775993)
  ·
    refine ⟨40124545118968608506831995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53499393491958144675775993 40124545118968608506831995)
    ·
      refine ⟨60186817678452912760247993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40124545118968608506831995 60186817678452912760247993)
      ·
        refine ⟨45140113258839684570185995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60186817678452912760247993 45140113258839684570185995)
        ·
          refine ⟨67710169888259526855278993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45140113258839684570185995 67710169888259526855278993)
          ·
            refine ⟨50782627416194645141459245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67710169888259526855278993 50782627416194645141459245)
            ·
              refine ⟨19043485281072991928047217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50782627416194645141459245 19043485281072991928047217)
              ·
                refine ⟨14282613960804743946035413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19043485281072991928047217 14282613960804743946035413)
                ·
                  refine ⟨334748764706361186235205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14282613960804743946035413 334748764706361186235205)
                  ·
                    rfl

theorem cell22_2933644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_2933644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933644 prefixEnd_2933644 := by exact prefixLift 2933644
  have htrace : WordTrace (prefixWord ++ tailWord_2933644) baseStart_2933644 baseEnd_2933644 := by
    simpa [prefixWord, tailWord_2933644, baseEnd_2933644] using wordTrace_append hprefix tailTrace_2933644
  have hstable : (prefixWord ++ tailWord_2933644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933644).length < 2 ^ (prefixWord ++ tailWord_2933644).sum := by decide
  have hdescent : baseEnd_2933644 < baseStart_2933644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933661 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 5]
def baseStart_2933661 : Nat := 118140960795 + 2933661 * 2 ^ 59
def prefixEnd_2933661 : Nat := 4983230072969 + 3 ^ 40 * 2933661 * 2
def baseEnd_2933661 : Nat := 334750704522167060343521

theorem tailTrace_2933661 : CollatzResearch.WordTrace tailWord_2933661 prefixEnd_2933661 334750704522167060343521 := by
  unfold tailWord_2933661
  simp only [CollatzResearch.WordTrace]
  refine ⟨106999407024854701254920837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71332938016569800836613891 106999407024854701254920837)
  ·
    refine ⟨20062388817160256485297657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106999407024854701254920837 20062388817160256485297657)
    ·
      refine ⟨15046791612870192363973243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20062388817160256485297657 15046791612870192363973243)
      ·
        refine ⟨22570187419305288545959865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15046791612870192363973243 22570187419305288545959865)
        ·
          refine ⟨16927640564478966409469899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22570187419305288545959865 16927640564478966409469899)
          ·
            refine ⟨25391460846718449614204849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16927640564478966409469899 25391460846718449614204849)
            ·
              refine ⟨19043595635038837210653637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25391460846718449614204849 19043595635038837210653637)
              ·
                refine ⟨3570674181569781976997557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19043595635038837210653637 3570674181569781976997557)
                ·
                  refine ⟨334750704522167060343521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3570674181569781976997557 334750704522167060343521)
                  ·
                    rfl

theorem cell22_2933661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_2933661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933661 prefixEnd_2933661 := by exact prefixLift 2933661
  have htrace : WordTrace (prefixWord ++ tailWord_2933661) baseStart_2933661 baseEnd_2933661 := by
    simpa [prefixWord, tailWord_2933661, baseEnd_2933661] using wordTrace_append hprefix tailTrace_2933661
  have hstable : (prefixWord ++ tailWord_2933661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933661).length < 2 ^ (prefixWord ++ tailWord_2933661).sum := by decide
  have hdescent : baseEnd_2933661 < baseStart_2933661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933665 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 3, 3]
def baseStart_2933665 : Nat := 118140960795 + 2933665 * 2 ^ 59
def prefixEnd_2933665 : Nat := 4983230072969 + 3 ^ 40 * 2933665 * 2
def baseEnd_2933665 : Nat := 1004253482848246503930551

theorem tailTrace_2933665 : CollatzResearch.WordTrace tailWord_2933665 prefixEnd_2933665 1004253482848246503930551 := by
  unfold tailWord_2933665
  simp only [CollatzResearch.WordTrace]
  refine ⟨106999552916840209938066449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71333035277893473292044299 106999552916840209938066449)
  ·
    refine ⟨80249664687630157453549837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106999552916840209938066449 80249664687630157453549837)
    ·
      refine ⟨30093624257861309045081189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80249664687630157453549837 30093624257861309045081189)
      ·
        refine ⟨5642554548348995445952723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30093624257861309045081189 5642554548348995445952723)
        ·
          refine ⟨8463831822523493168929085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642554548348995445952723 8463831822523493168929085)
          ·
            refine ⟨3173936933446309938348407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8463831822523493168929085 3173936933446309938348407)
            ·
              refine ⟨4760905400169464907522611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173936933446309938348407 4760905400169464907522611)
              ·
                refine ⟨7141358100254197361283917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760905400169464907522611 7141358100254197361283917)
                ·
                  refine ⟨2678009287595324010481469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7141358100254197361283917 2678009287595324010481469)
                  ·
                    refine ⟨1004253482848246503930551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678009287595324010481469 1004253482848246503930551)
                    ·
                      rfl

theorem cell22_2933665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_2933665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933665 prefixEnd_2933665 := by exact prefixLift 2933665
  have htrace : WordTrace (prefixWord ++ tailWord_2933665) baseStart_2933665 baseEnd_2933665 := by
    simpa [prefixWord, tailWord_2933665, baseEnd_2933665] using wordTrace_append hprefix tailTrace_2933665
  have hstable : (prefixWord ++ tailWord_2933665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933665).length < 2 ^ (prefixWord ++ tailWord_2933665).sum := by decide
  have hdescent : baseEnd_2933665 < baseStart_2933665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933736 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2933736 : Nat := 118140960795 + 2933736 * 2 ^ 59
def prefixEnd_2933736 : Nat := 4983230072969 + 3 ^ 40 * 2933736 * 2
def baseEnd_2933736 : Nat := 1004277787599225985405333

theorem tailTrace_2933736 : CollatzResearch.WordTrace tailWord_2933736 prefixEnd_2933736 1004277787599225985405333 := by
  unfold tailWord_2933736
  simp only [CollatzResearch.WordTrace]
  refine ⟨53501071249791494531950531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71334761666388659375934041 53501071249791494531950531)
  ·
    refine ⟨80251606874687241797925797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53501071249791494531950531 80251606874687241797925797)
    ·
      refine ⟨15047176289003857837111087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80251606874687241797925797 15047176289003857837111087)
      ·
        refine ⟨22570764433505786755666631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15047176289003857837111087 22570764433505786755666631)
        ·
          refine ⟨33856146650258680133499947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22570764433505786755666631 33856146650258680133499947)
          ·
            refine ⟨50784219975388020200249921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33856146650258680133499947 50784219975388020200249921)
            ·
              refine ⟨38088164981541015150187441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50784219975388020200249921 38088164981541015150187441)
              ·
                refine ⟨28566123736155761362640581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38088164981541015150187441 28566123736155761362640581)
                ·
                  refine ⟨5356148200529205255495109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28566123736155761362640581 5356148200529205255495109)
                  ·
                    refine ⟨1004277787599225985405333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5356148200529205255495109 1004277787599225985405333)
                    ·
                      rfl

theorem cell22_2933736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2933736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933736 prefixEnd_2933736 := by exact prefixLift 2933736
  have htrace : WordTrace (prefixWord ++ tailWord_2933736) baseStart_2933736 baseEnd_2933736 := by
    simpa [prefixWord, tailWord_2933736, baseEnd_2933736] using wordTrace_append hprefix tailTrace_2933736
  have hstable : (prefixWord ++ tailWord_2933736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933736).length < 2 ^ (prefixWord ++ tailWord_2933736).sum := by decide
  have hdescent : baseEnd_2933736 < baseStart_2933736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933738 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2933738 : Nat := 118140960795 + 2933738 * 2 ^ 59
def prefixEnd_2933738 : Nat := 4983230072969 + 3 ^ 40 * 2933738 * 2
def baseEnd_2933738 : Nat := 1004278472240098646855327

theorem tailTrace_2933738 : CollatzResearch.WordTrace tailWord_2933738 prefixEnd_2933738 1004278472240098646855327 := by
  unfold tailWord_2933738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26750553861393935851368467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71334810297050495603649245 26750553861393935851368467)
  ·
    refine ⟨40125830792090903777052701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26750553861393935851368467 40125830792090903777052701)
    ·
      refine ⟨15047186547034088916394763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40125830792090903777052701 15047186547034088916394763)
      ·
        refine ⟨22570779820551133374592145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15047186547034088916394763 22570779820551133374592145)
        ·
          refine ⟨16928084865413350030944109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22570779820551133374592145 16928084865413350030944109)
          ·
            refine ⟨6348031824530006261604041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16928084865413350030944109 6348031824530006261604041)
            ·
              refine ⟨4761023868397504696203031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6348031824530006261604041 4761023868397504696203031)
              ·
                refine ⟨7141535802596257044304547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761023868397504696203031 7141535802596257044304547)
                ·
                  refine ⟨10712303703894385566456821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141535802596257044304547 10712303703894385566456821)
                  ·
                    refine ⟨1004278472240098646855327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10712303703894385566456821 1004278472240098646855327)
                    ·
                      rfl

theorem cell22_2933738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2933738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933738 prefixEnd_2933738 := by exact prefixLift 2933738
  have htrace : WordTrace (prefixWord ++ tailWord_2933738) baseStart_2933738 baseEnd_2933738 := by
    simpa [prefixWord, tailWord_2933738, baseEnd_2933738] using wordTrace_append hprefix tailTrace_2933738
  have hstable : (prefixWord ++ tailWord_2933738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933738).length < 2 ^ (prefixWord ++ tailWord_2933738).sum := by decide
  have hdescent : baseEnd_2933738 < baseStart_2933738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933802 : List Nat := [3, 1, 4, 1, 4, 1, 2, 6]
def baseStart_2933802 : Nat := 118140960795 + 2933802 * 2 ^ 59
def prefixEnd_2933802 : Nat := 4983230072969 + 3 ^ 40 * 2933802 * 2
def baseEnd_2933802 : Nat := 111588931194224868139459

theorem tailTrace_2933802 : CollatzResearch.WordTrace tailWord_2933802 prefixEnd_2933802 111588931194224868139459 := by
  unfold tailWord_2933802
  simp only [CollatzResearch.WordTrace]
  refine ⟨26751137429335970583950915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71336366478229254890535773 26751137429335970583950915)
  ·
    refine ⟨40126706144003955875926373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26751137429335970583950915 40126706144003955875926373)
    ·
      refine ⟨7523757402000741726736195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40126706144003955875926373 7523757402000741726736195)
      ·
        refine ⟨11285636103001112590104293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7523757402000741726736195 11285636103001112590104293)
        ·
          refine ⟨2116056769312708610644555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11285636103001112590104293 2116056769312708610644555)
          ·
            refine ⟨3174085153969062915966833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116056769312708610644555 3174085153969062915966833)
            ·
              refine ⟨2380563865476797186975125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3174085153969062915966833 2380563865476797186975125)
              ·
                refine ⟨111588931194224868139459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2380563865476797186975125 111588931194224868139459)
                ·
                  rfl

theorem cell22_2933802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_2933802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933802 prefixEnd_2933802 := by exact prefixLift 2933802
  have htrace : WordTrace (prefixWord ++ tailWord_2933802) baseStart_2933802 baseEnd_2933802 := by
    simpa [prefixWord, tailWord_2933802, baseEnd_2933802] using wordTrace_append hprefix tailTrace_2933802
  have hstable : (prefixWord ++ tailWord_2933802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933802).length < 2 ^ (prefixWord ++ tailWord_2933802).sum := by decide
  have hdescent : baseEnd_2933802 < baseStart_2933802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933817 : List Nat := [1, 2, 1, 5, 2, 1, 3, 3, 1, 3]
def baseStart_2933817 : Nat := 118140960795 + 2933817 * 2 ^ 59
def prefixEnd_2933817 : Nat := 4983230072969 + 3 ^ 40 * 2933817 * 2
def baseEnd_2933817 : Nat := 1004305515554568774130085

theorem tailTrace_2933817 : CollatzResearch.WordTrace tailWord_2933817 prefixEnd_2933817 1004305515554568774130085 := by
  unfold tailWord_2933817
  simp only [CollatzResearch.WordTrace]
  refine ⟨107005096812289539897599705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71336731208193026598399803 107005096812289539897599705)
  ·
    refine ⟨80253822609217154923199779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107005096812289539897599705 80253822609217154923199779)
    ·
      refine ⟨120380733913825732384799669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80253822609217154923199779 120380733913825732384799669)
      ·
        refine ⟨11285693804421162411074969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120380733913825732384799669 11285693804421162411074969)
        ·
          refine ⟨8464270353315871808306227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11285693804421162411074969 8464270353315871808306227)
          ·
            refine ⟨12696405529973807712459341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8464270353315871808306227 12696405529973807712459341)
            ·
              refine ⟨4761152073740177892172253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12696405529973807712459341 4761152073740177892172253)
              ·
                refine ⟨1785432027652566709564595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4761152073740177892172253 1785432027652566709564595)
                ·
                  refine ⟨2678148041478850064346893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785432027652566709564595 2678148041478850064346893)
                  ·
                    refine ⟨1004305515554568774130085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678148041478850064346893 1004305515554568774130085)
                    ·
                      rfl

theorem cell22_2933817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 3].length) (baseStart_2933817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933817 prefixEnd_2933817 := by exact prefixLift 2933817
  have htrace : WordTrace (prefixWord ++ tailWord_2933817) baseStart_2933817 baseEnd_2933817 := by
    simpa [prefixWord, tailWord_2933817, baseEnd_2933817] using wordTrace_append hprefix tailTrace_2933817
  have hstable : (prefixWord ++ tailWord_2933817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933817).length < 2 ^ (prefixWord ++ tailWord_2933817).sum := by decide
  have hdescent : baseEnd_2933817 < baseStart_2933817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933830 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2933830 : Nat := 118140960795 + 2933830 * 2 ^ 59
def prefixEnd_2933830 : Nat := 4983230072969 + 3 ^ 40 * 2933830 * 2
def baseEnd_2933830 : Nat := 334769988573413691185015

theorem tailTrace_2933830 : CollatzResearch.WordTrace tailWord_2933830 prefixEnd_2933830 334769988573413691185015 := by
  unfold tailWord_2933830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3343924092538826347431967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71337047307494962078548629 3343924092538826347431967)
  ·
    refine ⟨5015886138808239521147951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3343924092538826347431967 5015886138808239521147951)
    ·
      refine ⟨7523829208212359281721927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5015886138808239521147951 7523829208212359281721927)
      ·
        refine ⟨11285743812318538922582891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7523829208212359281721927 11285743812318538922582891)
        ·
          refine ⟨16928615718477808383874337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11285743812318538922582891 16928615718477808383874337)
          ·
            refine ⟨12696461788858356287905753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16928615718477808383874337 12696461788858356287905753)
            ·
              refine ⟨9522346341643767215929315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12696461788858356287905753 9522346341643767215929315)
              ·
                refine ⟨14283519512465650823893973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9522346341643767215929315 14283519512465650823893973)
                ·
                  refine ⟨334769988573413691185015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14283519512465650823893973 334769988573413691185015)
                  ·
                    rfl

theorem cell22_2933830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2933830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933830 prefixEnd_2933830 := by exact prefixLift 2933830
  have htrace : WordTrace (prefixWord ++ tailWord_2933830) baseStart_2933830 baseEnd_2933830 := by
    simpa [prefixWord, tailWord_2933830, baseEnd_2933830] using wordTrace_append hprefix tailTrace_2933830
  have hstable : (prefixWord ++ tailWord_2933830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933830).length < 2 ^ (prefixWord ++ tailWord_2933830).sum := by decide
  have hdescent : baseEnd_2933830 < baseStart_2933830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933873 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 4, 3]
def baseStart_2933873 : Nat := 118140960795 + 2933873 * 2 ^ 59
def prefixEnd_2933873 : Nat := 4983230072969 + 3 ^ 40 * 2933873 * 2
def baseEnd_2933873 : Nat := 1004324685499003294729913

theorem tailTrace_2933873 : CollatzResearch.WordTrace tailWord_2933873 prefixEnd_2933873 1004324685499003294729913 := by
  unfold tailWord_2933873
  simp only [CollatzResearch.WordTrace]
  refine ⟨107007139300086661461638273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71338092866724440974425515 107007139300086661461638273)
  ·
    refine ⟨80255354475064996096228705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107007139300086661461638273 80255354475064996096228705)
    ·
      refine ⟨60191515856298747072171529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80255354475064996096228705 60191515856298747072171529)
      ·
        refine ⟨45143636892224060304128647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60191515856298747072171529 45143636892224060304128647)
        ·
          refine ⟨67715455338336090456192971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45143636892224060304128647 67715455338336090456192971)
          ·
            refine ⟨101573183007504135684289457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67715455338336090456192971 101573183007504135684289457)
            ·
              refine ⟨76179887255628101763217093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101573183007504135684289457 76179887255628101763217093)
              ·
                refine ⟨14283728860430269080603205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76179887255628101763217093 14283728860430269080603205)
                ·
                  refine ⟨2678199161330675452613101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14283728860430269080603205 2678199161330675452613101)
                  ·
                    refine ⟨1004324685499003294729913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678199161330675452613101 1004324685499003294729913)
                    ·
                      rfl

theorem cell22_2933873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_2933873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933873 prefixEnd_2933873 := by exact prefixLift 2933873
  have htrace : WordTrace (prefixWord ++ tailWord_2933873) baseStart_2933873 baseEnd_2933873 := by
    simpa [prefixWord, tailWord_2933873, baseEnd_2933873] using wordTrace_append hprefix tailTrace_2933873
  have hstable : (prefixWord ++ tailWord_2933873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933873).length < 2 ^ (prefixWord ++ tailWord_2933873).sum := by decide
  have hdescent : baseEnd_2933873 < baseStart_2933873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933888 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_2933888 : Nat := 118140960795 + 2933888 * 2 ^ 59
def prefixEnd_2933888 : Nat := 4983230072969 + 3 ^ 40 * 2933888 * 2
def baseEnd_2933888 : Nat := 1004329820305548255604867

theorem tailTrace_2933888 : CollatzResearch.WordTrace tailWord_2933888 prefixEnd_2933888 1004329820305548255604867 := by
  unfold tailWord_2933888
  simp only [CollatzResearch.WordTrace]
  refine ⟨53503843197516159511717159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71338457596688212682289545 53503843197516159511717159)
  ·
    refine ⟨80255764796274239267575739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53503843197516159511717159 80255764796274239267575739)
    ·
      refine ⟨120383647194411358901363609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80255764796274239267575739 120383647194411358901363609)
      ·
        refine ⟨90287735395808519176022707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120383647194411358901363609 90287735395808519176022707)
        ·
          refine ⟨135431603093712778764034061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90287735395808519176022707 135431603093712778764034061)
          ·
            refine ⟨50786851160142292036512773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135431603093712778764034061 50786851160142292036512773)
            ·
              refine ⟨9522534592526679756846145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50786851160142292036512773 9522534592526679756846145)
              ·
                refine ⟨7141900944395009817634609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9522534592526679756846145 7141900944395009817634609)
                ·
                  refine ⟨5356425708296257363225957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7141900944395009817634609 5356425708296257363225957)
                  ·
                    refine ⟨1004329820305548255604867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5356425708296257363225957 1004329820305548255604867)
                    ·
                      rfl

theorem cell22_2933888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_2933888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933888 prefixEnd_2933888 := by exact prefixLift 2933888
  have htrace : WordTrace (prefixWord ++ tailWord_2933888) baseStart_2933888 baseEnd_2933888 := by
    simpa [prefixWord, tailWord_2933888, baseEnd_2933888] using wordTrace_append hprefix tailTrace_2933888
  have hstable : (prefixWord ++ tailWord_2933888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933888).length < 2 ^ (prefixWord ++ tailWord_2933888).sum := by decide
  have hdescent : baseEnd_2933888 < baseStart_2933888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933892 : List Nat := [2, 3, 2, 1, 2, 2, 4, 2, 4]
def baseStart_2933892 : Nat := 118140960795 + 2933892 * 2 ^ 59
def prefixEnd_2933892 : Nat := 4983230072969 + 3 ^ 40 * 2933892 * 2
def baseEnd_2933892 : Nat := 334777063195764526168285

theorem tailTrace_2933892 : CollatzResearch.WordTrace tailWord_2933892 prefixEnd_2933892 334777063195764526168285 := by
  unfold tailWord_2933892
  simp only [CollatzResearch.WordTrace]
  refine ⟨53503916143508913853289965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71338554858011885137719953 53503916143508913853289965)
  ·
    refine ⟨20063968553815842694983737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53503916143508913853289965 20063968553815842694983737)
    ·
      refine ⟨15047976415361882021237803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20063968553815842694983737 15047976415361882021237803)
      ·
        refine ⟨22571964623042823031856705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15047976415361882021237803 22571964623042823031856705)
        ·
          refine ⟨16928973467282117273892529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22571964623042823031856705 16928973467282117273892529)
          ·
            refine ⟨12696730100461587955419397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16928973467282117273892529 12696730100461587955419397)
            ·
              refine ⟨2380636893836547741641137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12696730100461587955419397 2380636893836547741641137)
              ·
                refine ⟨1785477670377410806230853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2380636893836547741641137 1785477670377410806230853)
                ·
                  refine ⟨334777063195764526168285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785477670377410806230853 334777063195764526168285)
                  ·
                    rfl

theorem cell22_2933892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_2933892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933892 prefixEnd_2933892 := by exact prefixLift 2933892
  have htrace : WordTrace (prefixWord ++ tailWord_2933892) baseStart_2933892 baseEnd_2933892 := by
    simpa [prefixWord, tailWord_2933892, baseEnd_2933892] using wordTrace_append hprefix tailTrace_2933892
  have hstable : (prefixWord ++ tailWord_2933892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933892).length < 2 ^ (prefixWord ++ tailWord_2933892).sum := by decide
  have hdescent : baseEnd_2933892 < baseStart_2933892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933952 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 3, 3]
def baseStart_2933952 : Nat := 118140960795 + 2933952 * 2 ^ 59
def prefixEnd_2933952 : Nat := 4983230072969 + 3 ^ 40 * 2933952 * 2
def baseEnd_2933952 : Nat := 1004351728813473422004671

theorem tailTrace_2933952 : CollatzResearch.WordTrace tailWord_2933952 prefixEnd_2933952 1004351728813473422004671 := by
  unfold tailWord_2933952
  simp only [CollatzResearch.WordTrace]
  refine ⟨53505010333400228976882055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71340013777866971969176073 53505010333400228976882055)
  ·
    refine ⟨80257515500100343465323083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53505010333400228976882055 80257515500100343465323083)
    ·
      refine ⟨120386273250150515197984625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80257515500100343465323083 120386273250150515197984625)
      ·
        refine ⟨90289704937612886398488469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120386273250150515197984625 90289704937612886398488469)
        ·
          refine ⟨4232329918950604049929147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90289704937612886398488469 4232329918950604049929147)
          ·
            refine ⟨6348494878425906074893721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232329918950604049929147 6348494878425906074893721)
            ·
              refine ⟨4761371158819429556170291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6348494878425906074893721 4761371158819429556170291)
              ·
                refine ⟨7142056738229144334255437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761371158819429556170291 7142056738229144334255437)
                ·
                  refine ⟨2678271276835929125345789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7142056738229144334255437 2678271276835929125345789)
                  ·
                    refine ⟨1004351728813473422004671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678271276835929125345789 1004351728813473422004671)
                    ·
                      rfl

theorem cell22_2933952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_2933952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933952 prefixEnd_2933952 := by exact prefixLift 2933952
  have htrace : WordTrace (prefixWord ++ tailWord_2933952) baseStart_2933952 baseEnd_2933952 := by
    simpa [prefixWord, tailWord_2933952, baseEnd_2933952] using wordTrace_append hprefix tailTrace_2933952
  have hstable : (prefixWord ++ tailWord_2933952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933952).length < 2 ^ (prefixWord ++ tailWord_2933952).sum := by decide
  have hdescent : baseEnd_2933952 < baseStart_2933952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933958 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2933958 : Nat := 118140960795 + 2933958 * 2 ^ 59
def prefixEnd_2933958 : Nat := 4983230072969 + 3 ^ 40 * 2933958 * 2
def baseEnd_2933958 : Nat := 1004353782736091406354653

theorem tailTrace_2933958 : CollatzResearch.WordTrace tailWord_2933958 prefixEnd_2933958 1004353782736091406354653 := by
  unfold tailWord_2933958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344069984524335030577579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71340159669852480652321685 3344069984524335030577579)
  ·
    refine ⟨5016104976786502545866369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3344069984524335030577579 5016104976786502545866369)
    ·
      refine ⟨3762078732589876909399777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5016104976786502545866369 3762078732589876909399777)
      ·
        refine ⟨2821559049442407682049833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3762078732589876909399777 2821559049442407682049833)
        ·
          refine ⟨2116169287081805761537375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821559049442407682049833 2116169287081805761537375)
          ·
            refine ⟨3174253930622708642306063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116169287081805761537375 3174253930622708642306063)
            ·
              refine ⟨4761380895934062963459095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174253930622708642306063 4761380895934062963459095)
              ·
                refine ⟨7142071343901094445188643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761380895934062963459095 7142071343901094445188643)
                ·
                  refine ⟨10713107015851641667782965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7142071343901094445188643 10713107015851641667782965)
                  ·
                    refine ⟨1004353782736091406354653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10713107015851641667782965 1004353782736091406354653)
                    ·
                      rfl

theorem cell22_2933958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2933958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933958 prefixEnd_2933958 := by exact prefixLift 2933958
  have htrace : WordTrace (prefixWord ++ tailWord_2933958) baseStart_2933958 baseEnd_2933958 := by
    simpa [prefixWord, tailWord_2933958, baseEnd_2933958] using wordTrace_append hprefix tailTrace_2933958
  have hstable : (prefixWord ++ tailWord_2933958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933958).length < 2 ^ (prefixWord ++ tailWord_2933958).sum := by decide
  have hdescent : baseEnd_2933958 < baseStart_2933958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933995 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 1, 4]
def baseStart_2933995 : Nat := 118140960795 + 2933995 * 2 ^ 59
def prefixEnd_2933995 : Nat := 4983230072969 + 3 ^ 40 * 2933995 * 2
def baseEnd_2933995 : Nat := 1004366448592235643179539

theorem tailTrace_2933995 : CollatzResearch.WordTrace tailWord_2933995 prefixEnd_2933995 1004366448592235643179539 := by
  unfold tailWord_2933995
  simp only [CollatzResearch.WordTrace]
  refine ⟨107011589005644676297579439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71341059337096450865052959 107011589005644676297579439)
  ·
    refine ⟨160517383508467014446369159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107011589005644676297579439 160517383508467014446369159)
    ·
      refine ⟨240776075262700521669553739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160517383508467014446369159 240776075262700521669553739)
      ·
        refine ⟨361164112894050782504330609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240776075262700521669553739 361164112894050782504330609)
        ·
          refine ⟨270873084670538086878247957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361164112894050782504330609 270873084670538086878247957)
          ·
            refine ⟨12697175843931472822417873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 270873084670538086878247957 12697175843931472822417873)
            ·
              refine ⟨9522881882948604616813405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12697175843931472822417873 9522881882948604616813405)
              ·
                refine ⟨3571080706105726731305027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9522881882948604616813405 3571080706105726731305027)
                ·
                  refine ⟨5356621059158590096957541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571080706105726731305027 5356621059158590096957541)
                  ·
                    refine ⟨1004366448592235643179539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5356621059158590096957541 1004366448592235643179539)
                    ·
                      rfl

theorem cell22_2933995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 4].length) (baseStart_2933995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2933995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2933995 prefixEnd_2933995 := by exact prefixLift 2933995
  have htrace : WordTrace (prefixWord ++ tailWord_2933995) baseStart_2933995 baseEnd_2933995 := by
    simpa [prefixWord, tailWord_2933995, baseEnd_2933995] using wordTrace_append hprefix tailTrace_2933995
  have hstable : (prefixWord ++ tailWord_2933995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933995).length < 2 ^ (prefixWord ++ tailWord_2933995).sum := by decide
  have hdescent : baseEnd_2933995 < baseStart_2933995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934040 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_2934040 : Nat := 118140960795 + 2934040 * 2 ^ 59
def prefixEnd_2934040 : Nat := 4983230072969 + 3 ^ 40 * 2934040 * 2
def baseEnd_2934040 : Nat := 1004381853011870525804401

theorem tailTrace_2934040 : CollatzResearch.WordTrace tailWord_2934040 prefixEnd_2934040 1004381853011870525804401 := by
  unfold tailWord_2934040
  simp only [CollatzResearch.WordTrace]
  refine ⟨53506615145240824491483787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71342153526987765988645049 53506615145240824491483787)
  ·
    refine ⟨80259922717861236737225681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53506615145240824491483787 80259922717861236737225681)
    ·
      refine ⟨60194942038395927552919261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80259922717861236737225681 60194942038395927552919261)
      ·
        refine ⟨22573103264398472832344723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60194942038395927552919261 22573103264398472832344723)
        ·
          refine ⟨33859654896597709248517085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22573103264398472832344723 33859654896597709248517085)
          ·
            refine ⟨12697370586224140968193907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33859654896597709248517085 12697370586224140968193907)
            ·
              refine ⟨19046055879336211452290861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12697370586224140968193907 19046055879336211452290861)
              ·
                refine ⟨7142270954751079294609073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19046055879336211452290861 7142270954751079294609073)
                ·
                  refine ⟨5356703216063309470956805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7142270954751079294609073 5356703216063309470956805)
                  ·
                    refine ⟨1004381853011870525804401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5356703216063309470956805 1004381853011870525804401)
                    ·
                      rfl

theorem cell22_2934040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_2934040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934040 prefixEnd_2934040 := by exact prefixLift 2934040
  have htrace : WordTrace (prefixWord ++ tailWord_2934040) baseStart_2934040 baseEnd_2934040 := by
    simpa [prefixWord, tailWord_2934040, baseEnd_2934040] using wordTrace_append hprefix tailTrace_2934040
  have hstable : (prefixWord ++ tailWord_2934040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934040).length < 2 ^ (prefixWord ++ tailWord_2934040).sum := by decide
  have hdescent : baseEnd_2934040 < baseStart_2934040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934055 : List Nat := [1, 1, 8, 12]
def baseStart_2934055 : Nat := 118140960795 + 2934055 * 2 ^ 59
def prefixEnd_2934055 : Nat := 4983230072969 + 3 ^ 40 * 2934055 * 2
def baseEnd_2934055 : Nat := 1377759928420323026995

theorem tailTrace_2934055 : CollatzResearch.WordTrace tailWord_2934055 prefixEnd_2934055 1377759928420323026995 := by
  unfold tailWord_2934055
  simp only [CollatzResearch.WordTrace]
  refine ⟨107013777385427306544763619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71342518256951537696509079 107013777385427306544763619)
  ·
    refine ⟨160520666078140959817145429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107013777385427306544763619 160520666078140959817145429)
    ·
      refine ⟨1881101555603214372857173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 160520666078140959817145429 1881101555603214372857173)
      ·
        refine ⟨1377759928420323026995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1881101555603214372857173 1377759928420323026995)
        ·
          rfl

theorem cell22_2934055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 12].length) (baseStart_2934055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934055 prefixEnd_2934055 := by exact prefixLift 2934055
  have htrace : WordTrace (prefixWord ++ tailWord_2934055) baseStart_2934055 baseEnd_2934055 := by
    simpa [prefixWord, tailWord_2934055, baseEnd_2934055] using wordTrace_append hprefix tailTrace_2934055
  have hstable : (prefixWord ++ tailWord_2934055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934055).length < 2 ^ (prefixWord ++ tailWord_2934055).sum := by decide
  have hdescent : baseEnd_2934055 < baseStart_2934055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934061 : List Nat := [1, 5, 3, 1, 1, 1, 4, 2, 4]
def baseStart_2934061 : Nat := 118140960795 + 2934061 * 2 ^ 59
def prefixEnd_2934061 : Nat := 4983230072969 + 3 ^ 40 * 2934061 * 2
def baseEnd_2934061 : Nat := 334796347247011157009779

theorem tailTrace_2934061 : CollatzResearch.WordTrace tailWord_2934061 prefixEnd_2934061 334796347247011157009779 := by
  unfold tailWord_2934061
  simp only [CollatzResearch.WordTrace]
  refine ⟨107013996223405569569482037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71342664148937046379654691 107013996223405569569482037)
  ·
    refine ⟨10032562145944272147138941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107013996223405569569482037 10032562145944272147138941)
    ·
      refine ⟨3762210804729102055177103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10032562145944272147138941 3762210804729102055177103)
      ·
        refine ⟨5643316207093653082765655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3762210804729102055177103 5643316207093653082765655)
        ·
          refine ⟨8464974310640479624148483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643316207093653082765655 8464974310640479624148483)
          ·
            refine ⟨12697461465960719436222725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8464974310640479624148483 12697461465960719436222725)
            ·
              refine ⟨2380774024867634894291761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12697461465960719436222725 2380774024867634894291761)
              ·
                refine ⟨1785580518650726170718821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2380774024867634894291761 1785580518650726170718821)
                ·
                  refine ⟨334796347247011157009779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785580518650726170718821 334796347247011157009779)
                  ·
                    rfl

theorem cell22_2934061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_2934061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934061 prefixEnd_2934061 := by exact prefixLift 2934061
  have htrace : WordTrace (prefixWord ++ tailWord_2934061) baseStart_2934061 baseEnd_2934061 := by
    simpa [prefixWord, tailWord_2934061, baseEnd_2934061] using wordTrace_append hprefix tailTrace_2934061
  have hstable : (prefixWord ++ tailWord_2934061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934061).length < 2 ^ (prefixWord ++ tailWord_2934061).sum := by decide
  have hdescent : baseEnd_2934061 < baseStart_2934061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934083 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 9]
def baseStart_2934083 : Nat := 118140960795 + 2934083 * 2 ^ 59
def prefixEnd_2934083 : Nat := 4983230072969 + 3 ^ 40 * 2934083 * 2
def baseEnd_2934083 : Nat := 334798857596877582326423

theorem tailTrace_2934083 : CollatzResearch.WordTrace tailWord_2934083 prefixEnd_2934083 334798857596877582326423 := by
  unfold tailWord_2934083
  simp only [CollatzResearch.WordTrace]
  refine ⟨107014798629325867326782903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71343199086217244884521935 107014798629325867326782903)
  ·
    refine ⟨160522197943988800990174355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107014798629325867326782903 160522197943988800990174355)
    ·
      refine ⟨240783296915983201485261533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160522197943988800990174355 240783296915983201485261533)
      ·
        refine ⟨90293736343493700556973075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240783296915983201485261533 90293736343493700556973075)
        ·
          refine ⟨135440604515240550835459613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90293736343493700556973075 135440604515240550835459613)
          ·
            refine ⟨50790226693215206563297355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135440604515240550835459613 50790226693215206563297355)
            ·
              refine ⟨76185340039822809844946033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50790226693215206563297355 76185340039822809844946033)
              ·
                refine ⟨57139005029867107383709525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76185340039822809844946033 57139005029867107383709525)
                ·
                  refine ⟨334798857596877582326423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57139005029867107383709525 334798857596877582326423)
                  ·
                    rfl

theorem cell22_2934083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 9].length) (baseStart_2934083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934083 prefixEnd_2934083 := by exact prefixLift 2934083
  have htrace : WordTrace (prefixWord ++ tailWord_2934083) baseStart_2934083 baseEnd_2934083 := by
    simpa [prefixWord, tailWord_2934083, baseEnd_2934083] using wordTrace_append hprefix tailTrace_2934083
  have hstable : (prefixWord ++ tailWord_2934083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934083).length < 2 ^ (prefixWord ++ tailWord_2934083).sum := by decide
  have hdescent : baseEnd_2934083 < baseStart_2934083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934087 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 3, 3]
def baseStart_2934087 : Nat := 118140960795 + 2934087 * 2 ^ 59
def prefixEnd_2934087 : Nat := 4983230072969 + 3 ^ 40 * 2934087 * 2
def baseEnd_2934087 : Nat := 1004397942072378069879257

theorem tailTrace_2934087 : CollatzResearch.WordTrace tailWord_2934087 prefixEnd_2934087 1004397942072378069879257 := by
  unfold tailWord_2934087
  simp only [CollatzResearch.WordTrace]
  refine ⟨107014944521311376009928515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71343296347540917339952343 107014944521311376009928515)
  ·
    refine ⟨160522416781967064014892773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107014944521311376009928515 160522416781967064014892773)
    ·
      refine ⟨30097953146618824502792395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160522416781967064014892773 30097953146618824502792395)
      ·
        refine ⟨45146929719928236754188593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30097953146618824502792395 45146929719928236754188593)
        ·
          refine ⟨33860197289946177565641445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45146929719928236754188593 33860197289946177565641445)
          ·
            refine ⟨6348786991864908293557771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33860197289946177565641445 6348786991864908293557771)
            ·
              refine ⟨9523180487797362440336657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6348786991864908293557771 9523180487797362440336657)
              ·
                refine ⟨7142385365848021830252493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9523180487797362440336657 7142385365848021830252493)
                ·
                  refine ⟨2678394512193008186344685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7142385365848021830252493 2678394512193008186344685)
                  ·
                    refine ⟨1004397942072378069879257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678394512193008186344685 1004397942072378069879257)
                    ·
                      rfl

theorem cell22_2934087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_2934087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934087 prefixEnd_2934087 := by exact prefixLift 2934087
  have htrace : WordTrace (prefixWord ++ tailWord_2934087) baseStart_2934087 baseEnd_2934087 := by
    simpa [prefixWord, tailWord_2934087, baseEnd_2934087] using wordTrace_append hprefix tailTrace_2934087
  have hstable : (prefixWord ++ tailWord_2934087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934087).length < 2 ^ (prefixWord ++ tailWord_2934087).sum := by decide
  have hdescent : baseEnd_2934087 < baseStart_2934087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934100 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 7]
def baseStart_2934100 : Nat := 118140960795 + 2934100 * 2 ^ 59
def prefixEnd_2934100 : Nat := 4983230072969 + 3 ^ 40 * 2934100 * 2
def baseEnd_2934100 : Nat := 334800797412683456434739

theorem tailTrace_2934100 : CollatzResearch.WordTrace tailWord_2934100 prefixEnd_2934100 334800797412683456434739 := by
  unfold tailWord_2934100
  simp only [CollatzResearch.WordTrace]
  refine ⟨53507709335132139615075877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71343612446842852820101169 53507709335132139615075877)
  ·
    refine ⟨10032695500337276177826727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53507709335132139615075877 10032695500337276177826727)
    ·
      refine ⟨15049043250505914266740091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10032695500337276177826727 15049043250505914266740091)
      ·
        refine ⟨22573564875758871400110137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15049043250505914266740091 22573564875758871400110137)
        ·
          refine ⟨16930173656819153550082603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22573564875758871400110137 16930173656819153550082603)
          ·
            refine ⟨25395260485228730325123905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16930173656819153550082603 25395260485228730325123905)
            ·
              refine ⟨19046445363921547743842929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25395260485228730325123905 19046445363921547743842929)
              ·
                refine ⟨14284834022941160807882197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19046445363921547743842929 14284834022941160807882197)
                ·
                  refine ⟨334800797412683456434739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14284834022941160807882197 334800797412683456434739)
                  ·
                    rfl

theorem cell22_2934100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_2934100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934100 prefixEnd_2934100 := by exact prefixLift 2934100
  have htrace : WordTrace (prefixWord ++ tailWord_2934100) baseStart_2934100 baseEnd_2934100 := by
    simpa [prefixWord, tailWord_2934100, baseEnd_2934100] using wordTrace_append hprefix tailTrace_2934100
  have hstable : (prefixWord ++ tailWord_2934100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934100).length < 2 ^ (prefixWord ++ tailWord_2934100).sum := by decide
  have hdescent : baseEnd_2934100 < baseStart_2934100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934104 : List Nat := [2, 1, 2, 2, 1, 1, 6, 3, 1, 3]
def baseStart_2934104 : Nat := 118140960795 + 2934104 * 2 ^ 59
def prefixEnd_2934104 : Nat := 4983230072969 + 3 ^ 40 * 2934104 * 2
def baseEnd_2934104 : Nat := 1004403761519795692204205

theorem tailTrace_2934104 : CollatzResearch.WordTrace tailWord_2934104 prefixEnd_2934104 1004403761519795692204205 := by
  unfold tailWord_2934104
  simp only [CollatzResearch.WordTrace]
  refine ⟨53507782281124893956648683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71343709708166525275531577 53507782281124893956648683)
  ·
    refine ⟨80261673421687340934973025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53507782281124893956648683 80261673421687340934973025)
    ·
      refine ⟨60196255066265505701229769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80261673421687340934973025 60196255066265505701229769)
      ·
        refine ⟨45147191299699129275922327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60196255066265505701229769 45147191299699129275922327)
        ·
          refine ⟨67720786949548693913883491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45147191299699129275922327 67720786949548693913883491)
          ·
            refine ⟨101581180424323040870825237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67720786949548693913883491 101581180424323040870825237)
            ·
              refine ⟨4761617832390142540819933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101581180424323040870825237 4761617832390142540819933)
              ·
                refine ⟨1785606687146303452807475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4761617832390142540819933 1785606687146303452807475)
                ·
                  refine ⟨2678410030719455179211213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785606687146303452807475 2678410030719455179211213)
                  ·
                    refine ⟨1004403761519795692204205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678410030719455179211213 1004403761519795692204205)
                    ·
                      rfl

theorem cell22_2934104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_2934104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934104 prefixEnd_2934104 := by exact prefixLift 2934104
  have htrace : WordTrace (prefixWord ++ tailWord_2934104) baseStart_2934104 baseEnd_2934104 := by
    simpa [prefixWord, tailWord_2934104, baseEnd_2934104] using wordTrace_append hprefix tailTrace_2934104
  have hstable : (prefixWord ++ tailWord_2934104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934104).length < 2 ^ (prefixWord ++ tailWord_2934104).sum := by decide
  have hdescent : baseEnd_2934104 < baseStart_2934104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934115 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 2, 5]
def baseStart_2934115 : Nat := 118140960795 + 2934115 * 2 ^ 59
def prefixEnd_2934115 : Nat := 4983230072969 + 3 ^ 40 * 2934115 * 2
def baseEnd_2934115 : Nat := 1004407527044595330179171

theorem tailTrace_2934115 : CollatzResearch.WordTrace tailWord_2934115 prefixEnd_2934115 1004407527044595330179171 := by
  unfold tailWord_2934115
  simp only [CollatzResearch.WordTrace]
  refine ⟨107015965765209936791947799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71343977176806624527965199 107015965765209936791947799)
  ·
    refine ⟨160523948647814905187921699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107015965765209936791947799 160523948647814905187921699)
    ·
      refine ⟨240785922971722357781882549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160523948647814905187921699 240785922971722357781882549)
      ·
        refine ⟨22573680278598971042051489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240785922971722357781882549 22573680278598971042051489)
        ·
          refine ⟨16930260208949228281538617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22573680278598971042051489 16930260208949228281538617)
          ·
            refine ⟨12697695156711921211153963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16930260208949228281538617 12697695156711921211153963)
            ·
              refine ⟨19046542735067881816730945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12697695156711921211153963 19046542735067881816730945)
              ·
                refine ⟨14284907051300911362548209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19046542735067881816730945 14284907051300911362548209)
                ·
                  refine ⟨10713680288475683521911157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14284907051300911362548209 10713680288475683521911157)
                  ·
                    refine ⟨1004407527044595330179171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10713680288475683521911157 1004407527044595330179171)
                    ·
                      rfl

theorem cell22_2934115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_2934115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934115 prefixEnd_2934115 := by exact prefixLift 2934115
  have htrace : WordTrace (prefixWord ++ tailWord_2934115) baseStart_2934115 baseEnd_2934115 := by
    simpa [prefixWord, tailWord_2934115, baseEnd_2934115] using wordTrace_append hprefix tailTrace_2934115
  have hstable : (prefixWord ++ tailWord_2934115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934115).length < 2 ^ (prefixWord ++ tailWord_2934115).sum := by decide
  have hdescent : baseEnd_2934115 < baseStart_2934115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934147 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 1, 4]
def baseStart_2934147 : Nat := 118140960795 + 2934147 * 2 ^ 59
def prefixEnd_2934147 : Nat := 4983230072969 + 3 ^ 40 * 2934147 * 2
def baseEnd_2934147 : Nat := 1004418481298557913379073

theorem tailTrace_2934147 : CollatzResearch.WordTrace tailWord_2934147 prefixEnd_2934147 1004418481298557913379073 := by
  unfold tailWord_2934147
  simp only [CollatzResearch.WordTrace]
  refine ⟨107017132901094006257112695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71344755267396004171408463 107017132901094006257112695)
  ·
    refine ⟨160525699351641009385669043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107017132901094006257112695 160525699351641009385669043)
    ·
      refine ⟨240788549027461514078503565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160525699351641009385669043 240788549027461514078503565)
      ·
        refine ⟨90295705885298067779438837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240788549027461514078503565 90295705885298067779438837)
        ·
          refine ⟨8465222426746693854322391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90295705885298067779438837 8465222426746693854322391)
          ·
            refine ⟨12697833640120040781483587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8465222426746693854322391 12697833640120040781483587)
            ·
              refine ⟨19046750460180061172225381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12697833640120040781483587 19046750460180061172225381)
              ·
                refine ⟨3571265711283761469792259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19046750460180061172225381 3571265711283761469792259)
                ·
                  refine ⟨5356898566925642204688389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571265711283761469792259 5356898566925642204688389)
                  ·
                    refine ⟨1004418481298557913379073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5356898566925642204688389 1004418481298557913379073)
                    ·
                      rfl

theorem cell22_2934147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 4].length) (baseStart_2934147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934147 prefixEnd_2934147 := by exact prefixLift 2934147
  have htrace : WordTrace (prefixWord ++ tailWord_2934147) baseStart_2934147 baseEnd_2934147 := by
    simpa [prefixWord, tailWord_2934147, baseEnd_2934147] using wordTrace_append hprefix tailTrace_2934147
  have hstable : (prefixWord ++ tailWord_2934147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934147).length < 2 ^ (prefixWord ++ tailWord_2934147).sum := by decide
  have hdescent : baseEnd_2934147 < baseStart_2934147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934164 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2934164 : Nat := 118140960795 + 2934164 * 2 ^ 59
def prefixEnd_2934164 : Nat := 4983230072969 + 3 ^ 40 * 2934164 * 2
def baseEnd_2934164 : Nat := 1004424300745975535704021

theorem tailTrace_2934164 : CollatzResearch.WordTrace tailWord_2934164 prefixEnd_2934164 1004424300745975535704021 := by
  unfold tailWord_2934164
  simp only [CollatzResearch.WordTrace]
  refine ⟨53508876471016209080240773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71345168628021612106987697 53508876471016209080240773)
  ·
    refine ⟨10032914338315539202545145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53508876471016209080240773 10032914338315539202545145)
    ·
      refine ⟨7524685753736654401908859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10032914338315539202545145 7524685753736654401908859)
      ·
        refine ⟨11287028630604981602863289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7524685753736654401908859 11287028630604981602863289)
        ·
          refine ⟨8465271472953736202147467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11287028630604981602863289 8465271472953736202147467)
          ·
            refine ⟨12697907209430604303221201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8465271472953736202147467 12697907209430604303221201)
            ·
              refine ⟨9523430407072953227415901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12697907209430604303221201 9523430407072953227415901)
              ·
                refine ⟨3571286402652357460280963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9523430407072953227415901 3571286402652357460280963)
                ·
                  refine ⟨5356929603978536190421445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571286402652357460280963 5356929603978536190421445)
                  ·
                    refine ⟨1004424300745975535704021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5356929603978536190421445 1004424300745975535704021)
                    ·
                      rfl

theorem cell22_2934164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2934164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934164 prefixEnd_2934164 := by exact prefixLift 2934164
  have htrace : WordTrace (prefixWord ++ tailWord_2934164) baseStart_2934164 baseEnd_2934164 := by
    simpa [prefixWord, tailWord_2934164, baseEnd_2934164] using wordTrace_append hprefix tailTrace_2934164
  have hstable : (prefixWord ++ tailWord_2934164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934164).length < 2 ^ (prefixWord ++ tailWord_2934164).sum := by decide
  have hdescent : baseEnd_2934164 < baseStart_2934164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934179 : List Nat := [1, 1, 1, 4, 1, 3, 5, 2, 4]
def baseStart_2934179 : Nat := 118140960795 + 2934179 * 2 ^ 59
def prefixEnd_2934179 : Nat := 4983230072969 + 3 ^ 40 * 2934179 * 2
def baseEnd_2934179 : Nat := 334809811850840165526325

theorem tailTrace_2934179 : CollatzResearch.WordTrace tailWord_2934179 prefixEnd_2934179 334809811850840165526325 := by
  unfold tailWord_2934179
  simp only [CollatzResearch.WordTrace]
  refine ⟨107018300036978075722277591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71345533357985383814851727 107018300036978075722277591)
  ·
    refine ⟨160527450055467113583416387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107018300036978075722277591 160527450055467113583416387)
    ·
      refine ⟨240791175083200670375124581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160527450055467113583416387 240791175083200670375124581)
      ·
        refine ⟨45148345328100125695335859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240791175083200670375124581 45148345328100125695335859)
        ·
          refine ⟨67722517992150188543003789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45148345328100125695335859 67722517992150188543003789)
          ·
            refine ⟨25395944247056320703626421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67722517992150188543003789 25395944247056320703626421)
            ·
              refine ⟨2380869773161530065964977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25395944247056320703626421 2380869773161530065964977)
              ·
                refine ⟨1785652329871147549473733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2380869773161530065964977 1785652329871147549473733)
                ·
                  refine ⟨334809811850840165526325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785652329871147549473733 334809811850840165526325)
                  ·
                    rfl

theorem cell22_2934179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 4].length) (baseStart_2934179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934179 prefixEnd_2934179 := by exact prefixLift 2934179
  have htrace : WordTrace (prefixWord ++ tailWord_2934179) baseStart_2934179 baseEnd_2934179 := by
    simpa [prefixWord, tailWord_2934179, baseEnd_2934179] using wordTrace_append hprefix tailTrace_2934179
  have hstable : (prefixWord ++ tailWord_2934179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934179).length < 2 ^ (prefixWord ++ tailWord_2934179).sum := by decide
  have hdescent : baseEnd_2934179 < baseStart_2934179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934237 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2934237 : Nat := 118140960795 + 2934237 * 2 ^ 59
def prefixEnd_2934237 : Nat := 4983230072969 + 3 ^ 40 * 2934237 * 2
def baseEnd_2934237 : Nat := 1004449290137827678628797

theorem tailTrace_2934237 : CollatzResearch.WordTrace tailWord_2934237 prefixEnd_2934237 1004449290137827678628797 := by
  unfold tailWord_2934237
  simp only [CollatzResearch.WordTrace]
  refine ⟨107020415470767951627888965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71346943647178634418592643 107020415470767951627888965)
  ·
    refine ⟨20066327900768990930229181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107020415470767951627888965 20066327900768990930229181)
    ·
      refine ⟨7524872962788371598835943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20066327900768990930229181 7524872962788371598835943)
      ·
        refine ⟨11287309444182557398253915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7524872962788371598835943 11287309444182557398253915)
        ·
          refine ⟨16930964166273836097380873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11287309444182557398253915 16930964166273836097380873)
          ·
            refine ⟨12698223124705377073035655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16930964166273836097380873 12698223124705377073035655)
            ·
              refine ⟨19047334687058065609553483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12698223124705377073035655 19047334687058065609553483)
              ·
                refine ⟨28571002030587098414330225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19047334687058065609553483 28571002030587098414330225)
                ·
                  refine ⟨21428251522940323810747669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28571002030587098414330225 21428251522940323810747669)
                  ·
                    refine ⟨1004449290137827678628797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21428251522940323810747669 1004449290137827678628797)
                    ·
                      rfl

theorem cell22_2934237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2934237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934237 prefixEnd_2934237 := by exact prefixLift 2934237
  have htrace : WordTrace (prefixWord ++ tailWord_2934237) baseStart_2934237 baseEnd_2934237 := by
    simpa [prefixWord, tailWord_2934237, baseEnd_2934237] using wordTrace_append hprefix tailTrace_2934237
  have hstable : (prefixWord ++ tailWord_2934237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934237).length < 2 ^ (prefixWord ++ tailWord_2934237).sum := by decide
  have hdescent : baseEnd_2934237 < baseStart_2934237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934273 : List Nat := [1, 2, 4, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2934273 : Nat := 118140960795 + 2934273 * 2 ^ 59
def prefixEnd_2934273 : Nat := 4983230072969 + 3 ^ 40 * 2934273 * 2
def baseEnd_2934273 : Nat := 1004461613673535584728687

theorem tailTrace_2934273 : CollatzResearch.WordTrace tailWord_2934273 prefixEnd_2934273 1004461613673535584728687 := by
  unfold tailWord_2934273
  simp only [CollatzResearch.WordTrace]
  refine ⟨107021728498637529776199473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71347818999091686517466315 107021728498637529776199473)
  ·
    refine ⟨80266296373978147332149605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107021728498637529776199473 80266296373978147332149605)
    ·
      refine ⟨15049930570120902624778051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80266296373978147332149605 15049930570120902624778051)
      ·
        refine ⟨22574895855181353937167077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15049930570120902624778051 22574895855181353937167077)
        ·
          refine ⟨4232792972846503863218827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22574895855181353937167077 4232792972846503863218827)
          ·
            refine ⟨6349189459269755794828241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232792972846503863218827 6349189459269755794828241)
            ·
              refine ⟨4761892094452316846121181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6349189459269755794828241 4761892094452316846121181)
              ·
                refine ⟨1785709535419618817295443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4761892094452316846121181 1785709535419618817295443)
                ·
                  refine ⟨2678564303129428225943165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785709535419618817295443 2678564303129428225943165)
                  ·
                    refine ⟨1004461613673535584728687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678564303129428225943165 1004461613673535584728687)
                    ·
                      rfl

theorem cell22_2934273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2934273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934273 prefixEnd_2934273 := by exact prefixLift 2934273
  have htrace : WordTrace (prefixWord ++ tailWord_2934273) baseStart_2934273 baseEnd_2934273 := by
    simpa [prefixWord, tailWord_2934273, baseEnd_2934273] using wordTrace_append hprefix tailTrace_2934273
  have hstable : (prefixWord ++ tailWord_2934273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934273).length < 2 ^ (prefixWord ++ tailWord_2934273).sum := by decide
  have hdescent : baseEnd_2934273 < baseStart_2934273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934286 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_2934286 : Nat := 118140960795 + 2934286 * 2 ^ 59
def prefixEnd_2934286 : Nat := 4983230072969 + 3 ^ 40 * 2934286 * 2
def baseEnd_2934286 : Nat := 334822021279735961384549

theorem tailTrace_2934286 : CollatzResearch.WordTrace tailWord_2934286 prefixEnd_2934286 334822021279735961384549 := by
  unfold tailWord_2934286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13377775330948804124552839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71348135098393621997615141 13377775330948804124552839)
  ·
    refine ⟨20066662996423206186829259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13377775330948804124552839 20066662996423206186829259)
    ·
      refine ⟨30099994494634809280243889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20066662996423206186829259 30099994494634809280243889)
      ·
        refine ⟨22574995870976106960182917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30099994494634809280243889 22574995870976106960182917)
        ·
          refine ⟨4232811725808020055034297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22574995870976106960182917 4232811725808020055034297)
          ·
            refine ⟨3174608794356015041275723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4232811725808020055034297 3174608794356015041275723)
            ·
              refine ⟨4761913191534022561913585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174608794356015041275723 4761913191534022561913585)
              ·
                refine ⟨3571434893650516921435189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761913191534022561913585 3571434893650516921435189)
                ·
                  refine ⟨334822021279735961384549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3571434893650516921435189 334822021279735961384549)
                  ·
                    rfl

theorem cell22_2934286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_2934286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934286 prefixEnd_2934286 := by exact prefixLift 2934286
  have htrace : WordTrace (prefixWord ++ tailWord_2934286) baseStart_2934286 baseEnd_2934286 := by
    simpa [prefixWord, tailWord_2934286, baseEnd_2934286] using wordTrace_append hprefix tailTrace_2934286
  have hstable : (prefixWord ++ tailWord_2934286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934286).length < 2 ^ (prefixWord ++ tailWord_2934286).sum := by decide
  have hdescent : baseEnd_2934286 < baseStart_2934286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934327 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 1, 6]
def baseStart_2934327 : Nat := 118140960795 + 2934327 * 2 ^ 59
def prefixEnd_2934327 : Nat := 4983230072969 + 3 ^ 40 * 2934327 * 2
def baseEnd_2934327 : Nat := 1004480098977097443878521

theorem tailTrace_2934327 : CollatzResearch.WordTrace tailWord_2934327 prefixEnd_2934327 1004480098977097443878521 := by
  unfold tailWord_2934327
  simp only [CollatzResearch.WordTrace]
  refine ⟨107023698040441896998665235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71349132026961264665776823 107023698040441896998665235)
  ·
    refine ⟨160535547060662845497997853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107023698040441896998665235 160535547060662845497997853)
    ·
      refine ⟨60200830147748567061749195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160535547060662845497997853 60200830147748567061749195)
      ·
        refine ⟨90301245221622850592623793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60200830147748567061749195 90301245221622850592623793)
        ·
          refine ⟨67725933916217137944467845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90301245221622850592623793 67725933916217137944467845)
          ·
            refine ⟨12698612609290713364587721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67725933916217137944467845 12698612609290713364587721)
            ·
              refine ⟨9523959456968035023440791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12698612609290713364587721 9523959456968035023440791)
              ·
                refine ⟨14285939185452052535161187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9523959456968035023440791 14285939185452052535161187)
                ·
                  refine ⟨21428908778178078802741781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14285939185452052535161187 21428908778178078802741781)
                  ·
                    refine ⟨1004480098977097443878521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21428908778178078802741781 1004480098977097443878521)
                    ·
                      rfl

theorem cell22_2934327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_2934327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934327 prefixEnd_2934327 := by exact prefixLift 2934327
  have htrace : WordTrace (prefixWord ++ tailWord_2934327) baseStart_2934327 baseEnd_2934327 := by
    simpa [prefixWord, tailWord_2934327, baseEnd_2934327] using wordTrace_append hprefix tailTrace_2934327
  have hstable : (prefixWord ++ tailWord_2934327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934327).length < 2 ^ (prefixWord ++ tailWord_2934327).sum := by decide
  have hdescent : baseEnd_2934327 < baseStart_2934327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934329 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 4, 3]
def baseStart_2934329 : Nat := 118140960795 + 2934329 * 2 ^ 59
def prefixEnd_2934329 : Nat := 4983230072969 + 3 ^ 40 * 2934329 * 2
def baseEnd_2934329 : Nat := 1004480783617970105328515

theorem tailTrace_2934329 : CollatzResearch.WordTrace tailWord_2934329 prefixEnd_2934329 1004480783617970105328515 := by
  unfold tailWord_2934329
  simp only [CollatzResearch.WordTrace]
  refine ⟨107023770986434651340238041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71349180657623100893492027 107023770986434651340238041)
  ·
    refine ⟨80267828239825988505178531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107023770986434651340238041 80267828239825988505178531)
    ·
      refine ⟨120401742359738982757767797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80267828239825988505178531 120401742359738982757767797)
      ·
        refine ⟨11287663346225529633540731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120401742359738982757767797 11287663346225529633540731)
        ·
          refine ⟨16931495019338294450311097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11287663346225529633540731 16931495019338294450311097)
          ·
            refine ⟨12698621264503720837733323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16931495019338294450311097 12698621264503720837733323)
            ·
              refine ⟨19047931896755581256599985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12698621264503720837733323 19047931896755581256599985)
              ·
                refine ⟨14285948922566685942449989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19047931896755581256599985 14285948922566685942449989)
                ·
                  refine ⟨2678615422981253614209373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14285948922566685942449989 2678615422981253614209373)
                  ·
                    refine ⟨1004480783617970105328515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678615422981253614209373 1004480783617970105328515)
                    ·
                      rfl

theorem cell22_2934329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_2934329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934329 prefixEnd_2934329 := by exact prefixLift 2934329
  have htrace : WordTrace (prefixWord ++ tailWord_2934329) baseStart_2934329 baseEnd_2934329 := by
    simpa [prefixWord, tailWord_2934329, baseEnd_2934329] using wordTrace_append hprefix tailTrace_2934329
  have hstable : (prefixWord ++ tailWord_2934329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934329).length < 2 ^ (prefixWord ++ tailWord_2934329).sum := by decide
  have hdescent : baseEnd_2934329 < baseStart_2934329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934391 : List Nat := [1, 1, 3, 1, 1, 3, 1, 7, 1, 3]
def baseStart_2934391 : Nat := 118140960795 + 2934391 * 2 ^ 59
def prefixEnd_2934391 : Nat := 4983230072969 + 3 ^ 40 * 2934391 * 2
def baseEnd_2934391 : Nat := 1004502007485022610278325

theorem tailTrace_2934391 : CollatzResearch.WordTrace tailWord_2934391 prefixEnd_2934391 1004502007485022610278325 := by
  unfold tailWord_2934391
  simp only [CollatzResearch.WordTrace]
  refine ⟨107026032312210035928995027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71350688208140023952663351 107026032312210035928995027)
  ·
    refine ⟨160539048468315053893492541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107026032312210035928995027 160539048468315053893492541)
    ·
      refine ⟨60202143175618145210059703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160539048468315053893492541 60202143175618145210059703)
      ·
        refine ⟨90303214763427217815089555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60202143175618145210059703 90303214763427217815089555)
        ·
          refine ⟨135454822145140826722634333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90303214763427217815089555 135454822145140826722634333)
          ·
            refine ⟨50795558304427810020987875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135454822145140826722634333 50795558304427810020987875)
            ·
              refine ⟨76193337456641715031481813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50795558304427810020987875 76193337456641715031481813)
              ·
                refine ⟨1785781346640040196050355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76193337456641715031481813 1785781346640040196050355)
                ·
                  refine ⟨2678672019960060294075533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785781346640040196050355 2678672019960060294075533)
                  ·
                    refine ⟨1004502007485022610278325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678672019960060294075533 1004502007485022610278325)
                    ·
                      rfl

theorem cell22_2934391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_2934391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934391 prefixEnd_2934391 := by exact prefixLift 2934391
  have htrace : WordTrace (prefixWord ++ tailWord_2934391) baseStart_2934391 baseEnd_2934391 := by
    simpa [prefixWord, tailWord_2934391, baseEnd_2934391] using wordTrace_append hprefix tailTrace_2934391
  have hstable : (prefixWord ++ tailWord_2934391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934391).length < 2 ^ (prefixWord ++ tailWord_2934391).sum := by decide
  have hdescent : baseEnd_2934391 < baseStart_2934391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934481 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 1, 5]
def baseStart_2934481 : Nat := 118140960795 + 2934481 * 2 ^ 59
def prefixEnd_2934481 : Nat := 4983230072969 + 3 ^ 40 * 2934481 * 2
def baseEnd_2934481 : Nat := 1004532816324292375528049

theorem tailTrace_2934481 : CollatzResearch.WordTrace tailWord_2934481 prefixEnd_2934481 1004532816324292375528049 := by
  unfold tailWord_2934481
  simp only [CollatzResearch.WordTrace]
  refine ⟨107029314881883981299771297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71352876587922654199847531 107029314881883981299771297)
  ·
    refine ⟨80271986161412985974828473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107029314881883981299771297 80271986161412985974828473)
    ·
      refine ⟨60203989621059739481121355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80271986161412985974828473 60203989621059739481121355)
      ·
        refine ⟨90305984431589609221682033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60203989621059739481121355 90305984431589609221682033)
        ·
          refine ⟨67729488323692206916261525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90305984431589609221682033 67729488323692206916261525)
          ·
            refine ⟨3174819765173072199199759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67729488323692206916261525 3174819765173072199199759)
            ·
              refine ⟨4762229647759608298799639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174819765173072199199759 4762229647759608298799639)
              ·
                refine ⟨7143344471639412448199459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762229647759608298799639 7143344471639412448199459)
                ·
                  refine ⟨10715016707459118672299189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7143344471639412448199459 10715016707459118672299189)
                  ·
                    refine ⟨1004532816324292375528049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10715016707459118672299189 1004532816324292375528049)
                    ·
                      rfl

theorem cell22_2934481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_2934481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934481 prefixEnd_2934481 := by exact prefixLift 2934481
  have htrace : WordTrace (prefixWord ++ tailWord_2934481) baseStart_2934481 baseEnd_2934481 := by
    simpa [prefixWord, tailWord_2934481, baseEnd_2934481] using wordTrace_append hprefix tailTrace_2934481
  have hstable : (prefixWord ++ tailWord_2934481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934481).length < 2 ^ (prefixWord ++ tailWord_2934481).sum := by decide
  have hdescent : baseEnd_2934481 < baseStart_2934481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934524 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_2934524 : Nat := 118140960795 + 2934524 * 2 ^ 59
def prefixEnd_2934524 : Nat := 4983230072969 + 3 ^ 40 * 2934524 * 2
def baseEnd_2934524 : Nat := 1004547536103054596702917

theorem tailTrace_2934524 : CollatzResearch.WordTrace tailWord_2934524 prefixEnd_2934524 1004547536103054596702917 := by
  unfold tailWord_2934524
  simp only [CollatzResearch.WordTrace]
  refine ⟨53515441610364099821793313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71353922147152133095724417 53515441610364099821793313)
  ·
    refine ⟨40136581207773074866344985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53515441610364099821793313 40136581207773074866344985)
    ·
      refine ⟨30102435905829806149758739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40136581207773074866344985 30102435905829806149758739)
      ·
        refine ⟨45153653858744709224638109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30102435905829806149758739 45153653858744709224638109)
        ·
          refine ⟨16932620197029265959239291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45153653858744709224638109 16932620197029265959239291)
          ·
            refine ⟨25398930295543898938858937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16932620197029265959239291 25398930295543898938858937)
            ·
              refine ⟨19049197721657924204144203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25398930295543898938858937 19049197721657924204144203)
              ·
                refine ⟨28573796582486886306216305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19049197721657924204144203 28573796582486886306216305)
                ·
                  refine ⟨21430347436865164729662229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28573796582486886306216305 21430347436865164729662229)
                  ·
                    refine ⟨1004547536103054596702917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21430347436865164729662229 1004547536103054596702917)
                    ·
                      rfl

theorem cell22_2934524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_2934524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934524 prefixEnd_2934524 := by exact prefixLift 2934524
  have htrace : WordTrace (prefixWord ++ tailWord_2934524) baseStart_2934524 baseEnd_2934524 := by
    simpa [prefixWord, tailWord_2934524, baseEnd_2934524] using wordTrace_append hprefix tailTrace_2934524
  have hstable : (prefixWord ++ tailWord_2934524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934524).length < 2 ^ (prefixWord ++ tailWord_2934524).sum := by decide
  have hdescent : baseEnd_2934524 < baseStart_2934524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934569 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_2934569 : Nat := 118140960795 + 2934569 * 2 ^ 59
def prefixEnd_2934569 : Nat := 4983230072969 + 3 ^ 40 * 2934569 * 2
def baseEnd_2934569 : Nat := 1004562940522689479327779

theorem tailTrace_2934569 : CollatzResearch.WordTrace tailWord_2934569 prefixEnd_2934569 1004562940522689479327779 := by
  unfold tailWord_2934569
  simp only [CollatzResearch.WordTrace]
  refine ⟨107032524505565172328974761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71355016337043448219316507 107032524505565172328974761)
  ·
    refine ⟨80274393379173879246731071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107032524505565172328974761 80274393379173879246731071)
    ·
      refine ⟨120411590068760818870096607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80274393379173879246731071 120411590068760818870096607)
      ·
        refine ⟨180617385103141228305144911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120411590068760818870096607 180617385103141228305144911)
        ·
          refine ⟨270926077654711842457717367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180617385103141228305144911 270926077654711842457717367)
          ·
            refine ⟨406389116482067763686576051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270926077654711842457717367 406389116482067763686576051)
            ·
              refine ⟨609583674723101645529864077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406389116482067763686576051 609583674723101645529864077)
              ·
                refine ⟨228593878021163117073699029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 609583674723101645529864077 228593878021163117073699029)
                ·
                  refine ⟨5357669016121010556414821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 228593878021163117073699029 5357669016121010556414821)
                  ·
                    refine ⟨1004562940522689479327779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5357669016121010556414821 1004562940522689479327779)
                    ·
                      rfl

theorem cell22_2934569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_2934569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934569 prefixEnd_2934569 := by exact prefixLift 2934569
  have htrace : WordTrace (prefixWord ++ tailWord_2934569) baseStart_2934569 baseEnd_2934569 := by
    simpa [prefixWord, tailWord_2934569, baseEnd_2934569] using wordTrace_append hprefix tailTrace_2934569
  have hstable : (prefixWord ++ tailWord_2934569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934569).length < 2 ^ (prefixWord ++ tailWord_2934569).sum := by decide
  have hdescent : baseEnd_2934569 < baseStart_2934569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934577 : List Nat := [1, 2, 2, 3, 2, 4, 2, 2, 1, 3]
def baseStart_2934577 : Nat := 118140960795 + 2934577 * 2 ^ 59
def prefixEnd_2934577 : Nat := 4983230072969 + 3 ^ 40 * 2934577 * 2
def baseEnd_2934577 : Nat := 1004565679086180125127755

theorem tailTrace_2934577 : CollatzResearch.WordTrace tailWord_2934577 prefixEnd_2934577 1004565679086180125127755 := by
  unfold tailWord_2934577
  simp only [CollatzResearch.WordTrace]
  refine ⟨107032816289536189695265985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71355210859690793130177323 107032816289536189695265985)
  ·
    refine ⟨80274612217152142271449489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107032816289536189695265985 80274612217152142271449489)
    ·
      refine ⟨60205959162864106703587117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80274612217152142271449489 60205959162864106703587117)
      ·
        refine ⟨22577234686074040013845169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60205959162864106703587117 22577234686074040013845169)
        ·
          refine ⟨16932926014555530010383877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22577234686074040013845169 16932926014555530010383877)
          ·
            refine ⟨3174923627729161876946977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16932926014555530010383877 3174923627729161876946977)
            ·
              refine ⟨2381192720796871407710233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3174923627729161876946977 2381192720796871407710233)
              ·
                refine ⟨1785894540597653555782675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2381192720796871407710233 1785894540597653555782675)
                ·
                  refine ⟨2678841810896480333674013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785894540597653555782675 2678841810896480333674013)
                  ·
                    refine ⟨1004565679086180125127755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678841810896480333674013 1004565679086180125127755)
                    ·
                      rfl

theorem cell22_2934577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_2934577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934577 prefixEnd_2934577 := by exact prefixLift 2934577
  have htrace : WordTrace (prefixWord ++ tailWord_2934577) baseStart_2934577 baseEnd_2934577 := by
    simpa [prefixWord, tailWord_2934577, baseEnd_2934577] using wordTrace_append hprefix tailTrace_2934577
  have hstable : (prefixWord ++ tailWord_2934577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934577).length < 2 ^ (prefixWord ++ tailWord_2934577).sum := by decide
  have hdescent : baseEnd_2934577 < baseStart_2934577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934586 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_2934586 : Nat := 118140960795 + 2934586 * 2 ^ 59
def prefixEnd_2934586 : Nat := 4983230072969 + 3 ^ 40 * 2934586 * 2
def baseEnd_2934586 : Nat := 1004568759970107101652727

theorem tailTrace_2934586 : CollatzResearch.WordTrace tailWord_2934586 prefixEnd_2934586 1004568759970107101652727 := by
  unfold tailWord_2934586
  simp only [CollatzResearch.WordTrace]
  refine ⟨26758286136625896058085903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71355429697669056154895741 26758286136625896058085903)
  ·
    refine ⟨40137429204938844087128855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26758286136625896058085903 40137429204938844087128855)
    ·
      refine ⟨60206143807408266130693283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40137429204938844087128855 60206143807408266130693283)
      ·
        refine ⟨90309215711112399196039925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60206143807408266130693283 90309215711112399196039925)
        ·
          refine ⟨8466488972916787424628743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90309215711112399196039925 8466488972916787424628743)
          ·
            refine ⟨12699733459375181136943115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8466488972916787424628743 12699733459375181136943115)
            ·
              refine ⟨19049600189062771705414673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12699733459375181136943115 19049600189062771705414673)
              ·
                refine ⟨14287200141797078779061005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19049600189062771705414673 14287200141797078779061005)
                ·
                  refine ⟨5357700053173904542147877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14287200141797078779061005 5357700053173904542147877)
                  ·
                    refine ⟨1004568759970107101652727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5357700053173904542147877 1004568759970107101652727)
                    ·
                      rfl

theorem cell22_2934586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_2934586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934586 prefixEnd_2934586 := by exact prefixLift 2934586
  have htrace : WordTrace (prefixWord ++ tailWord_2934586) baseStart_2934586 baseEnd_2934586 := by
    simpa [prefixWord, tailWord_2934586, baseEnd_2934586] using wordTrace_append hprefix tailTrace_2934586
  have hstable : (prefixWord ++ tailWord_2934586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934586).length < 2 ^ (prefixWord ++ tailWord_2934586).sum := by decide
  have hdescent : baseEnd_2934586 < baseStart_2934586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934618 : List Nat := [3, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_2934618 : Nat := 118140960795 + 2934618 * 2 ^ 59
def prefixEnd_2934618 : Nat := 4983230072969 + 3 ^ 40 * 2934618 * 2
def baseEnd_2934618 : Nat := 334859904741356561617543

theorem tailTrace_2934618 : CollatzResearch.WordTrace tailWord_2934618 prefixEnd_2934618 334859904741356561617543 := by
  unfold tailWord_2934618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26758577920596913424377127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71356207788258435798339005 26758577920596913424377127)
  ·
    refine ⟨40137866880895370136565691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26758577920596913424377127 40137866880895370136565691)
    ·
      refine ⟨60206800321343055204848537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40137866880895370136565691 60206800321343055204848537)
      ·
        refine ⟨45155100241007291403636403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60206800321343055204848537 45155100241007291403636403)
        ·
          refine ⟨67732650361510937105454605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45155100241007291403636403 67732650361510937105454605)
          ·
            refine ⟨25399743885566601414545477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67732650361510937105454605 25399743885566601414545477)
            ·
              refine ⟨4762451978543737765227277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25399743885566601414545477 4762451978543737765227277)
              ·
                refine ⟨1785919491953901661960229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4762451978543737765227277 1785919491953901661960229)
                ·
                  refine ⟨334859904741356561617543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785919491953901661960229 334859904741356561617543)
                  ·
                    rfl

theorem cell22_2934618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_2934618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934618 prefixEnd_2934618 := by exact prefixLift 2934618
  have htrace : WordTrace (prefixWord ++ tailWord_2934618) baseStart_2934618 baseEnd_2934618 := by
    simpa [prefixWord, tailWord_2934618, baseEnd_2934618] using wordTrace_append hprefix tailTrace_2934618
  have hstable : (prefixWord ++ tailWord_2934618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934618).length < 2 ^ (prefixWord ++ tailWord_2934618).sum := by decide
  have hdescent : baseEnd_2934618 < baseStart_2934618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934620 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2934620 : Nat := 118140960795 + 2934620 * 2 ^ 59
def prefixEnd_2934620 : Nat := 4983230072969 + 3 ^ 40 * 2934620 * 2
def baseEnd_2934620 : Nat := 1004580398864942346302623

theorem tailTrace_2934620 : CollatzResearch.WordTrace tailWord_2934620 prefixEnd_2934620 1004580398864942346302623 := by
  unfold tailWord_2934620
  simp only [CollatzResearch.WordTrace]
  refine ⟨53517192314190204019540657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71356256418920272026054209 53517192314190204019540657)
  ·
    refine ⟨40137894235642653014655493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53517192314190204019540657 40137894235642653014655493)
    ·
      refine ⟨7525855169182997440247905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40137894235642653014655493 7525855169182997440247905)
      ·
        refine ⟨5644391376887248080185929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7525855169182997440247905 5644391376887248080185929)
        ·
          refine ⟨4233293532665436060139447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5644391376887248080185929 4233293532665436060139447)
          ·
            refine ⟨6349940298998154090209171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233293532665436060139447 6349940298998154090209171)
            ·
              refine ⟨9524910448497231135313757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349940298998154090209171 9524910448497231135313757)
              ·
                refine ⟨3571841418186461675742659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9524910448497231135313757 3571841418186461675742659)
                ·
                  refine ⟨5357762127279692513613989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571841418186461675742659 5357762127279692513613989)
                  ·
                    refine ⟨1004580398864942346302623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5357762127279692513613989 1004580398864942346302623)
                    ·
                      rfl

theorem cell22_2934620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2934620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934620 prefixEnd_2934620 := by exact prefixLift 2934620
  have htrace : WordTrace (prefixWord ++ tailWord_2934620) baseStart_2934620 baseEnd_2934620 := by
    simpa [prefixWord, tailWord_2934620, baseEnd_2934620] using wordTrace_append hprefix tailTrace_2934620
  have hstable : (prefixWord ++ tailWord_2934620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934620).length < 2 ^ (prefixWord ++ tailWord_2934620).sum := by decide
  have hdescent : baseEnd_2934620 < baseStart_2934620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934631 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2934631 : Nat := 118140960795 + 2934631 * 2 ^ 59
def prefixEnd_2934631 : Nat := 4983230072969 + 3 ^ 40 * 2934631 * 2
def baseEnd_2934631 : Nat := 1004584164389741984277589

theorem tailTrace_2934631 : CollatzResearch.WordTrace tailWord_2934631 prefixEnd_2934631 1004584164389741984277589 := by
  unfold tailWord_2934631
  simp only [CollatzResearch.WordTrace]
  refine ⟨107034785831340556917731747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71356523887560371278487831 107034785831340556917731747)
  ·
    refine ⟨160552178747010835376597621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107034785831340556917731747 160552178747010835376597621)
    ·
      refine ⟨15051766757532265816556027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160552178747010835376597621 15051766757532265816556027)
      ·
        refine ⟨22577650136298398724834041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15051766757532265816556027 22577650136298398724834041)
        ·
          refine ⟨16933237602223799043625531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22577650136298398724834041 16933237602223799043625531)
          ·
            refine ⟨25399856403335698565438297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16933237602223799043625531 25399856403335698565438297)
            ·
              refine ⟨19049892302501773924078723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25399856403335698565438297 19049892302501773924078723)
              ·
                refine ⟨28574838453752660886118085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19049892302501773924078723 28574838453752660886118085)
                ·
                  refine ⟨5357782210078623916147141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28574838453752660886118085 5357782210078623916147141)
                  ·
                    refine ⟨1004584164389741984277589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5357782210078623916147141 1004584164389741984277589)
                    ·
                      rfl

theorem cell22_2934631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2934631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934631 prefixEnd_2934631 := by exact prefixLift 2934631
  have htrace : WordTrace (prefixWord ++ tailWord_2934631) baseStart_2934631 baseEnd_2934631 := by
    simpa [prefixWord, tailWord_2934631, baseEnd_2934631] using wordTrace_append hprefix tailTrace_2934631
  have hstable : (prefixWord ++ tailWord_2934631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934631).length < 2 ^ (prefixWord ++ tailWord_2934631).sum := by decide
  have hdescent : baseEnd_2934631 < baseStart_2934631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934680 : List Nat := [2, 1, 2, 6, 2, 1, 8]
def baseStart_2934680 : Nat := 118140960795 + 2934680 * 2 ^ 59
def prefixEnd_2934680 : Nat := 4983230072969 + 3 ^ 40 * 2934680 * 2
def baseEnd_2934680 : Nat := 37207442151523044066757

theorem tailTrace_2934680 : CollatzResearch.WordTrace tailWord_2934680 prefixEnd_2934680 37207442151523044066757 := by
  unfold tailWord_2934680
  simp only [CollatzResearch.WordTrace]
  refine ⟨53518286504081519143132747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71357715338775358857510329 53518286504081519143132747)
  ·
    refine ⟨80277429756122278714699121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53518286504081519143132747 80277429756122278714699121)
    ·
      refine ⟨60208072317091709036024341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80277429756122278714699121 60208072317091709036024341)
      ·
        refine ⟨2822253389863673861063641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60208072317091709036024341 2822253389863673861063641)
        ·
          refine ⟨2116690042397755395797731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2822253389863673861063641 2116690042397755395797731)
          ·
            refine ⟨3175035063596633093696597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116690042397755395797731 3175035063596633093696597)
            ·
              refine ⟨37207442151523044066757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3175035063596633093696597 37207442151523044066757)
              ·
                rfl

theorem cell22_2934680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 8].length) (baseStart_2934680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934680 prefixEnd_2934680 := by exact prefixLift 2934680
  have htrace : WordTrace (prefixWord ++ tailWord_2934680) baseStart_2934680 baseEnd_2934680 := by
    simpa [prefixWord, tailWord_2934680, baseEnd_2934680] using wordTrace_append hprefix tailTrace_2934680
  have hstable : (prefixWord ++ tailWord_2934680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934680).length < 2 ^ (prefixWord ++ tailWord_2934680).sum := by decide
  have hdescent : baseEnd_2934680 < baseStart_2934680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934691 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 5]
def baseStart_2934691 : Nat := 118140960795 + 2934691 * 2 ^ 59
def prefixEnd_2934691 : Nat := 4983230072969 + 3 ^ 40 * 2934691 * 2
def baseEnd_2934691 : Nat := 334868234538640609259135

theorem tailTrace_2934691 : CollatzResearch.WordTrace tailWord_2934691 prefixEnd_2934691 334868234538640609259135 := by
  unfold tailWord_2934691
  simp only [CollatzResearch.WordTrace]
  refine ⟨107036974211123187164915927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71357982807415458109943951 107036974211123187164915927)
  ·
    refine ⟨160555461316684780747373891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107036974211123187164915927 160555461316684780747373891)
    ·
      refine ⟨240833191975027171121060837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160555461316684780747373891 240833191975027171121060837)
      ·
        refine ⟨45156223495317594585198907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240833191975027171121060837 45156223495317594585198907)
        ·
          refine ⟨67734335242976391877798361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45156223495317594585198907 67734335242976391877798361)
          ·
            refine ⟨50800751432232293908348771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67734335242976391877798361 50800751432232293908348771)
            ·
              refine ⟨76201127148348440862523157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50800751432232293908348771 76201127148348440862523157)
              ·
                refine ⟨3571927835078833165430773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76201127148348440862523157 3571927835078833165430773)
                ·
                  refine ⟨334868234538640609259135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3571927835078833165430773 334868234538640609259135)
                  ·
                    rfl

theorem cell22_2934691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 5].length) (baseStart_2934691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934691 prefixEnd_2934691 := by exact prefixLift 2934691
  have htrace : WordTrace (prefixWord ++ tailWord_2934691) baseStart_2934691 baseEnd_2934691 := by
    simpa [prefixWord, tailWord_2934691, baseEnd_2934691] using wordTrace_append hprefix tailTrace_2934691
  have hstable : (prefixWord ++ tailWord_2934691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934691).length < 2 ^ (prefixWord ++ tailWord_2934691).sum := by decide
  have hdescent : baseEnd_2934691 < baseStart_2934691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934695 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2934695 : Nat := 118140960795 + 2934695 * 2 ^ 59
def prefixEnd_2934695 : Nat := 4983230072969 + 3 ^ 40 * 2934695 * 2
def baseEnd_2934695 : Nat := 1004606072897667150677393

theorem tailTrace_2934695 : CollatzResearch.WordTrace tailWord_2934695 prefixEnd_2934695 1004606072897667150677393 := by
  unfold tailWord_2934695
  simp only [CollatzResearch.WordTrace]
  refine ⟨107037120103108695848061539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71358080068739130565374359 107037120103108695848061539)
  ·
    refine ⟨160555680154663043772092309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107037120103108695848061539 160555680154663043772092309)
    ·
      refine ⟨7526047507249830176816827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 160555680154663043772092309 7526047507249830176816827)
      ·
        refine ⟨11289071260874745265225241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7526047507249830176816827 11289071260874745265225241)
        ·
          refine ⟨8466803445656058948918931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11289071260874745265225241 8466803445656058948918931)
          ·
            refine ⟨12700205168484088423378397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8466803445656058948918931 12700205168484088423378397)
            ·
              refine ⟨4762576938181533158766899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12700205168484088423378397 4762576938181533158766899)
              ·
                refine ⟨7143865407272299738150349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762576938181533158766899 7143865407272299738150349)
                ·
                  refine ⟨2678949527727112401806381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7143865407272299738150349 2678949527727112401806381)
                  ·
                    refine ⟨1004606072897667150677393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678949527727112401806381 1004606072897667150677393)
                    ·
                      rfl

theorem cell22_2934695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2934695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934695 prefixEnd_2934695 := by exact prefixLift 2934695
  have htrace : WordTrace (prefixWord ++ tailWord_2934695) baseStart_2934695 baseEnd_2934695 := by
    simpa [prefixWord, tailWord_2934695, baseEnd_2934695] using wordTrace_append hprefix tailTrace_2934695
  have hstable : (prefixWord ++ tailWord_2934695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934695).length < 2 ^ (prefixWord ++ tailWord_2934695).sum := by decide
  have hdescent : baseEnd_2934695 < baseStart_2934695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934706 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_2934706 : Nat := 118140960795 + 2934706 * 2 ^ 59
def prefixEnd_2934706 : Nat := 4983230072969 + 3 ^ 40 * 2934706 * 2
def baseEnd_2934706 : Nat := 1004609838422466788652359

theorem tailTrace_2934706 : CollatzResearch.WordTrace tailWord_2934706 prefixEnd_2934706 1004609838422466788652359 := by
  unfold tailWord_2934706
  simp only [CollatzResearch.WordTrace]
  refine ⟨26759380326517211181677993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71358347537379229817807981 26759380326517211181677993)
  ·
    refine ⟨20069535244887908386258495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26759380326517211181677993 20069535244887908386258495)
    ·
      refine ⟨30104302867331862579387743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20069535244887908386258495 30104302867331862579387743)
      ·
        refine ⟨45156454300997793869081615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30104302867331862579387743 45156454300997793869081615)
        ·
          refine ⟨67734681451496690803622423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45156454300997793869081615 67734681451496690803622423)
          ·
            refine ⟨101602022177245036205433635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67734681451496690803622423 101602022177245036205433635)
            ·
              refine ⟨152403033265867554308150453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101602022177245036205433635 152403033265867554308150453)
              ·
                refine ⟨14287784368675083216389105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152403033265867554308150453 14287784368675083216389105)
                ·
                  refine ⟨10715838276506312412291829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14287784368675083216389105 10715838276506312412291829)
                  ·
                    refine ⟨1004609838422466788652359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10715838276506312412291829 1004609838422466788652359)
                    ·
                      rfl

theorem cell22_2934706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_2934706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934706 prefixEnd_2934706 := by exact prefixLift 2934706
  have htrace : WordTrace (prefixWord ++ tailWord_2934706) baseStart_2934706 baseEnd_2934706 := by
    simpa [prefixWord, tailWord_2934706, baseEnd_2934706] using wordTrace_append hprefix tailTrace_2934706
  have hstable : (prefixWord ++ tailWord_2934706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934706).length < 2 ^ (prefixWord ++ tailWord_2934706).sum := by decide
  have hdescent : baseEnd_2934706 < baseStart_2934706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934742 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2934742 : Nat := 118140960795 + 2934742 * 2 ^ 59
def prefixEnd_2934742 : Nat := 4983230072969 + 3 ^ 40 * 2934742 * 2
def baseEnd_2934742 : Nat := 334874053986058231584083

theorem tailTrace_2934742 : CollatzResearch.WordTrace tailWord_2934742 prefixEnd_2934742 334874053986058231584083 := by
  unfold tailWord_2934742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689927145871151429688905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71359222889292281916681653 6689927145871151429688905)
  ·
    refine ⟨5017445359403363572266679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6689927145871151429688905 5017445359403363572266679)
    ·
      refine ⟨7526168039105045358400019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5017445359403363572266679 7526168039105045358400019)
      ·
        refine ⟨11289252058657568037600029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7526168039105045358400019 11289252058657568037600029)
        ·
          refine ⟨4233469521996588014100011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11289252058657568037600029 4233469521996588014100011)
          ·
            refine ⟨6350204282994882021150017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233469521996588014100011 6350204282994882021150017)
            ·
              refine ⟨4762653212246161515862513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6350204282994882021150017 4762653212246161515862513)
              ·
                refine ⟨3571989909184621136896885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4762653212246161515862513 3571989909184621136896885)
                ·
                  refine ⟨334874053986058231584083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3571989909184621136896885 334874053986058231584083)
                  ·
                    rfl

theorem cell22_2934742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2934742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934742 prefixEnd_2934742 := by exact prefixLift 2934742
  have htrace : WordTrace (prefixWord ++ tailWord_2934742) baseStart_2934742 baseEnd_2934742 := by
    simpa [prefixWord, tailWord_2934742, baseEnd_2934742] using wordTrace_append hprefix tailTrace_2934742
  have hstable : (prefixWord ++ tailWord_2934742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934742).length < 2 ^ (prefixWord ++ tailWord_2934742).sum := by decide
  have hdescent : baseEnd_2934742 < baseStart_2934742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934746 : List Nat := [3, 1, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_2934746 : Nat := 118140960795 + 2934746 * 2 ^ 59
def prefixEnd_2934746 : Nat := 4983230072969 + 3 ^ 40 * 2934746 * 2
def baseEnd_2934746 : Nat := 1004623531239920017652237

theorem tailTrace_2934746 : CollatzResearch.WordTrace tailWord_2934746 prefixEnd_2934746 1004623531239920017652237 := by
  unfold tailWord_2934746
  simp only [CollatzResearch.WordTrace]
  refine ⟨26759745056480982889542023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71359320150615954372112061 26759745056480982889542023)
  ·
    refine ⟨40139617584721474334313035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26759745056480982889542023 40139617584721474334313035)
    ·
      refine ⟨60209426377082211501469553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40139617584721474334313035 60209426377082211501469553)
      ·
        refine ⟨45157069782811658626102165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60209426377082211501469553 45157069782811658626102165)
        ·
          refine ⟨2116737646069296498098539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45157069782811658626102165 2116737646069296498098539)
          ·
            refine ⟨3175106469103944747147809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116737646069296498098539 3175106469103944747147809)
            ·
              refine ⟨2381329851827958560360857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3175106469103944747147809 2381329851827958560360857)
              ·
                refine ⟨1785997388870968920270643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2381329851827958560360857 1785997388870968920270643)
                ·
                  refine ⟨2678996083306453380405965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785997388870968920270643 2678996083306453380405965)
                  ·
                    refine ⟨1004623531239920017652237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2678996083306453380405965 1004623531239920017652237)
                    ·
                      rfl

theorem cell22_2934746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_2934746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934746 prefixEnd_2934746 := by exact prefixLift 2934746
  have htrace : WordTrace (prefixWord ++ tailWord_2934746) baseStart_2934746 baseEnd_2934746 := by
    simpa [prefixWord, tailWord_2934746, baseEnd_2934746] using wordTrace_append hprefix tailTrace_2934746
  have hstable : (prefixWord ++ tailWord_2934746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934746).length < 2 ^ (prefixWord ++ tailWord_2934746).sum := by decide
  have hdescent : baseEnd_2934746 < baseStart_2934746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934781 : List Nat := [1, 4, 1, 1, 1, 2, 2, 10]
def baseStart_2934781 : Nat := 118140960795 + 2934781 * 2 ^ 59
def prefixEnd_2934781 : Nat := 4983230072969 + 3 ^ 40 * 2934781 * 2
def baseEnd_2934781 : Nat := 111626168050576843669681

theorem tailTrace_2934781 : CollatzResearch.WordTrace tailWord_2934781 prefixEnd_2934781 111626168050576843669681 := by
  unfold tailWord_2934781
  simp only [CollatzResearch.WordTrace]
  refine ⟨107040256780797132535692197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71360171187198088357128131 107040256780797132535692197)
  ·
    refine ⟨20070048146399462350442287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107040256780797132535692197 20070048146399462350442287)
    ·
      refine ⟨30105072219599193525663431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20070048146399462350442287 30105072219599193525663431)
      ·
        refine ⟨45157608329398790288495147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30105072219599193525663431 45157608329398790288495147)
        ·
          refine ⟨67736412494098185432742721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45157608329398790288495147 67736412494098185432742721)
          ·
            refine ⟨50802309370573639074557041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67736412494098185432742721 50802309370573639074557041)
            ·
              refine ⟨38101732027930229305917781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50802309370573639074557041 38101732027930229305917781)
              ·
                refine ⟨111626168050576843669681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38101732027930229305917781 111626168050576843669681)
                ·
                  rfl

theorem cell22_2934781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 10].length) (baseStart_2934781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934781 prefixEnd_2934781 := by exact prefixLift 2934781
  have htrace : WordTrace (prefixWord ++ tailWord_2934781) baseStart_2934781 baseEnd_2934781 := by
    simpa [prefixWord, tailWord_2934781, baseEnd_2934781] using wordTrace_append hprefix tailTrace_2934781
  have hstable : (prefixWord ++ tailWord_2934781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934781).length < 2 ^ (prefixWord ++ tailWord_2934781).sum := by decide
  have hdescent : baseEnd_2934781 < baseStart_2934781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934811 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 2, 6]
def baseStart_2934811 : Nat := 118140960795 + 2934811 * 2 ^ 59
def prefixEnd_2934811 : Nat := 4983230072969 + 3 ^ 40 * 2934811 * 2
def baseEnd_2934811 : Nat := 1004645782068281514777037

theorem tailTrace_2934811 : CollatzResearch.WordTrace tailWord_2934811 prefixEnd_2934811 1004645782068281514777037 := by
  unfold tailWord_2934811
  simp only [CollatzResearch.WordTrace]
  refine ⟨107041350970688447659284287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71360900647125631772856191 107041350970688447659284287)
  ·
    refine ⟨160562026456032671488926431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107041350970688447659284287 160562026456032671488926431)
    ·
      refine ⟨240843039684049007233389647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160562026456032671488926431 240843039684049007233389647)
      ·
        refine ⟨361264559526073510850084471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240843039684049007233389647 361264559526073510850084471)
        ·
          refine ⟨541896839289110266275126707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361264559526073510850084471 541896839289110266275126707)
          ·
            refine ⟨812845258933665399412690061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541896839289110266275126707 812845258933665399412690061)
            ·
              refine ⟨304816972100124524779758773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 812845258933665399412690061 304816972100124524779758773)
              ·
                refine ⟨28576591134386674198102385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304816972100124524779758773 28576591134386674198102385)
                ·
                  refine ⟨21432443350790005648576789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28576591134386674198102385 21432443350790005648576789)
                  ·
                    refine ⟨1004645782068281514777037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21432443350790005648576789 1004645782068281514777037)
                    ·
                      rfl

theorem cell22_2934811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_2934811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934811 prefixEnd_2934811 := by exact prefixLift 2934811
  have htrace : WordTrace (prefixWord ++ tailWord_2934811) baseStart_2934811 baseEnd_2934811 := by
    simpa [prefixWord, tailWord_2934811, baseEnd_2934811] using wordTrace_append hprefix tailTrace_2934811
  have hstable : (prefixWord ++ tailWord_2934811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934811).length < 2 ^ (prefixWord ++ tailWord_2934811).sum := by decide
  have hdescent : baseEnd_2934811 < baseStart_2934811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934847 : List Nat := [1, 1, 2, 2, 3, 1, 5, 3, 1, 3]
def baseStart_2934847 : Nat := 118140960795 + 2934847 * 2 ^ 59
def prefixEnd_2934847 : Nat := 4983230072969 + 3 ^ 40 * 2934847 * 2
def baseEnd_2934847 : Nat := 1004658105603989420876927

theorem tailTrace_2934847 : CollatzResearch.WordTrace tailWord_2934847 prefixEnd_2934847 1004658105603989420876927 := by
  unfold tailWord_2934847
  simp only [CollatzResearch.WordTrace]
  refine ⟨107042663998558025807594795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71361775999038683871729863 107042663998558025807594795)
  ·
    refine ⟨160563995997837038711392193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107042663998558025807594795 160563995997837038711392193)
    ·
      refine ⟨120422996998377779033544145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160563995997837038711392193 120422996998377779033544145)
      ·
        refine ⟨90317247748783334275158109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120422996998377779033544145 90317247748783334275158109)
        ·
          refine ⟨33868967905793750353184291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90317247748783334275158109 33868967905793750353184291)
          ·
            refine ⟨50803451858690625529776437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33868967905793750353184291 50803451858690625529776437)
            ·
              refine ⟨4762823611752246143416541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50803451858690625529776437 4762823611752246143416541)
              ·
                refine ⟨1786058854407092303781203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4762823611752246143416541 1786058854407092303781203)
                ·
                  refine ⟨2679088281610638455671805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786058854407092303781203 2679088281610638455671805)
                  ·
                    refine ⟨1004658105603989420876927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2679088281610638455671805 1004658105603989420876927)
                    ·
                      rfl

theorem cell22_2934847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 3].length) (baseStart_2934847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934847 prefixEnd_2934847 := by exact prefixLift 2934847
  have htrace : WordTrace (prefixWord ++ tailWord_2934847) baseStart_2934847 baseEnd_2934847 := by
    simpa [prefixWord, tailWord_2934847, baseEnd_2934847] using wordTrace_append hprefix tailTrace_2934847
  have hstable : (prefixWord ++ tailWord_2934847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934847).length < 2 ^ (prefixWord ++ tailWord_2934847).sum := by decide
  have hdescent : baseEnd_2934847 < baseStart_2934847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934873 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_2934873 : Nat := 118140960795 + 2934873 * 2 ^ 59
def prefixEnd_2934873 : Nat := 4983230072969 + 3 ^ 40 * 2934873 * 2
def baseEnd_2934873 : Nat := 1004667005935334019726847

theorem tailTrace_2934873 : CollatzResearch.WordTrace tailWord_2934873 prefixEnd_2934873 1004667005935334019726847 := by
  unfold tailWord_2934873
  simp only [CollatzResearch.WordTrace]
  refine ⟨107043612296463832248041273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71362408197642554832027515 107043612296463832248041273)
  ·
    refine ⟨80282709222347874186030955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107043612296463832248041273 80282709222347874186030955)
    ·
      refine ⟨120424063833521811279046433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80282709222347874186030955 120424063833521811279046433)
      ·
        refine ⟨90318047875141358459284825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120424063833521811279046433 90318047875141358459284825)
        ·
          refine ⟨67738535906356018844463619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90318047875141358459284825 67738535906356018844463619)
          ·
            refine ⟨101607803859534028266695429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67738535906356018844463619 101607803859534028266695429)
            ·
              refine ⟨19051463223662630300005393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101607803859534028266695429 19051463223662630300005393)
              ·
                refine ⟨14288597417746972725004045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19051463223662630300005393 14288597417746972725004045)
                ·
                  refine ⟨5358224031655114771876517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14288597417746972725004045 5358224031655114771876517)
                  ·
                    refine ⟨1004667005935334019726847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5358224031655114771876517 1004667005935334019726847)
                    ·
                      rfl

theorem cell22_2934873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_2934873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934873 prefixEnd_2934873 := by exact prefixLift 2934873
  have htrace : WordTrace (prefixWord ++ tailWord_2934873) baseStart_2934873 baseEnd_2934873 := by
    simpa [prefixWord, tailWord_2934873, baseEnd_2934873] using wordTrace_append hprefix tailTrace_2934873
  have hstable : (prefixWord ++ tailWord_2934873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934873).length < 2 ^ (prefixWord ++ tailWord_2934873).sum := by decide
  have hdescent : baseEnd_2934873 < baseStart_2934873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934877 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 5]
def baseStart_2934877 : Nat := 118140960795 + 2934877 * 2 ^ 59
def prefixEnd_2934877 : Nat := 4983230072969 + 3 ^ 40 * 2934877 * 2
def baseEnd_2934877 : Nat := 334889458405693114208945

theorem tailTrace_2934877 : CollatzResearch.WordTrace tailWord_2934877 prefixEnd_2934877 334889458405693114208945 := by
  unfold tailWord_2934877
  simp only [CollatzResearch.WordTrace]
  refine ⟨107043758188449340931186885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71362505458966227287457923 107043758188449340931186885)
  ·
    refine ⟨20070704660334251424597541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107043758188449340931186885 20070704660334251424597541)
    ·
      refine ⟨3763257123812672142112039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20070704660334251424597541 3763257123812672142112039)
      ·
        refine ⟨5644885685719008213168059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763257123812672142112039 5644885685719008213168059)
        ·
          refine ⟨8467328528578512319752089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5644885685719008213168059 8467328528578512319752089)
          ·
            refine ⟨6350496396433884239814067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8467328528578512319752089 6350496396433884239814067)
            ·
              refine ⟨9525744594650826359721101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6350496396433884239814067 9525744594650826359721101)
              ·
                refine ⟨3572154222994059884895413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9525744594650826359721101 3572154222994059884895413)
                ·
                  refine ⟨334889458405693114208945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3572154222994059884895413 334889458405693114208945)
                  ·
                    rfl

theorem cell22_2934877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_2934877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934877 prefixEnd_2934877 := by exact prefixLift 2934877
  have htrace : WordTrace (prefixWord ++ tailWord_2934877) baseStart_2934877 baseEnd_2934877 := by
    simpa [prefixWord, tailWord_2934877, baseEnd_2934877] using wordTrace_append hprefix tailTrace_2934877
  have hstable : (prefixWord ++ tailWord_2934877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934877).length < 2 ^ (prefixWord ++ tailWord_2934877).sum := by decide
  have hdescent : baseEnd_2934877 < baseStart_2934877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
