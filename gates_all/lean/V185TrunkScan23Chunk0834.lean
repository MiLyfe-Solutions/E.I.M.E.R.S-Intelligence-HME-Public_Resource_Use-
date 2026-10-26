import V185TrunkScan23Chunk0833

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4935135 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_4935135 : Nat := 118140960795 + 4935135 * 2 ^ 59
def prefixEnd_4935135 : Nat := 4983230072969 + 3 ^ 40 * 4935135 * 2
def baseEnd_4935135 : Nat := 2534096349826653995316233

theorem tailTrace_4935135 : CollatzResearch.WordTrace tailWord_4935135 prefixEnd_4935135 2534096349826653995316233 := by
  unfold tailWord_4935135
  simp only [CollatzResearch.WordTrace]
  refine ⟨179999160975856223800078859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119999440650570815866719239 179999160975856223800078859)
  ·
    refine ⟨269998741463784335700118289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179999160975856223800078859 269998741463784335700118289)
    ·
      refine ⟨202499056097838251775088717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269998741463784335700118289 202499056097838251775088717)
      ·
        refine ⟨75937146036689344415658269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202499056097838251775088717 75937146036689344415658269)
        ·
          refine ⟨28476429763758504155871851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75937146036689344415658269 28476429763758504155871851)
          ·
            refine ⟨42714644645637756233807777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28476429763758504155871851 42714644645637756233807777)
            ·
              refine ⟨32035983484228317175355833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42714644645637756233807777 32035983484228317175355833)
              ·
                refine ⟨24026987613171237881516875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32035983484228317175355833 24026987613171237881516875)
                ·
                  refine ⟨36040481419756856822275313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24026987613171237881516875 36040481419756856822275313)
                  ·
                    refine ⟨27030361064817642616706485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36040481419756856822275313 27030361064817642616706485)
                    ·
                      refine ⟨2534096349826653995316233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27030361064817642616706485 2534096349826653995316233)
                      ·
                        rfl

theorem cell23_4935135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_4935135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935135 prefixEnd_4935135 := by exact prefixLift 4935135
  have htrace : WordTrace (prefixWord ++ tailWord_4935135) baseStart_4935135 baseEnd_4935135 := by
    simpa [prefixWord, tailWord_4935135, baseEnd_4935135] using wordTrace_append hprefix tailTrace_4935135
  have hstable : (prefixWord ++ tailWord_4935135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935135).length < 2 ^ (prefixWord ++ tailWord_4935135).sum := by decide
  have hdescent : baseEnd_4935135 < baseStart_4935135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935146 : List Nat := [3, 1, 3, 1, 4, 1, 3, 2, 5]
def baseStart_4935146 : Nat := 118140960795 + 4935146 * 2 ^ 59
def prefixEnd_4935146 : Nat := 4983230072969 + 3 ^ 40 * 4935146 * 2
def baseEnd_4935146 : Nat := 281566888679317050253187

theorem tailTrace_4935146 : CollatzResearch.WordTrace tailWord_4935146 prefixEnd_4935146 281566888679317050253187 := by
  unfold tailWord_4935146
  simp only [CollatzResearch.WordTrace]
  refine ⟨44999890544704093169682323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119999708119210915119152861 44999890544704093169682323)
  ·
    refine ⟨67499835817056139754523485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44999890544704093169682323 67499835817056139754523485)
    ·
      refine ⟨25312438431396052407946307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67499835817056139754523485 25312438431396052407946307)
      ·
        refine ⟨37968657647094078611919461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25312438431396052407946307 37968657647094078611919461)
        ·
          refine ⟨7119123308830139739734899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37968657647094078611919461 7119123308830139739734899)
          ·
            refine ⟨10678684963245209609602349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7119123308830139739734899 10678684963245209609602349)
            ·
              refine ⟨4004506861216953603600881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10678684963245209609602349 4004506861216953603600881)
              ·
                refine ⟨3003380145912715202700661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4004506861216953603600881 3003380145912715202700661)
                ·
                  refine ⟨281566888679317050253187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3003380145912715202700661 281566888679317050253187)
                  ·
                    rfl

theorem cell23_4935146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_4935146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935146 prefixEnd_4935146 := by exact prefixLift 4935146
  have htrace : WordTrace (prefixWord ++ tailWord_4935146) baseStart_4935146 baseEnd_4935146 := by
    simpa [prefixWord, tailWord_4935146, baseEnd_4935146] using wordTrace_append hprefix tailTrace_4935146
  have hstable : (prefixWord ++ tailWord_4935146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935146).length < 2 ^ (prefixWord ++ tailWord_4935146).sum := by decide
  have hdescent : baseEnd_4935146 < baseStart_4935146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935162 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2]
def baseStart_4935162 : Nat := 118140960795 + 4935162 * 2 ^ 59
def prefixEnd_4935162 : Nat := 4983230072969 + 3 ^ 40 * 4935162 * 2
def baseEnd_4935162 : Nat := 2534110213804325389678609

theorem tailTrace_4935162 : CollatzResearch.WordTrace tailWord_4935162 prefixEnd_4935162 2534110213804325389678609 := by
  unfold tailWord_4935162
  simp only [CollatzResearch.WordTrace]
  refine ⟨45000036436689601852827935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120000097164505604940874493 45000036436689601852827935)
  ·
    refine ⟨67500054655034402779241903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45000036436689601852827935 67500054655034402779241903)
    ·
      refine ⟨101250081982551604168862855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67500054655034402779241903 101250081982551604168862855)
      ·
        refine ⟨151875122973827406253294283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101250081982551604168862855 151875122973827406253294283)
        ·
          refine ⟨227812684460741109379941425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151875122973827406253294283 227812684460741109379941425)
          ·
            refine ⟨170859513345555832034956069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227812684460741109379941425 170859513345555832034956069)
            ·
              refine ⟨32036158752291718506554263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170859513345555832034956069 32036158752291718506554263)
              ·
                refine ⟨48054238128437577759831395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32036158752291718506554263 48054238128437577759831395)
                ·
                  refine ⟨72081357192656366639747093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48054238128437577759831395 72081357192656366639747093)
                  ·
                    refine ⟨3378813618405767186238145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72081357192656366639747093 3378813618405767186238145)
                    ·
                      refine ⟨2534110213804325389678609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378813618405767186238145 2534110213804325389678609)
                      ·
                        rfl

theorem cell23_4935162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_4935162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935162 prefixEnd_4935162 := by exact prefixLift 4935162
  have htrace : WordTrace (prefixWord ++ tailWord_4935162) baseStart_4935162 baseEnd_4935162 := by
    simpa [prefixWord, tailWord_4935162, baseEnd_4935162] using wordTrace_append hprefix tailTrace_4935162
  have hstable : (prefixWord ++ tailWord_4935162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935162).length < 2 ^ (prefixWord ++ tailWord_4935162).sum := by decide
  have hdescent : baseEnd_4935162 < baseStart_4935162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935179 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 4]
def baseStart_4935179 : Nat := 118140960795 + 4935179 * 2 ^ 59
def prefixEnd_4935179 : Nat := 4983230072969 + 3 ^ 40 * 4935179 * 2
def baseEnd_4935179 : Nat := 2534118942975451823166031

theorem tailTrace_4935179 : CollatzResearch.WordTrace tailWord_4935179 prefixEnd_4935179 2534118942975451823166031 := by
  unfold tailWord_4935179
  simp only [CollatzResearch.WordTrace]
  refine ⟨180000765787696819314680591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120000510525131212876453727 180000765787696819314680591)
  ·
    refine ⟨270001148681545228972020887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180000765787696819314680591 270001148681545228972020887)
    ·
      refine ⟨405001723022317843458031331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270001148681545228972020887 405001723022317843458031331)
      ·
        refine ⟨607502584533476765187046997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405001723022317843458031331 607502584533476765187046997)
        ·
          refine ⟨7119170912501680842035707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 607502584533476765187046997 7119170912501680842035707)
          ·
            refine ⟨10678756368752521263053561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7119170912501680842035707 10678756368752521263053561)
            ·
              refine ⟨8009067276564390947290171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10678756368752521263053561 8009067276564390947290171)
              ·
                refine ⟨12013600914846586420935257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8009067276564390947290171 12013600914846586420935257)
                ·
                  refine ⟨9010200686134939815701443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12013600914846586420935257 9010200686134939815701443)
                  ·
                    refine ⟨13515301029202409723552165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9010200686134939815701443 13515301029202409723552165)
                    ·
                      refine ⟨2534118942975451823166031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13515301029202409723552165 2534118942975451823166031)
                      ·
                        rfl

theorem cell23_4935179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 4].length) (baseStart_4935179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935179 prefixEnd_4935179 := by exact prefixLift 4935179
  have htrace : WordTrace (prefixWord ++ tailWord_4935179) baseStart_4935179 baseEnd_4935179 := by
    simpa [prefixWord, tailWord_4935179, baseEnd_4935179] using wordTrace_append hprefix tailTrace_4935179
  have hstable : (prefixWord ++ tailWord_4935179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935179).length < 2 ^ (prefixWord ++ tailWord_4935179).sum := by decide
  have hdescent : baseEnd_4935179 < baseStart_4935179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935202 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 6]
def baseStart_4935202 : Nat := 118140960795 + 4935202 * 2 ^ 59
def prefixEnd_4935202 : Nat := 4983230072969 + 3 ^ 40 * 4935202 * 2
def baseEnd_4935202 : Nat := 281570083670056137019825

theorem tailTrace_4935202 : CollatzResearch.WordTrace tailWord_4935202 prefixEnd_4935202 281570083670056137019825 := by
  unfold tailWord_4935202
  simp only [CollatzResearch.WordTrace]
  refine ⟨45000401166653373560691965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120001069777742329495178573 45000401166653373560691965)
  ·
    refine ⟨16875150437495015085259487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45000401166653373560691965 16875150437495015085259487)
    ·
      refine ⟨25312725656242522627889231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16875150437495015085259487 25312725656242522627889231)
      ·
        refine ⟨37969088484363783941833847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25312725656242522627889231 37969088484363783941833847)
        ·
          refine ⟨56953632726545675912750771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37969088484363783941833847 56953632726545675912750771)
          ·
            refine ⟨85430449089818513869126157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56953632726545675912750771 85430449089818513869126157)
            ·
              refine ⟨32036418408681942700922309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85430449089818513869126157 32036418408681942700922309)
              ·
                refine ⟨6006828451627864256422933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32036418408681942700922309 6006828451627864256422933)
                ·
                  refine ⟨281570083670056137019825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6006828451627864256422933 281570083670056137019825)
                  ·
                    rfl

theorem cell23_4935202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_4935202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935202 prefixEnd_4935202 := by exact prefixLift 4935202
  have htrace : WordTrace (prefixWord ++ tailWord_4935202) baseStart_4935202 baseEnd_4935202 := by
    simpa [prefixWord, tailWord_4935202, baseEnd_4935202] using wordTrace_append hprefix tailTrace_4935202
  have hstable : (prefixWord ++ tailWord_4935202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935202).length < 2 ^ (prefixWord ++ tailWord_4935202).sum := by decide
  have hdescent : baseEnd_4935202 < baseStart_4935202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935205 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_4935205 : Nat := 118140960795 + 4935205 * 2 ^ 59
def prefixEnd_4935205 : Nat := 4983230072969 + 3 ^ 40 * 4935205 * 2
def baseEnd_4935205 : Nat := 2534132293472468721440911

theorem tailTrace_4935205 : CollatzResearch.WordTrace tailWord_4935205 prefixEnd_4935205 2534132293472468721440911 := by
  unfold tailWord_4935205
  simp only [CollatzResearch.WordTrace]
  refine ⟨180001714085602625755127069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120001142723735083836751379 180001714085602625755127069)
  ·
    refine ⟨67500642782100984658172651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180001714085602625755127069 67500642782100984658172651)
    ·
      refine ⟨101250964173151476987258977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67500642782100984658172651 101250964173151476987258977)
      ·
        refine ⟨75938223129863607740444233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101250964173151476987258977 75938223129863607740444233)
        ·
          refine ⟨56953667347397705805333175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75938223129863607740444233 56953667347397705805333175)
          ·
            refine ⟨85430501021096558707999763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56953667347397705805333175 85430501021096558707999763)
            ·
              refine ⟨128145751531644838061999645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85430501021096558707999763 128145751531644838061999645)
              ·
                refine ⟨48054656824366814273249867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128145751531644838061999645 48054656824366814273249867)
                ·
                  refine ⟨72081985236550221409874801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48054656824366814273249867 72081985236550221409874801)
                  ·
                    refine ⟨54061488927412666057406101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72081985236550221409874801 54061488927412666057406101)
                    ·
                      refine ⟨2534132293472468721440911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54061488927412666057406101 2534132293472468721440911)
                      ·
                        rfl

theorem cell23_4935205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_4935205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935205 prefixEnd_4935205 := by exact prefixLift 4935205
  have htrace : WordTrace (prefixWord ++ tailWord_4935205) baseStart_4935205 baseEnd_4935205 := by
    simpa [prefixWord, tailWord_4935205, baseEnd_4935205] using wordTrace_append hprefix tailTrace_4935205
  have hstable : (prefixWord ++ tailWord_4935205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935205).length < 2 ^ (prefixWord ++ tailWord_4935205).sum := by decide
  have hdescent : baseEnd_4935205 < baseStart_4935205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935232 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 1, 5]
def baseStart_4935232 : Nat := 118140960795 + 4935232 * 2 ^ 59
def prefixEnd_4935232 : Nat := 4983230072969 + 3 ^ 40 * 4935232 * 2
def baseEnd_4935232 : Nat := 844715385816713371934429

theorem tailTrace_4935232 : CollatzResearch.WordTrace tailWord_4935232 prefixEnd_4935232 844715385816713371934429 := by
  unfold tailWord_4935232
  simp only [CollatzResearch.WordTrace]
  refine ⟨90001349428252404683179975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120001799237669872910906633 90001349428252404683179975)
  ·
    refine ⟨135002024142378607024769963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90001349428252404683179975 135002024142378607024769963)
    ·
      refine ⟨202503036213567910537154945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135002024142378607024769963 202503036213567910537154945)
      ·
        refine ⟨151877277160175932902866209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202503036213567910537154945 151877277160175932902866209)
        ·
          refine ⟨113907957870131949677149657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151877277160175932902866209 113907957870131949677149657)
          ·
            refine ⟨85430968402598962257862243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113907957870131949677149657 85430968402598962257862243)
            ·
              refine ⟨128146452603898443386793365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85430968402598962257862243 128146452603898443386793365)
              ·
                refine ⟨6006864965807739533755939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128146452603898443386793365 6006864965807739533755939)
                ·
                  refine ⟨9010297448711609300633909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6006864965807739533755939 9010297448711609300633909)
                  ·
                    refine ⟨844715385816713371934429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9010297448711609300633909 844715385816713371934429)
                    ·
                      rfl

theorem cell23_4935232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_4935232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935232 prefixEnd_4935232 := by exact prefixLift 4935232
  have htrace : WordTrace (prefixWord ++ tailWord_4935232) baseStart_4935232 baseEnd_4935232 := by
    simpa [prefixWord, tailWord_4935232, baseEnd_4935232] using wordTrace_append hprefix tailTrace_4935232
  have hstable : (prefixWord ++ tailWord_4935232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935232).length < 2 ^ (prefixWord ++ tailWord_4935232).sum := by decide
  have hdescent : baseEnd_4935232 < baseStart_4935232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935286 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_4935286 : Nat := 118140960795 + 4935286 * 2 ^ 59
def prefixEnd_4935286 : Nat := 4983230072969 + 3 ^ 40 * 4935286 * 2
def baseEnd_4935286 : Nat := 2534173885405482904528039

theorem tailTrace_4935286 : CollatzResearch.WordTrace tailWord_4935286 prefixEnd_4935286 2534173885405482904528039 := by
  unfold tailWord_4935286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11250291774894323536801607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120003112265539451059217141 11250291774894323536801607)
  ·
    refine ⟨16875437662341485305202411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11250291774894323536801607 16875437662341485305202411)
    ·
      refine ⟨25313156493512227957803617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16875437662341485305202411 25313156493512227957803617)
      ·
        refine ⟨18984867370134170968352713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25313156493512227957803617 18984867370134170968352713)
        ·
          refine ⟨14238650527600628226264535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18984867370134170968352713 14238650527600628226264535)
          ·
            refine ⟨21357975791400942339396803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14238650527600628226264535 21357975791400942339396803)
            ·
              refine ⟨32036963687101413509095205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21357975791400942339396803 32036963687101413509095205)
              ·
                refine ⟨6006930691331515032955351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32036963687101413509095205 6006930691331515032955351)
                ·
                  refine ⟨9010396036997272549433027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6006930691331515032955351 9010396036997272549433027)
                  ·
                    refine ⟨13515594055495908824149541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9010396036997272549433027 13515594055495908824149541)
                    ·
                      refine ⟨2534173885405482904528039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13515594055495908824149541 2534173885405482904528039)
                      ·
                        rfl

theorem cell23_4935286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_4935286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935286 prefixEnd_4935286 := by exact prefixLift 4935286
  have htrace : WordTrace (prefixWord ++ tailWord_4935286) baseStart_4935286 baseEnd_4935286 := by
    simpa [prefixWord, tailWord_4935286, baseEnd_4935286] using wordTrace_append hprefix tailTrace_4935286
  have hstable : (prefixWord ++ tailWord_4935286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935286).length < 2 ^ (prefixWord ++ tailWord_4935286).sum := by decide
  have hdescent : baseEnd_4935286 < baseStart_4935286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935306 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_4935306 : Nat := 118140960795 + 4935306 * 2 ^ 59
def prefixEnd_4935306 : Nat := 4983230072969 + 3 ^ 40 * 4935306 * 2
def baseEnd_4935306 : Nat := 2534184155018572826277947

theorem tailTrace_4935306 : CollatzResearch.WordTrace tailWord_4935306 prefixEnd_4935306 2534184155018572826277947 := by
  unfold tailWord_4935306
  simp only [CollatzResearch.WordTrace]
  refine ⟨45001349464559180001138443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120003598572157813336369181 45001349464559180001138443)
  ·
    refine ⟨67502024196838770001707665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45001349464559180001138443 67502024196838770001707665)
    ·
      refine ⟨50626518147629077501280749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67502024196838770001707665 50626518147629077501280749)
      ·
        refine ⟨18984944305360904062980281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50626518147629077501280749 18984944305360904062980281)
        ·
          refine ⟨14238708229020678047235211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18984944305360904062980281 14238708229020678047235211)
          ·
            refine ⟨21358062343531017070852817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14238708229020678047235211 21358062343531017070852817)
            ·
              refine ⟨16018546757648262803139613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21358062343531017070852817 16018546757648262803139613)
              ·
                refine ⟨6006955034118098551177355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16018546757648262803139613 6006955034118098551177355)
                ·
                  refine ⟨9010432551177147826766033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6006955034118098551177355 9010432551177147826766033)
                  ·
                    refine ⟨6757824413382860870074525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9010432551177147826766033 6757824413382860870074525)
                    ·
                      refine ⟨2534184155018572826277947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6757824413382860870074525 2534184155018572826277947)
                      ·
                        rfl

theorem cell23_4935306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_4935306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935306 prefixEnd_4935306 := by exact prefixLift 4935306
  have htrace : WordTrace (prefixWord ++ tailWord_4935306) baseStart_4935306 baseEnd_4935306 := by
    simpa [prefixWord, tailWord_4935306, baseEnd_4935306] using wordTrace_append hprefix tailTrace_4935306
  have hstable : (prefixWord ++ tailWord_4935306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935306).length < 2 ^ (prefixWord ++ tailWord_4935306).sum := by decide
  have hdescent : baseEnd_4935306 < baseStart_4935306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935393 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_4935393 : Nat := 118140960795 + 4935393 * 2 ^ 59
def prefixEnd_4935393 : Nat := 4983230072969 + 3 ^ 40 * 4935393 * 2
def baseEnd_4935393 : Nat := 2534228827835513985890047

theorem tailTrace_4935393 : CollatzResearch.WordTrace tailWord_4935393 prefixEnd_4935393 2534228827835513985890047 := by
  unfold tailWord_4935393
  simp only [CollatzResearch.WordTrace]
  refine ⟨180008571008921533862970833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120005714005947689241980555 180008571008921533862970833)
  ·
    refine ⟨135006428256691150397228125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180008571008921533862970833 135006428256691150397228125)
    ·
      refine ⟨50627410596259181398960547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135006428256691150397228125 50627410596259181398960547)
      ·
        refine ⟨75941115894388772098440821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50627410596259181398960547 75941115894388772098440821)
        ·
          refine ⟨7119479615098947384228827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75941115894388772098440821 7119479615098947384228827)
          ·
            refine ⟨10679219422648421076343241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7119479615098947384228827 10679219422648421076343241)
            ·
              refine ⟨8009414566986315807257431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10679219422648421076343241 8009414566986315807257431)
              ·
                refine ⟨12014121850479473710886147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8009414566986315807257431 12014121850479473710886147)
                ·
                  refine ⟨18021182775719210566329221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12014121850479473710886147 18021182775719210566329221)
                  ·
                    refine ⟨3378971770447351981186729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18021182775719210566329221 3378971770447351981186729)
                    ·
                      refine ⟨2534228827835513985890047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378971770447351981186729 2534228827835513985890047)
                      ·
                        rfl

theorem cell23_4935393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_4935393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935393 prefixEnd_4935393 := by exact prefixLift 4935393
  have htrace : WordTrace (prefixWord ++ tailWord_4935393) baseStart_4935393 baseEnd_4935393 := by
    simpa [prefixWord, tailWord_4935393, baseEnd_4935393] using wordTrace_append hprefix tailTrace_4935393
  have hstable : (prefixWord ++ tailWord_4935393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935393).length < 2 ^ (prefixWord ++ tailWord_4935393).sum := by decide
  have hdescent : baseEnd_4935393 < baseStart_4935393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935419 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 1, 7, 2]
def baseStart_4935419 : Nat := 118140960795 + 4935419 * 2 ^ 59
def prefixEnd_4935419 : Nat := 4983230072969 + 3 ^ 40 * 4935419 * 2
def baseEnd_4935419 : Nat := 2534242178332530884164927

theorem tailTrace_4935419 : CollatzResearch.WordTrace tailWord_4935419 prefixEnd_4935419 2534242178332530884164927 := by
  unfold tailWord_4935419
  simp only [CollatzResearch.WordTrace]
  refine ⟨180009519306827340303417311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120006346204551560202278207 180009519306827340303417311)
  ·
    refine ⟨270014278960241010455125967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180009519306827340303417311 270014278960241010455125967)
    ·
      refine ⟨405021418440361515682688951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270014278960241010455125967 405021418440361515682688951)
      ·
        refine ⟨607532127660542273524033427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405021418440361515682688951 607532127660542273524033427)
        ·
          refine ⟨911298191490813410286050141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607532127660542273524033427 911298191490813410286050141)
          ·
            refine ⟨341736821809055028857268803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 911298191490813410286050141 341736821809055028857268803)
            ·
              refine ⟨512605232713582543285903205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341736821809055028857268803 512605232713582543285903205)
              ·
                refine ⟨96113481133796726866106851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 512605232713582543285903205 96113481133796726866106851)
                ·
                  refine ⟨144170221700695090299160277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96113481133796726866106851 144170221700695090299160277)
                  ·
                    refine ⟨3378989571110041178886569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 144170221700695090299160277 3378989571110041178886569)
                    ·
                      refine ⟨2534242178332530884164927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378989571110041178886569 2534242178332530884164927)
                      ·
                        rfl

theorem cell23_4935419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 7, 2].length) (baseStart_4935419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935419 prefixEnd_4935419 := by exact prefixLift 4935419
  have htrace : WordTrace (prefixWord ++ tailWord_4935419) baseStart_4935419 baseEnd_4935419 := by
    simpa [prefixWord, tailWord_4935419, baseEnd_4935419] using wordTrace_append hprefix tailTrace_4935419
  have hstable : (prefixWord ++ tailWord_4935419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935419).length < 2 ^ (prefixWord ++ tailWord_4935419).sum := by decide
  have hdescent : baseEnd_4935419 < baseStart_4935419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935426 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_4935426 : Nat := 118140960795 + 4935426 * 2 ^ 59
def prefixEnd_4935426 : Nat := 4983230072969 + 3 ^ 40 * 4935426 * 2
def baseEnd_4935426 : Nat := 2534245772697112356777395

theorem tailTrace_4935426 : CollatzResearch.WordTrace tailWord_4935426 prefixEnd_4935426 2534245772697112356777395 := by
  unfold tailWord_4935426
  simp only [CollatzResearch.WordTrace]
  refine ⟨45002443654450495124730533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120006516411867986999281421 45002443654450495124730533)
  ·
    refine ⟨8437958185209467835886975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45002443654450495124730533 8437958185209467835886975)
    ·
      refine ⟨12656937277814201753830463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8437958185209467835886975 12656937277814201753830463)
      ·
        refine ⟨18985405916721302630745695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12656937277814201753830463 18985405916721302630745695)
        ·
          refine ⟨28478108875081953946118543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18985405916721302630745695 28478108875081953946118543)
          ·
            refine ⟨42717163312622930919177815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28478108875081953946118543 42717163312622930919177815)
            ·
              refine ⟨64075744968934396378766723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42717163312622930919177815 64075744968934396378766723)
              ·
                refine ⟨96113617453401594568150085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64075744968934396378766723 96113617453401594568150085)
                ·
                  refine ⟨18021303272512798981528141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96113617453401594568150085 18021303272512798981528141)
                  ·
                    refine ⟨6757988727192299618073053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18021303272512798981528141 6757988727192299618073053)
                    ·
                      refine ⟨2534245772697112356777395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6757988727192299618073053 2534245772697112356777395)
                      ·
                        rfl

theorem cell23_4935426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_4935426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935426 prefixEnd_4935426 := by exact prefixLift 4935426
  have htrace : WordTrace (prefixWord ++ tailWord_4935426) baseStart_4935426 baseEnd_4935426 := by
    simpa [prefixWord, tailWord_4935426, baseEnd_4935426] using wordTrace_append hprefix tailTrace_4935426
  have hstable : (prefixWord ++ tailWord_4935426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935426).length < 2 ^ (prefixWord ++ tailWord_4935426).sum := by decide
  have hdescent : baseEnd_4935426 < baseStart_4935426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935444 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4935444 : Nat := 118140960795 + 4935444 * 2 ^ 59
def prefixEnd_4935444 : Nat := 4983230072969 + 3 ^ 40 * 4935444 * 2
def baseEnd_4935444 : Nat := 2534255015348893286352313

theorem tailTrace_4935444 : CollatzResearch.WordTrace tailWord_4935444 prefixEnd_4935444 2534255015348893286352313 := by
  unfold tailWord_4935444
  simp only [CollatzResearch.WordTrace]
  refine ⟨90005215565868384786538693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120006954087824513048718257 90005215565868384786538693)
  ·
    refine ⟨16875977918600322147476005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90005215565868384786538693 16875977918600322147476005)
    ·
      refine ⟨3164245859737560402651751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16875977918600322147476005 3164245859737560402651751)
      ·
        refine ⟨4746368789606340603977627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3164245859737560402651751 4746368789606340603977627)
        ·
          refine ⟨7119553184409510905966441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4746368789606340603977627 7119553184409510905966441)
          ·
            refine ⟨5339664888307133179474831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7119553184409510905966441 5339664888307133179474831)
            ·
              refine ⟨8009497332460699769212247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339664888307133179474831 8009497332460699769212247)
              ·
                refine ⟨12014245998691049653818371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8009497332460699769212247 12014245998691049653818371)
                ·
                  refine ⟨18021368998036574480727557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12014245998691049653818371 18021368998036574480727557)
                  ·
                    refine ⟨3379006687131857715136417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18021368998036574480727557 3379006687131857715136417)
                    ·
                      refine ⟨2534255015348893286352313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379006687131857715136417 2534255015348893286352313)
                      ·
                        rfl

theorem cell23_4935444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4935444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935444 prefixEnd_4935444 := by exact prefixLift 4935444
  have htrace : WordTrace (prefixWord ++ tailWord_4935444) baseStart_4935444 baseEnd_4935444 := by
    simpa [prefixWord, tailWord_4935444, baseEnd_4935444] using wordTrace_append hprefix tailTrace_4935444
  have hstable : (prefixWord ++ tailWord_4935444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935444).length < 2 ^ (prefixWord ++ tailWord_4935444).sum := by decide
  have hdescent : baseEnd_4935444 < baseStart_4935444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935506 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 6]
def baseStart_4935506 : Nat := 118140960795 + 4935506 * 2 ^ 59
def prefixEnd_4935506 : Nat := 4983230072969 + 3 ^ 40 * 4935506 * 2
def baseEnd_4935506 : Nat := 281587427905496893753003

theorem tailTrace_4935506 : CollatzResearch.WordTrace tailWord_4935506 prefixEnd_4935506 281587427905496893753003 := by
  unfold tailWord_4935506
  simp only [CollatzResearch.WordTrace]
  refine ⟨45003173114378038540458593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120008461638341436107889581 45003173114378038540458593)
  ·
    refine ⟨33752379835783528905343945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45003173114378038540458593 33752379835783528905343945)
    ·
      refine ⟨25314284876837646679007959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33752379835783528905343945 25314284876837646679007959)
      ·
        refine ⟨37971427315256470018511939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25314284876837646679007959 37971427315256470018511939)
        ·
          refine ⟨56957140972884705027767909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37971427315256470018511939 56957140972884705027767909)
          ·
            refine ⟨10679463932415882192706483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56957140972884705027767909 10679463932415882192706483)
            ·
              refine ⟨16019195898623823289059725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10679463932415882192706483 16019195898623823289059725)
              ·
                refine ⟨6007198461983933733397397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16019195898623823289059725 6007198461983933733397397)
                ·
                  refine ⟨281587427905496893753003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6007198461983933733397397 281587427905496893753003)
                  ·
                    rfl

theorem cell23_4935506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_4935506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935506 prefixEnd_4935506 := by exact prefixLift 4935506
  have htrace : WordTrace (prefixWord ++ tailWord_4935506) baseStart_4935506 baseEnd_4935506 := by
    simpa [prefixWord, tailWord_4935506, baseEnd_4935506] using wordTrace_append hprefix tailTrace_4935506
  have hstable : (prefixWord ++ tailWord_4935506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935506).length < 2 ^ (prefixWord ++ tailWord_4935506).sum := by decide
  have hdescent : baseEnd_4935506 < baseStart_4935506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935549 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_4935549 : Nat := 118140960795 + 4935549 * 2 ^ 59
def prefixEnd_4935549 : Nat := 4983230072969 + 3 ^ 40 * 4935549 * 2
def baseEnd_4935549 : Nat := 844769643605871791846443

theorem tailTrace_4935549 : CollatzResearch.WordTrace tailWord_4935549 prefixEnd_4935549 844769643605871791846443 := by
  unfold tailWord_4935549
  simp only [CollatzResearch.WordTrace]
  refine ⟨180014260796356372505649701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120009507197570915003766467 180014260796356372505649701)
  ·
    refine ⟨33752673899316819844809319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180014260796356372505649701 33752673899316819844809319)
    ·
      refine ⟨50629010848975229767213979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33752673899316819844809319 50629010848975229767213979)
      ·
        refine ⟨75943516273462844650820969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50629010848975229767213979 75943516273462844650820969)
        ·
          refine ⟨56957637205097133488115727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75943516273462844650820969 56957637205097133488115727)
          ·
            refine ⟨85436455807645700232173591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56957637205097133488115727 85436455807645700232173591)
            ·
              refine ⟨128154683711468550348260387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85436455807645700232173591 128154683711468550348260387)
              ·
                refine ⟨192232025567202825522390581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128154683711468550348260387 192232025567202825522390581)
                ·
                  refine ⟨18021752396925264892724117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192232025567202825522390581 18021752396925264892724117)
                  ·
                    refine ⟨844769643605871791846443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18021752396925264892724117 844769643605871791846443)
                    ·
                      rfl

theorem cell23_4935549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_4935549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935549 prefixEnd_4935549 := by exact prefixLift 4935549
  have htrace : WordTrace (prefixWord ++ tailWord_4935549) baseStart_4935549 baseEnd_4935549 := by
    simpa [prefixWord, tailWord_4935549, baseEnd_4935549] using wordTrace_append hprefix tailTrace_4935549
  have hstable : (prefixWord ++ tailWord_4935549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935549).length < 2 ^ (prefixWord ++ tailWord_4935549).sum := by decide
  have hdescent : baseEnd_4935549 < baseStart_4935549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935556 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_4935556 : Nat := 118140960795 + 4935556 * 2 ^ 59
def prefixEnd_4935556 : Nat := 4983230072969 + 3 ^ 40 * 4935556 * 2
def baseEnd_4935556 : Nat := 2534312525182196848151797

theorem tailTrace_4935556 : CollatzResearch.WordTrace tailWord_4935556 prefixEnd_4935556 2534312525182196848151797 := by
  unfold tailWord_4935556
  simp only [CollatzResearch.WordTrace]
  refine ⟨90007258053665506350577261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120009677404887341800769681 90007258053665506350577261)
  ·
    refine ⟨33752721770124564881466473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90007258053665506350577261 33752721770124564881466473)
    ·
      refine ⟨25314541327593423661099855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33752721770124564881466473 25314541327593423661099855)
      ·
        refine ⟨37971811991390135491649783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25314541327593423661099855 37971811991390135491649783)
        ·
          refine ⟨56957717987085203237474675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37971811991390135491649783 56957717987085203237474675)
          ·
            refine ⟨85436576980627804856212013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56957717987085203237474675 85436576980627804856212013)
            ·
              refine ⟨32038716367735426821079505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85436576980627804856212013 32038716367735426821079505)
              ·
                refine ⟨24029037275801570115809629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32038716367735426821079505 24029037275801570115809629)
                ·
                  refine ⟨9010888978425588793428611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24029037275801570115809629 9010888978425588793428611)
                  ·
                    refine ⟨13516333467638383190142917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9010888978425588793428611 13516333467638383190142917)
                    ·
                      refine ⟨2534312525182196848151797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13516333467638383190142917 2534312525182196848151797)
                      ·
                        rfl

theorem cell23_4935556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_4935556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935556 prefixEnd_4935556 := by exact prefixLift 4935556
  have htrace : WordTrace (prefixWord ++ tailWord_4935556) baseStart_4935556 baseEnd_4935556 := by
    simpa [prefixWord, tailWord_4935556, baseEnd_4935556] using wordTrace_append hprefix tailTrace_4935556
  have hstable : (prefixWord ++ tailWord_4935556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935556).length < 2 ^ (prefixWord ++ tailWord_4935556).sum := by decide
  have hdescent : baseEnd_4935556 < baseStart_4935556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935569 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_4935569 : Nat := 118140960795 + 4935569 * 2 ^ 59
def prefixEnd_4935569 : Nat := 4983230072969 + 3 ^ 40 * 4935569 * 2
def baseEnd_4935569 : Nat := 2534319200430705297289237

theorem tailTrace_4935569 : CollatzResearch.WordTrace tailWord_4935569 prefixEnd_4935569 2534319200430705297289237 := by
  unfold tailWord_4935569
  simp only [CollatzResearch.WordTrace]
  refine ⟨180014990256283915921377761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120009993504189277280918507 180014990256283915921377761)
  ·
    refine ⟨135011242692212936941033321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180014990256283915921377761 135011242692212936941033321)
    ·
      refine ⟨101258432019159702705774991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135011242692212936941033321 101258432019159702705774991)
      ·
        refine ⟨151887648028739554058662487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101258432019159702705774991 151887648028739554058662487)
        ·
          refine ⟨227831472043109331087993731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151887648028739554058662487 227831472043109331087993731)
          ·
            refine ⟨341747208064663996631990597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227831472043109331087993731 341747208064663996631990597)
            ·
              refine ⟨64077601512124499368498237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 341747208064663996631990597 64077601512124499368498237)
              ·
                refine ⟨24029100567046687263186839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64077601512124499368498237 24029100567046687263186839)
                ·
                  refine ⟨36043650850570030894780259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24029100567046687263186839 36043650850570030894780259)
                  ·
                    refine ⟨54065476275855046342170389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36043650850570030894780259 54065476275855046342170389)
                    ·
                      refine ⟨2534319200430705297289237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54065476275855046342170389 2534319200430705297289237)
                      ·
                        rfl

theorem cell23_4935569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_4935569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935569 prefixEnd_4935569 := by exact prefixLift 4935569
  have htrace : WordTrace (prefixWord ++ tailWord_4935569) baseStart_4935569 baseEnd_4935569 := by
    simpa [prefixWord, tailWord_4935569, baseEnd_4935569] using wordTrace_append hprefix tailTrace_4935569
  have hstable : (prefixWord ++ tailWord_4935569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935569).length < 2 ^ (prefixWord ++ tailWord_4935569).sum := by decide
  have hdescent : baseEnd_4935569 < baseStart_4935569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935619 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 5]
def baseStart_4935619 : Nat := 118140960795 + 4935619 * 2 ^ 59
def prefixEnd_4935619 : Nat := 4983230072969 + 3 ^ 40 * 4935619 * 2
def baseEnd_4935619 : Nat := 2534344874463430101664007

theorem tailTrace_4935619 : CollatzResearch.WordTrace tailWord_4935619 prefixEnd_4935619 2534344874463430101664007 := by
  unfold tailWord_4935619
  simp only [CollatzResearch.WordTrace]
  refine ⟨180016813906102774460697911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120011209270735182973798607 180016813906102774460697911)
  ·
    refine ⟨270025220859154161691046867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180016813906102774460697911 270025220859154161691046867)
    ·
      refine ⟨405037831288731242536570301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270025220859154161691046867 405037831288731242536570301)
      ·
        refine ⟨151889186733274215951213863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 405037831288731242536570301 151889186733274215951213863)
        ·
          refine ⟨227833780099911323926820795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151889186733274215951213863 227833780099911323926820795)
          ·
            refine ⟨341750670149866985890231193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227833780099911323926820795 341750670149866985890231193)
            ·
              refine ⟨256313002612400239417673395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341750670149866985890231193 256313002612400239417673395)
              ·
                refine ⟨384469503918600359126510093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256313002612400239417673395 384469503918600359126510093)
                ·
                  refine ⟨144176063969475134672441285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384469503918600359126510093 144176063969475134672441285)
                  ·
                    refine ⟨27033011994276587751082741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144176063969475134672441285 27033011994276587751082741)
                    ·
                      refine ⟨2534344874463430101664007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27033011994276587751082741 2534344874463430101664007)
                      ·
                        rfl

theorem cell23_4935619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_4935619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935619 prefixEnd_4935619 := by exact prefixLift 4935619
  have htrace : WordTrace (prefixWord ++ tailWord_4935619) baseStart_4935619 baseEnd_4935619 := by
    simpa [prefixWord, tailWord_4935619, baseEnd_4935619] using wordTrace_append hprefix tailTrace_4935619
  have hstable : (prefixWord ++ tailWord_4935619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935619).length < 2 ^ (prefixWord ++ tailWord_4935619).sum := by decide
  have hdescent : baseEnd_4935619 < baseStart_4935619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935636 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4935636 : Nat := 118140960795 + 4935636 * 2 ^ 59
def prefixEnd_4935636 : Nat := 4983230072969 + 3 ^ 40 * 4935636 * 2
def baseEnd_4935636 : Nat := 2534353603634556535151429

theorem tailTrace_4935636 : CollatzResearch.WordTrace tailWord_4935636 prefixEnd_4935636 2534353603634556535151429 := by
  unfold tailWord_4935636
  simp only [CollatzResearch.WordTrace]
  refine ⟨90008716973520593182033381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120011622631360790909377841 90008716973520593182033381)
  ·
    refine ⟨16876634432535111221631259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90008716973520593182033381 16876634432535111221631259)
    ·
      refine ⟨25314951648802666832446889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16876634432535111221631259 25314951648802666832446889)
      ·
        refine ⟨18986213736602000124335167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25314951648802666832446889 18986213736602000124335167)
        ·
          refine ⟨28479320604903000186502751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18986213736602000124335167 28479320604903000186502751)
          ·
            refine ⟨42718980907354500279754127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28479320604903000186502751 42718980907354500279754127)
            ·
              refine ⟨64078471361031750419631191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42718980907354500279754127 64078471361031750419631191)
              ·
                refine ⟨96117707041547625629446787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64078471361031750419631191 96117707041547625629446787)
                ·
                  refine ⟨144176560562321438444170181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96117707041547625629446787 144176560562321438444170181)
                  ·
                    refine ⟨27033105105435269708281909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144176560562321438444170181 27033105105435269708281909)
                    ·
                      refine ⟨2534353603634556535151429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27033105105435269708281909 2534353603634556535151429)
                      ·
                        rfl

theorem cell23_4935636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4935636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935636 prefixEnd_4935636 := by exact prefixLift 4935636
  have htrace : WordTrace (prefixWord ++ tailWord_4935636) baseStart_4935636 baseEnd_4935636 := by
    simpa [prefixWord, tailWord_4935636, baseEnd_4935636] using wordTrace_append hprefix tailTrace_4935636
  have hstable : (prefixWord ++ tailWord_4935636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935636).length < 2 ^ (prefixWord ++ tailWord_4935636).sum := by decide
  have hdescent : baseEnd_4935636 < baseStart_4935636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935641 : List Nat := [1, 2, 1, 2, 7, 1, 1, 3, 1, 2, 2]
def baseStart_4935641 : Nat := 118140960795 + 4935641 * 2 ^ 59
def prefixEnd_4935641 : Nat := 4983230072969 + 3 ^ 40 * 4935641 * 2
def baseEnd_4935641 : Nat := 2534356171037829015588907

theorem tailTrace_4935641 : CollatzResearch.WordTrace tailWord_4935641 prefixEnd_4935641 2534356171037829015588907 := by
  unfold tailWord_4935641
  simp only [CollatzResearch.WordTrace]
  refine ⟨180017616312023072217998777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120011744208015381478665851 180017616312023072217998777)
  ·
    refine ⟨135013212234017304163499083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180017616312023072217998777 135013212234017304163499083)
    ·
      refine ⟨202519818351025956245248625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135013212234017304163499083 202519818351025956245248625)
      ·
        refine ⟨151889863763269467183936469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202519818351025956245248625 151889863763269467183936469)
        ·
          refine ⟨3559918681951628137123511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 151889863763269467183936469 3559918681951628137123511)
          ·
            refine ⟨5339878022927442205685267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559918681951628137123511 5339878022927442205685267)
            ·
              refine ⟨8009817034391163308527901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339878022927442205685267 8009817034391163308527901)
              ·
                refine ⟨3003681387896686240697963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8009817034391163308527901 3003681387896686240697963)
                ·
                  refine ⟨4505522081845029361046945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3003681387896686240697963 4505522081845029361046945)
                  ·
                    refine ⟨3379141561383772020785209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4505522081845029361046945 3379141561383772020785209)
                    ·
                      refine ⟨2534356171037829015588907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379141561383772020785209 2534356171037829015588907)
                      ·
                        rfl

theorem cell23_4935641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_4935641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935641 prefixEnd_4935641 := by exact prefixLift 4935641
  have htrace : WordTrace (prefixWord ++ tailWord_4935641) baseStart_4935641 baseEnd_4935641 := by
    simpa [prefixWord, tailWord_4935641, baseEnd_4935641] using wordTrace_append hprefix tailTrace_4935641
  have hstable : (prefixWord ++ tailWord_4935641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935641).length < 2 ^ (prefixWord ++ tailWord_4935641).sum := by decide
  have hdescent : baseEnd_4935641 < baseStart_4935641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935676 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_4935676 : Nat := 118140960795 + 4935676 * 2 ^ 59
def prefixEnd_4935676 : Nat := 4983230072969 + 3 ^ 40 * 4935676 * 2
def baseEnd_4935676 : Nat := 2534374142860736378651245

theorem tailTrace_4935676 : CollatzResearch.WordTrace tailWord_4935676 prefixEnd_4935676 2534374142860736378651245 := by
  unfold tailWord_4935676
  simp only [CollatzResearch.WordTrace]
  refine ⟨90009446433448136597761441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120012595244597515463681921 90009446433448136597761441)
  ·
    refine ⟨67507084825086102448321081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90009446433448136597761441 67507084825086102448321081)
    ·
      refine ⟨50630313618814576836240811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67507084825086102448321081 50630313618814576836240811)
      ·
        refine ⟨75945470428221865254361217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50630313618814576836240811 75945470428221865254361217)
        ·
          refine ⟨56959102821166398940770913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75945470428221865254361217 56959102821166398940770913)
          ·
            refine ⟨42719327115874799205578185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56959102821166398940770913 42719327115874799205578185)
            ·
              refine ⟨32039495336906099404183639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42719327115874799205578185 32039495336906099404183639)
              ·
                refine ⟨48059243005359149106275459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32039495336906099404183639 48059243005359149106275459)
                ·
                  refine ⟨72088864508038723659413189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48059243005359149106275459 72088864508038723659413189)
                  ·
                    refine ⟨13516662095257260686139973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72088864508038723659413189 13516662095257260686139973)
                    ·
                      refine ⟨2534374142860736378651245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13516662095257260686139973 2534374142860736378651245)
                      ·
                        rfl

theorem cell23_4935676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_4935676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935676 prefixEnd_4935676 := by exact prefixLift 4935676
  have htrace : WordTrace (prefixWord ++ tailWord_4935676) baseStart_4935676 baseEnd_4935676 := by
    simpa [prefixWord, tailWord_4935676, baseEnd_4935676] using wordTrace_append hprefix tailTrace_4935676
  have hstable : (prefixWord ++ tailWord_4935676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935676).length < 2 ^ (prefixWord ++ tailWord_4935676).sum := by decide
  have hdescent : baseEnd_4935676 < baseStart_4935676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935696 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 3]
def baseStart_4935696 : Nat := 118140960795 + 4935696 * 2 ^ 59
def prefixEnd_4935696 : Nat := 4983230072969 + 3 ^ 40 * 4935696 * 2
def baseEnd_4935696 : Nat := 2534384412473826300401153

theorem tailTrace_4935696 : CollatzResearch.WordTrace tailWord_4935696 prefixEnd_4935696 2534384412473826300401153 := by
  unfold tailWord_4935696
  simp only [CollatzResearch.WordTrace]
  refine ⟨90009811163411908305625471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120013081551215877740833961 90009811163411908305625471)
  ·
    refine ⟨135014716745117862458438207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90009811163411908305625471 135014716745117862458438207)
    ·
      refine ⟨202522075117676793687657311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135014716745117862458438207 202522075117676793687657311)
      ·
        refine ⟨303783112676515190531485967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202522075117676793687657311 303783112676515190531485967)
        ·
          refine ⟨455674669014772785797228951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303783112676515190531485967 455674669014772785797228951)
          ·
            refine ⟨683512003522159178695843427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455674669014772785797228951 683512003522159178695843427)
            ·
              refine ⟨1025268005283238768043765141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683512003522159178695843427 1025268005283238768043765141)
              ·
                refine ⟨48059437747651817252051491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1025268005283238768043765141 48059437747651817252051491)
                ·
                  refine ⟨72089156621477725878077237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48059437747651817252051491 72089156621477725878077237)
                  ·
                    refine ⟨6758358433263536801069741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72089156621477725878077237 6758358433263536801069741)
                    ·
                      refine ⟨2534384412473826300401153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6758358433263536801069741 2534384412473826300401153)
                      ·
                        rfl

theorem cell23_4935696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_4935696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935696 prefixEnd_4935696 := by exact prefixLift 4935696
  have htrace : WordTrace (prefixWord ++ tailWord_4935696) baseStart_4935696 baseEnd_4935696 := by
    simpa [prefixWord, tailWord_4935696, baseEnd_4935696] using wordTrace_append hprefix tailTrace_4935696
  have hstable : (prefixWord ++ tailWord_4935696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935696).length < 2 ^ (prefixWord ++ tailWord_4935696).sum := by decide
  have hdescent : baseEnd_4935696 < baseStart_4935696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935750 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_4935750 : Nat := 118140960795 + 4935750 * 2 ^ 59
def prefixEnd_4935750 : Nat := 4983230072969 + 3 ^ 40 * 4935750 * 2
def baseEnd_4935750 : Nat := 844804046809723029708635

theorem tailTrace_4935750 : CollatzResearch.WordTrace tailWord_4935750 prefixEnd_4935750 844804046809723029708635 := by
  unfold tailWord_4935750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5625674745894630744803647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120014394579085455889144469 5625674745894630744803647)
  ·
    refine ⟨8438512118841946117205471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5625674745894630744803647 8438512118841946117205471)
    ·
      refine ⟨12657768178262919175808207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8438512118841946117205471 12657768178262919175808207)
      ·
        refine ⟨18986652267394378763712311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12657768178262919175808207 18986652267394378763712311)
        ·
          refine ⟨28479978401091568145568467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18986652267394378763712311 28479978401091568145568467)
          ·
            refine ⟨42719967601637352218352701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28479978401091568145568467 42719967601637352218352701)
            ·
              refine ⟨16019987850614007081882263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42719967601637352218352701 16019987850614007081882263)
              ·
                refine ⟨24029981775921010622823395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16019987850614007081882263 24029981775921010622823395)
                ·
                  refine ⟨36044972663881515934235093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24029981775921010622823395 36044972663881515934235093)
                  ·
                    refine ⟨844804046809723029708635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36044972663881515934235093 844804046809723029708635)
                    ·
                      rfl

theorem cell23_4935750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_4935750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935750 prefixEnd_4935750 := by exact prefixLift 4935750
  have htrace : WordTrace (prefixWord ++ tailWord_4935750) baseStart_4935750 baseEnd_4935750 := by
    simpa [prefixWord, tailWord_4935750, baseEnd_4935750] using wordTrace_append hprefix tailTrace_4935750
  have hstable : (prefixWord ++ tailWord_4935750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935750).length < 2 ^ (prefixWord ++ tailWord_4935750).sum := by decide
  have hdescent : baseEnd_4935750 < baseStart_4935750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935753 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 1, 6, 2]
def baseStart_4935753 : Nat := 118140960795 + 4935753 * 2 ^ 59
def prefixEnd_4935753 : Nat := 4983230072969 + 3 ^ 40 * 4935753 * 2
def baseEnd_4935753 : Nat := 2534413680871132577388391

theorem tailTrace_4935753 : CollatzResearch.WordTrace tailWord_4935753 prefixEnd_4935753 2534413680871132577388391 := by
  unfold tailWord_4935753
  simp only [CollatzResearch.WordTrace]
  refine ⟨180021701287617315346075913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120014467525078210230717275 180021701287617315346075913)
  ·
    refine ⟨135016275965712986509556935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180021701287617315346075913 135016275965712986509556935)
    ·
      refine ⟨202524413948569479764335403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135016275965712986509556935 202524413948569479764335403)
      ·
        refine ⟨303786620922854219646503105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202524413948569479764335403 303786620922854219646503105)
        ·
          refine ⟨227839965692140664734877329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303786620922854219646503105 227839965692140664734877329)
          ·
            refine ⟨170879974269105498551157997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227839965692140664734877329 170879974269105498551157997)
            ·
              refine ⟨64079990350914561956684249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170879974269105498551157997 64079990350914561956684249)
              ·
                refine ⟨48059992763185921467513187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64079990350914561956684249 48059992763185921467513187)
                ·
                  refine ⟨72089989144778882201269781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48059992763185921467513187 72089989144778882201269781)
                  ·
                    refine ⟨3379218241161510103184521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72089989144778882201269781 3379218241161510103184521)
                    ·
                      refine ⟨2534413680871132577388391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379218241161510103184521 2534413680871132577388391)
                      ·
                        rfl

theorem cell23_4935753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 6, 2].length) (baseStart_4935753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935753 prefixEnd_4935753 := by exact prefixLift 4935753
  have htrace : WordTrace (prefixWord ++ tailWord_4935753) baseStart_4935753 baseEnd_4935753 := by
    simpa [prefixWord, tailWord_4935753, baseEnd_4935753] using wordTrace_append hprefix tailTrace_4935753
  have hstable : (prefixWord ++ tailWord_4935753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935753).length < 2 ^ (prefixWord ++ tailWord_4935753).sum := by decide
  have hdescent : baseEnd_4935753 < baseStart_4935753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935837 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_4935837 : Nat := 118140960795 + 4935837 * 2 ^ 59
def prefixEnd_4935837 : Nat := 4983230072969 + 3 ^ 40 * 4935837 * 2
def baseEnd_4935837 : Nat := 2534456813246110248738005

theorem tailTrace_4935837 : CollatzResearch.WordTrace tailWord_4935837 prefixEnd_4935837 2534456813246110248738005 := by
  unfold tailWord_4935837
  simp only [CollatzResearch.WordTrace]
  refine ⟨180024765019312997692133765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120016510012875331794755843 180024765019312997692133765)
  ·
    refine ⟨33754643441121187067275081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180024765019312997692133765 33754643441121187067275081)
    ·
      refine ⟨25315982580840890300456311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33754643441121187067275081 25315982580840890300456311)
      ·
        refine ⟨37973973871261335450684467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25315982580840890300456311 37973973871261335450684467)
        ·
          refine ⟨56960960806892003176026701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37973973871261335450684467 56960960806892003176026701)
          ·
            refine ⟨21360360302584501191010013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56960960806892003176026701 21360360302584501191010013)
            ·
              refine ⟨8010135113469187946628755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21360360302584501191010013 8010135113469187946628755)
              ·
                refine ⟨12015202670203781919943133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8010135113469187946628755 12015202670203781919943133)
                ·
                  refine ⟨4505701001326418219978675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12015202670203781919943133 4505701001326418219978675)
                  ·
                    refine ⟨6758551501989627329968013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4505701001326418219978675 6758551501989627329968013)
                    ·
                      refine ⟨2534456813246110248738005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6758551501989627329968013 2534456813246110248738005)
                      ·
                        rfl

theorem cell23_4935837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_4935837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935837 prefixEnd_4935837 := by exact prefixLift 4935837
  have htrace : WordTrace (prefixWord ++ tailWord_4935837) baseStart_4935837 baseEnd_4935837 := by
    simpa [prefixWord, tailWord_4935837, baseEnd_4935837] using wordTrace_append hprefix tailTrace_4935837
  have hstable : (prefixWord ++ tailWord_4935837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935837).length < 2 ^ (prefixWord ++ tailWord_4935837).sum := by decide
  have hdescent : baseEnd_4935837 < baseStart_4935837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935844 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 6]
def baseStart_4935844 : Nat := 118140960795 + 4935844 * 2 ^ 59
def prefixEnd_4935844 : Nat := 4983230072969 + 3 ^ 40 * 4935844 * 2
def baseEnd_4935844 : Nat := 281606711956743524594497

theorem tailTrace_4935844 : CollatzResearch.WordTrace tailWord_4935844 prefixEnd_4935844 281606711956743524594497 := by
  unfold tailWord_4935844
  simp only [CollatzResearch.WordTrace]
  refine ⟨90012510165143818943819293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120016680220191758591759057 90012510165143818943819293)
  ·
    refine ⟨33754691311928932103932235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90012510165143818943819293 33754691311928932103932235)
    ·
      refine ⟨50632036967893398155898353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33754691311928932103932235 50632036967893398155898353)
      ·
        refine ⟨37974027725920048616923765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50632036967893398155898353 37974027725920048616923765)
        ·
          refine ⟨3560065099305004557836603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37974027725920048616923765 3560065099305004557836603)
          ·
            refine ⟨5340097648957506836754905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560065099305004557836603 5340097648957506836754905)
            ·
              refine ⟨4005073236718130127566179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5340097648957506836754905 4005073236718130127566179)
              ·
                refine ⟨6007609855077195191349269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4005073236718130127566179 6007609855077195191349269)
                ·
                  refine ⟨281606711956743524594497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6007609855077195191349269 281606711956743524594497)
                  ·
                    rfl

theorem cell23_4935844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_4935844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935844 prefixEnd_4935844 := by exact prefixLift 4935844
  have htrace : WordTrace (prefixWord ++ tailWord_4935844) baseStart_4935844 baseEnd_4935844 := by
    simpa [prefixWord, tailWord_4935844, baseEnd_4935844] using wordTrace_append hprefix tailTrace_4935844
  have hstable : (prefixWord ++ tailWord_4935844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935844).length < 2 ^ (prefixWord ++ tailWord_4935844).sum := by decide
  have hdescent : baseEnd_4935844 < baseStart_4935844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935917 : List Nat := [1, 5, 1, 2, 3, 1, 3, 7]
def baseStart_4935917 : Nat := 118140960795 + 4935917 * 2 ^ 59
def prefixEnd_4935917 : Nat := 4983230072969 + 3 ^ 40 * 4935917 * 2
def baseEnd_4935917 : Nat := 93870292285128516138431

theorem tailTrace_4935917 : CollatzResearch.WordTrace tailWord_4935917 prefixEnd_4935917 93870292285128516138431 := by
  unfold tailWord_4935917
  simp only [CollatzResearch.WordTrace]
  refine ⟨180027682859023171355046005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120018455239348780903364003 180027682859023171355046005)
  ·
    refine ⟨16877595268033422314535563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180027682859023171355046005 16877595268033422314535563)
    ·
      refine ⟨25316392902050133471803345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16877595268033422314535563 25316392902050133471803345)
      ·
        refine ⟨18987294676537600103852509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25316392902050133471803345 18987294676537600103852509)
        ·
          refine ⟨7120235503701600038944691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18987294676537600103852509 7120235503701600038944691)
          ·
            refine ⟨10680353255552400058417037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7120235503701600038944691 10680353255552400058417037)
            ·
              refine ⟨4005132470832150021906389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10680353255552400058417037 4005132470832150021906389)
              ·
                refine ⟨93870292285128516138431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4005132470832150021906389 93870292285128516138431)
                ·
                  rfl

theorem cell23_4935917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 7].length) (baseStart_4935917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935917 prefixEnd_4935917 := by exact prefixLift 4935917
  have htrace : WordTrace (prefixWord ++ tailWord_4935917) baseStart_4935917 baseEnd_4935917 := by
    simpa [prefixWord, tailWord_4935917, baseEnd_4935917] using wordTrace_append hprefix tailTrace_4935917
  have hstable : (prefixWord ++ tailWord_4935917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935917).length < 2 ^ (prefixWord ++ tailWord_4935917).sum := by decide
  have hdescent : baseEnd_4935917 < baseStart_4935917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935923 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 5]
def baseStart_4935923 : Nat := 118140960795 + 4935923 * 2 ^ 59
def prefixEnd_4935923 : Nat := 4983230072969 + 3 ^ 40 * 4935923 * 2
def baseEnd_4935923 : Nat := 2534500972582396912262609

theorem tailTrace_4935923 : CollatzResearch.WordTrace tailWord_4935923 prefixEnd_4935923 2534500972582396912262609 := by
  unfold tailWord_4935923
  simp only [CollatzResearch.WordTrace]
  refine ⟨180027901697001434379764423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120018601131334289586509615 180027901697001434379764423)
  ·
    refine ⟨270041852545502151569646635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180027901697001434379764423 270041852545502151569646635)
    ·
      refine ⟨405062778818253227354469953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270041852545502151569646635 405062778818253227354469953)
      ·
        refine ⟨303797084113689920515852465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405062778818253227354469953 303797084113689920515852465)
        ·
          refine ⟨227847813085267440386889349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303797084113689920515852465 227847813085267440386889349)
          ·
            refine ⟨42721464953487645072541753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227847813085267440386889349 42721464953487645072541753)
            ·
              refine ⟨32041098715115733804406315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42721464953487645072541753 32041098715115733804406315)
              ·
                refine ⟨48061648072673600706609473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32041098715115733804406315 48061648072673600706609473)
                ·
                  refine ⟨36046236054505200529957105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48061648072673600706609473 36046236054505200529957105)
                  ·
                    refine ⟨27034677040878900397467829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36046236054505200529957105 27034677040878900397467829)
                    ·
                      refine ⟨2534500972582396912262609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27034677040878900397467829 2534500972582396912262609)
                      ·
                        rfl

theorem cell23_4935923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_4935923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935923 prefixEnd_4935923 := by exact prefixLift 4935923
  have htrace : WordTrace (prefixWord ++ tailWord_4935923) baseStart_4935923 baseEnd_4935923 := by
    simpa [prefixWord, tailWord_4935923, baseEnd_4935923] using wordTrace_append hprefix tailTrace_4935923
  have hstable : (prefixWord ++ tailWord_4935923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935923).length < 2 ^ (prefixWord ++ tailWord_4935923).sum := by decide
  have hdescent : baseEnd_4935923 < baseStart_4935923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935944 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_4935944 : Nat := 118140960795 + 4935944 * 2 ^ 59
def prefixEnd_4935944 : Nat := 4983230072969 + 3 ^ 40 * 4935944 * 2
def baseEnd_4935944 : Nat := 2534511755676141330100013

theorem tailTrace_4935944 : CollatzResearch.WordTrace tailWord_4935944 prefixEnd_4935944 2534511755676141330100013 := by
  unfold tailWord_4935944
  simp only [CollatzResearch.WordTrace]
  refine ⟨90014333814962677483139443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120019111753283569977519257 90014333814962677483139443)
  ·
    refine ⟨135021500722444016224709165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90014333814962677483139443 135021500722444016224709165)
    ·
      refine ⟨50633062770916506084265937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135021500722444016224709165 50633062770916506084265937)
      ·
        refine ⟨37974797078187379563199453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50633062770916506084265937 37974797078187379563199453)
        ·
          refine ⟨14240548904320267336199795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37974797078187379563199453 14240548904320267336199795)
          ·
            refine ⟨21360823356480401004299693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14240548904320267336199795 21360823356480401004299693)
            ·
              refine ⟨8010308758680150376612385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21360823356480401004299693 8010308758680150376612385)
              ·
                refine ⟨6007731569010112782459289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8010308758680150376612385 6007731569010112782459289)
                ·
                  refine ⟨4505798676757584586844467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6007731569010112782459289 4505798676757584586844467)
                  ·
                    refine ⟨6758698015136376880266701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4505798676757584586844467 6758698015136376880266701)
                    ·
                      refine ⟨2534511755676141330100013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6758698015136376880266701 2534511755676141330100013)
                      ·
                        rfl

theorem cell23_4935944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_4935944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935944 prefixEnd_4935944 := by exact prefixLift 4935944
  have htrace : WordTrace (prefixWord ++ tailWord_4935944) baseStart_4935944 baseEnd_4935944 := by
    simpa [prefixWord, tailWord_4935944, baseEnd_4935944] using wordTrace_append hprefix tailTrace_4935944
  have hstable : (prefixWord ++ tailWord_4935944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935944).length < 2 ^ (prefixWord ++ tailWord_4935944).sum := by decide
  have hdescent : baseEnd_4935944 < baseStart_4935944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936000 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 3]
def baseStart_4936000 : Nat := 118140960795 + 4936000 * 2 ^ 59
def prefixEnd_4936000 : Nat := 4983230072969 + 3 ^ 40 * 4936000 * 2
def baseEnd_4936000 : Nat := 2534540510592793110999755

theorem tailTrace_4936000 : CollatzResearch.WordTrace tailWord_4936000 prefixEnd_4936000 2534540510592793110999755 := by
  unfold tailWord_4936000
  simp only [CollatzResearch.WordTrace]
  refine ⟨90015355058861238265158727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120020473411814984353544969 90015355058861238265158727)
  ·
    refine ⟨135023032588291857397738091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90015355058861238265158727 135023032588291857397738091)
    ·
      refine ⟨202534548882437786096607137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135023032588291857397738091 202534548882437786096607137)
      ·
        refine ⟨151900911661828339572455353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202534548882437786096607137 151900911661828339572455353)
        ·
          refine ⟨113925683746371254679341515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151900911661828339572455353 113925683746371254679341515)
          ·
            refine ⟨170888525619556882019012273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113925683746371254679341515 170888525619556882019012273)
            ·
              refine ⟨128166394214667661514259205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170888525619556882019012273 128166394214667661514259205)
              ·
                refine ⟨24031198915250186533923601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128166394214667661514259205 24031198915250186533923601)
                ·
                  refine ⟨18023399186437639900442701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24031198915250186533923601 18023399186437639900442701)
                  ·
                    refine ⟨6758774694914114962666013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18023399186437639900442701 6758774694914114962666013)
                    ·
                      refine ⟨2534540510592793110999755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6758774694914114962666013 2534540510592793110999755)
                      ·
                        rfl

theorem cell23_4936000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_4936000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936000 prefixEnd_4936000 := by exact prefixLift 4936000
  have htrace : WordTrace (prefixWord ++ tailWord_4936000) baseStart_4936000 baseEnd_4936000 := by
    simpa [prefixWord, tailWord_4936000, baseEnd_4936000] using wordTrace_append hprefix tailTrace_4936000
  have hstable : (prefixWord ++ tailWord_4936000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936000).length < 2 ^ (prefixWord ++ tailWord_4936000).sum := by decide
  have hdescent : baseEnd_4936000 < baseStart_4936000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936037 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_4936037 : Nat := 118140960795 + 4936037 * 2 ^ 59
def prefixEnd_4936037 : Nat := 4983230072969 + 3 ^ 40 * 4936037 * 2
def baseEnd_4936037 : Nat := 844853169792336488745695

theorem tailTrace_4936037 : CollatzResearch.WordTrace tailWord_4936037 prefixEnd_4936037 844853169792336488745695 := by
  unfold tailWord_4936037
  simp only [CollatzResearch.WordTrace]
  refine ⟨180032059618588431849414365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120021373079058954566276243 180032059618588431849414365)
  ·
    refine ⟨67512022356970661943530387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180032059618588431849414365 67512022356970661943530387)
    ·
      refine ⟨101268033535455992915295581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67512022356970661943530387 101268033535455992915295581)
      ·
        refine ⟨37975512575795997343235843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101268033535455992915295581 37975512575795997343235843)
        ·
          refine ⟨56963268863693996014853765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37975512575795997343235843 56963268863693996014853765)
          ·
            refine ⟨10680612911942624252785081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56963268863693996014853765 10680612911942624252785081)
            ·
              refine ⟨8010459683956968189588811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10680612911942624252785081 8010459683956968189588811)
              ·
                refine ⟨12015689525935452284383217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8010459683956968189588811 12015689525935452284383217)
                ·
                  refine ⟨9011767144451589213287413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12015689525935452284383217 9011767144451589213287413)
                  ·
                    refine ⟨844853169792336488745695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9011767144451589213287413 844853169792336488745695)
                    ·
                      rfl

theorem cell23_4936037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_4936037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936037 prefixEnd_4936037 := by exact prefixLift 4936037
  have htrace : WordTrace (prefixWord ++ tailWord_4936037) baseStart_4936037 baseEnd_4936037 := by
    simpa [prefixWord, tailWord_4936037, baseEnd_4936037] using wordTrace_append hprefix tailTrace_4936037
  have hstable : (prefixWord ++ tailWord_4936037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936037).length < 2 ^ (prefixWord ++ tailWord_4936037).sum := by decide
  have hdescent : baseEnd_4936037 < baseStart_4936037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936057 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 2, 4, 2]
def baseStart_4936057 : Nat := 118140960795 + 4936057 * 2 ^ 59
def prefixEnd_4936057 : Nat := 4983230072969 + 3 ^ 40 * 4936057 * 2
def baseEnd_4936057 : Nat := 2534569778990099387986993

theorem tailTrace_4936057 : CollatzResearch.WordTrace tailWord_4936057 prefixEnd_4936057 2534569778990099387986993 := by
  unfold tailWord_4936057
  simp only [CollatzResearch.WordTrace]
  refine ⟨180032789078515975265142425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120021859385677316843428283 180032789078515975265142425)
  ·
    refine ⟨135024591808886981448856819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180032789078515975265142425 135024591808886981448856819)
    ·
      refine ⟨202536887713330472173285229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135024591808886981448856819 202536887713330472173285229)
      ·
        refine ⟨75951332892498927064981961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202536887713330472173285229 75951332892498927064981961)
        ·
          refine ⟨56963499669374195298736471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75951332892498927064981961 56963499669374195298736471)
          ·
            refine ⟨85445249504061292948104707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56963499669374195298736471 85445249504061292948104707)
            ·
              refine ⟨128167874256091939422157061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85445249504061292948104707 128167874256091939422157061)
              ·
                refine ⟨24031476423017238641654449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128167874256091939422157061 24031476423017238641654449)
                ·
                  refine ⟨18023607317262928981240837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24031476423017238641654449 18023607317262928981240837)
                  ·
                    refine ⟨3379426371986799183982657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18023607317262928981240837 3379426371986799183982657)
                    ·
                      refine ⟨2534569778990099387986993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379426371986799183982657 2534569778990099387986993)
                      ·
                        rfl

theorem cell23_4936057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_4936057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936057 prefixEnd_4936057 := by exact prefixLift 4936057
  have htrace : WordTrace (prefixWord ++ tailWord_4936057) baseStart_4936057 baseEnd_4936057 := by
    simpa [prefixWord, tailWord_4936057, baseEnd_4936057] using wordTrace_append hprefix tailTrace_4936057
  have hstable : (prefixWord ++ tailWord_4936057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936057).length < 2 ^ (prefixWord ++ tailWord_4936057).sum := by decide
  have hdescent : baseEnd_4936057 < baseStart_4936057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936157 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4936157 : Nat := 118140960795 + 4936157 * 2 ^ 59
def prefixEnd_4936157 : Nat := 4983230072969 + 3 ^ 40 * 4936157 * 2
def baseEnd_4936157 : Nat := 844873709018516332245511

theorem tailTrace_4936157 : CollatzResearch.WordTrace tailWord_4936157 prefixEnd_4936157 844873709018516332245511 := by
  unfold tailWord_4936157
  simp only [CollatzResearch.WordTrace]
  refine ⟨180036436378153692343782725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120024290918769128229188483 180036436378153692343782725)
  ·
    refine ⟨33756831820903817314459261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180036436378153692343782725 33756831820903817314459261)
    ·
      refine ⟨12658811932838931492922223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33756831820903817314459261 12658811932838931492922223)
      ·
        refine ⟨18988217899258397239383335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12658811932838931492922223 18988217899258397239383335)
        ·
          refine ⟨28482326848887595859075003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18988217899258397239383335 28482326848887595859075003)
          ·
            refine ⟨42723490273331393788612505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28482326848887595859075003 42723490273331393788612505)
            ·
              refine ⟨32042617704998545341459379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42723490273331393788612505 32042617704998545341459379)
              ·
                refine ⟨48063926557497818012189069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32042617704998545341459379 48063926557497818012189069)
                ·
                  refine ⟨18023972459061681754570901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48063926557497818012189069 18023972459061681754570901)
                  ·
                    refine ⟨844873709018516332245511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18023972459061681754570901 844873709018516332245511)
                    ·
                      rfl

theorem cell23_4936157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4936157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936157 prefixEnd_4936157 := by exact prefixLift 4936157
  have htrace : WordTrace (prefixWord ++ tailWord_4936157) baseStart_4936157 baseEnd_4936157 := by
    simpa [prefixWord, tailWord_4936157, baseEnd_4936157] using wordTrace_append hprefix tailTrace_4936157
  have hstable : (prefixWord ++ tailWord_4936157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936157).length < 2 ^ (prefixWord ++ tailWord_4936157).sum := by decide
  have hdescent : baseEnd_4936157 < baseStart_4936157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936174 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_4936174 : Nat := 118140960795 + 4936174 * 2 ^ 59
def prefixEnd_4936174 : Nat := 4983230072969 + 3 ^ 40 * 4936174 * 2
def baseEnd_4936174 : Nat := 844876618742225143407985

theorem tailTrace_4936174 : CollatzResearch.WordTrace tailWord_4936174 prefixEnd_4936174 844876618742225143407985 := by
  unfold tailWord_4936174
  simp only [CollatzResearch.WordTrace]
  refine ⟨22504632052386513030893947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120024704279394736164767717 22504632052386513030893947)
  ·
    refine ⟨33756948078579769546340921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22504632052386513030893947 33756948078579769546340921)
    ·
      refine ⟨25317711058934827159755691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33756948078579769546340921 25317711058934827159755691)
      ·
        refine ⟨37976566588402240739633537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25317711058934827159755691 37976566588402240739633537)
        ·
          refine ⟨28482424941301680554725153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37976566588402240739633537 28482424941301680554725153)
          ·
            refine ⟨21361818705976260416043865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28482424941301680554725153 21361818705976260416043865)
            ·
              refine ⟨16021364029482195312032899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21361818705976260416043865 16021364029482195312032899)
              ·
                refine ⟨24032046044223292968049349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16021364029482195312032899 24032046044223292968049349)
                ·
                  refine ⟨4506008633291867431509253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24032046044223292968049349 4506008633291867431509253)
                  ·
                    refine ⟨844876618742225143407985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4506008633291867431509253 844876618742225143407985)
                    ·
                      rfl

theorem cell23_4936174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_4936174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936174 prefixEnd_4936174 := by exact prefixLift 4936174
  have htrace : WordTrace (prefixWord ++ tailWord_4936174) baseStart_4936174 baseEnd_4936174 := by
    simpa [prefixWord, tailWord_4936174, baseEnd_4936174] using wordTrace_append hprefix tailTrace_4936174
  have hstable : (prefixWord ++ tailWord_4936174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936174).length < 2 ^ (prefixWord ++ tailWord_4936174).sum := by decide
  have hdescent : baseEnd_4936174 < baseStart_4936174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936232 : List Nat := [2, 1, 5, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4936232 : Nat := 118140960795 + 4936232 * 2 ^ 59
def prefixEnd_4936232 : Nat := 4983230072969 + 3 ^ 40 * 4936232 * 2
def baseEnd_4936232 : Nat := 2534659638104636203298689

theorem tailTrace_4936232 : CollatzResearch.WordTrace tailWord_4936232 prefixEnd_4936232 2534659638104636203298689 := by
  unfold tailWord_4936232
  simp only [CollatzResearch.WordTrace]
  refine ⟨90019585926440990076381475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120026114568587986768508633 90019585926440990076381475)
  ·
    refine ⟨135029378889661485114572213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90019585926440990076381475 135029378889661485114572213)
    ·
      refine ⟨12659004270905764229491145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135029378889661485114572213 12659004270905764229491145)
      ·
        refine ⟨9494253203179323172118359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12659004270905764229491145 9494253203179323172118359)
        ·
          refine ⟨14241379804768984758177539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9494253203179323172118359 14241379804768984758177539)
          ·
            refine ⟨21362069707153477137266309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14241379804768984758177539 21362069707153477137266309)
            ·
              refine ⟨4005388070091276963237433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21362069707153477137266309 4005388070091276963237433)
              ·
                refine ⟨3004041052568457722428075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4005388070091276963237433 3004041052568457722428075)
                ·
                  refine ⟨4506061578852686583642113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004041052568457722428075 4506061578852686583642113)
                  ·
                    refine ⟨3379546184139514937731585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4506061578852686583642113 3379546184139514937731585)
                    ·
                      refine ⟨2534659638104636203298689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379546184139514937731585 2534659638104636203298689)
                      ·
                        rfl

theorem cell23_4936232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4936232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936232 prefixEnd_4936232 := by exact prefixLift 4936232
  have htrace : WordTrace (prefixWord ++ tailWord_4936232) baseStart_4936232 baseEnd_4936232 := by
    simpa [prefixWord, tailWord_4936232, baseEnd_4936232] using wordTrace_append hprefix tailTrace_4936232
  have hstable : (prefixWord ++ tailWord_4936232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936232).length < 2 ^ (prefixWord ++ tailWord_4936232).sum := by decide
  have hdescent : baseEnd_4936232 < baseStart_4936232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936247 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 2, 6]
def baseStart_4936247 : Nat := 118140960795 + 4936247 * 2 ^ 59
def prefixEnd_4936247 : Nat := 4983230072969 + 3 ^ 40 * 4936247 * 2
def baseEnd_4936247 : Nat := 844889113438151214870373

theorem tailTrace_4936247 : CollatzResearch.WordTrace tailWord_4936247 prefixEnd_4936247 844889113438151214870373 := by
  unfold tailWord_4936247
  simp only [CollatzResearch.WordTrace]
  refine ⟨180039718947827637714558995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120026479298551758476372663 180039718947827637714558995)
  ·
    refine ⟨270059578421741456571838493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180039718947827637714558995 270059578421741456571838493)
    ·
      refine ⟨101272341908153046214439435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270059578421741456571838493 101272341908153046214439435)
      ·
        refine ⟨151908512862229569321659153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101272341908153046214439435 151908512862229569321659153)
        ·
          refine ⟨113931384646672176991244365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151908512862229569321659153 113931384646672176991244365)
          ·
            refine ⟨42724269242502066371716637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113931384646672176991244365 42724269242502066371716637)
            ·
              refine ⟨16021600965938274889393739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42724269242502066371716637 16021600965938274889393739)
              ·
                refine ⟨24032401448907412334090609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16021600965938274889393739 24032401448907412334090609)
                ·
                  refine ⟨18024301086680559250567957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24032401448907412334090609 18024301086680559250567957)
                  ·
                    refine ⟨844889113438151214870373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18024301086680559250567957 844889113438151214870373)
                    ·
                      rfl

theorem cell23_4936247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_4936247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936247 prefixEnd_4936247 := by exact prefixLift 4936247
  have htrace : WordTrace (prefixWord ++ tailWord_4936247) baseStart_4936247 baseEnd_4936247 := by
    simpa [prefixWord, tailWord_4936247, baseEnd_4936247] using wordTrace_append hprefix tailTrace_4936247
  have hstable : (prefixWord ++ tailWord_4936247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936247).length < 2 ^ (prefixWord ++ tailWord_4936247).sum := by decide
  have hdescent : baseEnd_4936247 < baseStart_4936247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936288 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 2, 2, 2]
def baseStart_4936288 : Nat := 118140960795 + 4936288 * 2 ^ 59
def prefixEnd_4936288 : Nat := 4983230072969 + 3 ^ 40 * 4936288 * 2
def baseEnd_4936288 : Nat := 2534688393021287984198431

theorem tailTrace_4936288 : CollatzResearch.WordTrace tailWord_4936288 prefixEnd_4936288 2534688393021287984198431 := by
  unfold tailWord_4936288
  simp only [CollatzResearch.WordTrace]
  refine ⟨90020607170339550858400759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120027476227119401144534345 90020607170339550858400759)
  ·
    refine ⟨135030910755509326287601139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90020607170339550858400759 135030910755509326287601139)
    ·
      refine ⟨202546366133263989431401709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135030910755509326287601139 202546366133263989431401709)
      ·
        refine ⟨75954887299973996036775641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202546366133263989431401709 75954887299973996036775641)
        ·
          refine ⟨56966165474980497027581731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75954887299973996036775641 56966165474980497027581731)
          ·
            refine ⟨85449248212470745541372597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56966165474980497027581731 85449248212470745541372597)
            ·
              refine ⟨8010867019919132394503681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85449248212470745541372597 8010867019919132394503681)
              ·
                refine ⟨6008150264939349295877761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8010867019919132394503681 6008150264939349295877761)
                ·
                  refine ⟨4506112698704511971908321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6008150264939349295877761 4506112698704511971908321)
                  ·
                    refine ⟨3379584524028383978931241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4506112698704511971908321 3379584524028383978931241)
                    ·
                      refine ⟨2534688393021287984198431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379584524028383978931241 2534688393021287984198431)
                      ·
                        rfl

theorem cell23_4936288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_4936288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936288 prefixEnd_4936288 := by exact prefixLift 4936288
  have htrace : WordTrace (prefixWord ++ tailWord_4936288) baseStart_4936288 baseEnd_4936288 := by
    simpa [prefixWord, tailWord_4936288, baseEnd_4936288] using wordTrace_append hprefix tailTrace_4936288
  have hstable : (prefixWord ++ tailWord_4936288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936288).length < 2 ^ (prefixWord ++ tailWord_4936288).sum := by decide
  have hdescent : baseEnd_4936288 < baseStart_4936288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936307 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 6, 5]
def baseStart_4936307 : Nat := 118140960795 + 4936307 * 2 ^ 59
def prefixEnd_4936307 : Nat := 4983230072969 + 3 ^ 40 * 4936307 * 2
def baseEnd_4936307 : Nat := 844899383051241136620281

theorem tailTrace_4936307 : CollatzResearch.WordTrace tailWord_4936307 prefixEnd_4936307 844899383051241136620281 := by
  unfold tailWord_4936307
  simp only [CollatzResearch.WordTrace]
  refine ⟨180041907327610267961743175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120027938218406845307828783 180041907327610267961743175)
  ·
    refine ⟨270062860991415401942614763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180041907327610267961743175 270062860991415401942614763)
    ·
      refine ⟨405094291487123102913922145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270062860991415401942614763 405094291487123102913922145)
      ·
        refine ⟨303820718615342327185441609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405094291487123102913922145 303820718615342327185441609)
        ·
          refine ⟨227865538961506745389081207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303820718615342327185441609 227865538961506745389081207)
          ·
            refine ⟨341798308442260118083621811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227865538961506745389081207 341798308442260118083621811)
            ·
              refine ⟨512697462663390177125432717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341798308442260118083621811 512697462663390177125432717)
              ·
                refine ⟨192261548498771316422037269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 512697462663390177125432717 192261548498771316422037269)
                ·
                  refine ⟨9012260085879905457282997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192261548498771316422037269 9012260085879905457282997)
                  ·
                    refine ⟨844899383051241136620281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9012260085879905457282997 844899383051241136620281)
                    ·
                      rfl

theorem cell23_4936307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 5].length) (baseStart_4936307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936307 prefixEnd_4936307 := by exact prefixLift 4936307
  have htrace : WordTrace (prefixWord ++ tailWord_4936307) baseStart_4936307 baseEnd_4936307 := by
    simpa [prefixWord, tailWord_4936307, baseEnd_4936307] using wordTrace_append hprefix tailTrace_4936307
  have hstable : (prefixWord ++ tailWord_4936307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936307).length < 2 ^ (prefixWord ++ tailWord_4936307).sum := by decide
  have hdescent : baseEnd_4936307 < baseStart_4936307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936314 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2]
def baseStart_4936314 : Nat := 118140960795 + 4936314 * 2 ^ 59
def prefixEnd_4936314 : Nat := 4983230072969 + 3 ^ 40 * 4936314 * 2
def baseEnd_4936314 : Nat := 2534701743518304882473311

theorem tailTrace_4936314 : CollatzResearch.WordTrace tailWord_4936314 prefixEnd_4936314 2534701743518304882473311 := by
  unfold tailWord_4936314
  simp only [CollatzResearch.WordTrace]
  refine ⟨45010540659646227039311999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120028108425723272104831997 45010540659646227039311999)
  ·
    refine ⟨67515810989469340558967999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45010540659646227039311999 67515810989469340558967999)
    ·
      refine ⟨101273716484204010838451999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67515810989469340558967999 101273716484204010838451999)
      ·
        refine ⟨151910574726306016257677999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101273716484204010838451999 151910574726306016257677999)
        ·
          refine ⟨227865862089459024386516999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151910574726306016257677999 227865862089459024386516999)
          ·
            refine ⟨341798793134188536579775499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227865862089459024386516999 341798793134188536579775499)
            ·
              refine ⟨512698189701282804869663249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341798793134188536579775499 512698189701282804869663249)
              ·
                refine ⟨384523642275962103652247437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512698189701282804869663249 384523642275962103652247437)
                ·
                  refine ⟨144196365853485788869592789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384523642275962103652247437 144196365853485788869592789)
                  ·
                    refine ⟨3379602324691073176631081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 144196365853485788869592789 3379602324691073176631081)
                    ·
                      refine ⟨2534701743518304882473311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379602324691073176631081 2534701743518304882473311)
                      ·
                        rfl

theorem cell23_4936314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_4936314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936314 prefixEnd_4936314 := by exact prefixLift 4936314
  have htrace : WordTrace (prefixWord ++ tailWord_4936314) baseStart_4936314 baseEnd_4936314 := by
    simpa [prefixWord, tailWord_4936314, baseEnd_4936314] using wordTrace_append hprefix tailTrace_4936314
  have hstable : (prefixWord ++ tailWord_4936314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936314).length < 2 ^ (prefixWord ++ tailWord_4936314).sum := by decide
  have hdescent : baseEnd_4936314 < baseStart_4936314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936324 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_4936324 : Nat := 118140960795 + 4936324 * 2 ^ 59
def prefixEnd_4936324 : Nat := 4983230072969 + 3 ^ 40 * 4936324 * 2
def baseEnd_4936324 : Nat := 844902292774949947782755

theorem tailTrace_4936324 : CollatzResearch.WordTrace tailWord_4936324 prefixEnd_4936324 844902292774949947782755 := by
  unfold tailWord_4936324
  simp only [CollatzResearch.WordTrace]
  refine ⟨90021263684274339932556013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120028351579032453243408017 90021263684274339932556013)
  ·
    refine ⟨33757973881602877474708505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90021263684274339932556013 33757973881602877474708505)
    ·
      refine ⟨25318480411202158106031379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33757973881602877474708505 25318480411202158106031379)
      ·
        refine ⟨37977720616803237159047069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25318480411202158106031379 37977720616803237159047069)
        ·
          refine ⟨14241645231301213934642651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37977720616803237159047069 14241645231301213934642651)
          ·
            refine ⟨21362467846951820901963977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14241645231301213934642651 21362467846951820901963977)
            ·
              refine ⟨16021850885213865676472983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21362467846951820901963977 16021850885213865676472983)
              ·
                refine ⟨24032776327820798514709475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16021850885213865676472983 24032776327820798514709475)
                ·
                  refine ⟨36049164491731197772064213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24032776327820798514709475 36049164491731197772064213)
                  ·
                    refine ⟨844902292774949947782755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36049164491731197772064213 844902292774949947782755)
                    ·
                      rfl

theorem cell23_4936324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_4936324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936324 prefixEnd_4936324 := by exact prefixLift 4936324
  have htrace : WordTrace (prefixWord ++ tailWord_4936324) baseStart_4936324 baseEnd_4936324 := by
    simpa [prefixWord, tailWord_4936324, baseEnd_4936324] using wordTrace_append hprefix tailTrace_4936324
  have hstable : (prefixWord ++ tailWord_4936324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936324).length < 2 ^ (prefixWord ++ tailWord_4936324).sum := by decide
  have hdescent : baseEnd_4936324 < baseStart_4936324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936334 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4936334 : Nat := 118140960795 + 4936334 * 2 ^ 59
def prefixEnd_4936334 : Nat := 4983230072969 + 3 ^ 40 * 4936334 * 2
def baseEnd_4936334 : Nat := 2534712013131394804223219

theorem tailTrace_4936334 : CollatzResearch.WordTrace tailWord_4936334 prefixEnd_4936334 2534712013131394804223219 := by
  unfold tailWord_4936334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22505361512314056446622007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120028594732341634381984037 22505361512314056446622007)
  ·
    refine ⟨33758042268471084669933011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22505361512314056446622007 33758042268471084669933011)
    ·
      refine ⟨50637063402706627004899517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33758042268471084669933011 50637063402706627004899517)
      ·
        refine ⟨18988898776014985126837319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50637063402706627004899517 18988898776014985126837319)
        ·
          refine ⟨28483348164022477690255979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18988898776014985126837319 28483348164022477690255979)
          ·
            refine ⟨42725022246033716535383969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28483348164022477690255979 42725022246033716535383969)
            ·
              refine ⟨32043766684525287401537977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42725022246033716535383969 32043766684525287401537977)
              ·
                refine ⟨24032825013393965551153483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32043766684525287401537977 24032825013393965551153483)
                ·
                  refine ⟨36049237520090948326730225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24032825013393965551153483 36049237520090948326730225)
                  ·
                    refine ⟨27036928140068211245047669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36049237520090948326730225 27036928140068211245047669)
                    ·
                      refine ⟨2534712013131394804223219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27036928140068211245047669 2534712013131394804223219)
                      ·
                        rfl

theorem cell23_4936334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4936334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936334 prefixEnd_4936334 := by exact prefixLift 4936334
  have htrace : WordTrace (prefixWord ++ tailWord_4936334) baseStart_4936334 baseEnd_4936334 := by
    simpa [prefixWord, tailWord_4936334, baseEnd_4936334] using wordTrace_append hprefix tailTrace_4936334
  have hstable : (prefixWord ++ tailWord_4936334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936334).length < 2 ^ (prefixWord ++ tailWord_4936334).sum := by decide
  have hdescent : baseEnd_4936334 < baseStart_4936334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936381 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_4936381 : Nat := 118140960795 + 4936381 * 2 ^ 59
def prefixEnd_4936381 : Nat := 4983230072969 + 3 ^ 40 * 4936381 * 2
def baseEnd_4936381 : Nat := 2534736146722156120335503

theorem tailTrace_4936381 : CollatzResearch.WordTrace tailWord_4936381 prefixEnd_4936381 2534736146722156120335503 := by
  unfold tailWord_4936381
  simp only [CollatzResearch.WordTrace]
  refine ⟨180044606329342178599936997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120029737552894785733291331 180044606329342178599936997)
  ·
    refine ⟨33758363686751658487488187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180044606329342178599936997 33758363686751658487488187)
    ·
      refine ⟨50637545530127487731232281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33758363686751658487488187 50637545530127487731232281)
      ·
        refine ⟨37978159147595615798424211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50637545530127487731232281 37978159147595615798424211)
        ·
          refine ⟨56967238721393423697636317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37978159147595615798424211 56967238721393423697636317)
          ·
            refine ⟨21362714520522533886613619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56967238721393423697636317 21362714520522533886613619)
            ·
              refine ⟨32044071780783800829920429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21362714520522533886613619 32044071780783800829920429)
              ·
                refine ⟨12016526917793925311220161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32044071780783800829920429 12016526917793925311220161)
                ·
                  refine ⟨9012395188345443983415121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12016526917793925311220161 9012395188345443983415121)
                  ·
                    refine ⟨6759296391259082987561341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9012395188345443983415121 6759296391259082987561341)
                    ·
                      refine ⟨2534736146722156120335503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6759296391259082987561341 2534736146722156120335503)
                      ·
                        rfl

theorem cell23_4936381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_4936381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936381 prefixEnd_4936381 := by exact prefixLift 4936381
  have htrace : WordTrace (prefixWord ++ tailWord_4936381) baseStart_4936381 baseEnd_4936381 := by
    simpa [prefixWord, tailWord_4936381, baseEnd_4936381] using wordTrace_append hprefix tailTrace_4936381
  have hstable : (prefixWord ++ tailWord_4936381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936381).length < 2 ^ (prefixWord ++ tailWord_4936381).sum := by decide
  have hdescent : baseEnd_4936381 < baseStart_4936381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936438 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_4936438 : Nat := 118140960795 + 4936438 * 2 ^ 59
def prefixEnd_4936438 : Nat := 4983230072969 + 3 ^ 40 * 4936438 * 2
def baseEnd_4936438 : Nat := 2534765415119462397322741

theorem tailTrace_4936438 : CollatzResearch.WordTrace tailWord_4936438 prefixEnd_4936438 2534765415119462397322741 := by
  unfold tailWord_4936438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11252917830633479833422623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120031123526757118223174645 11252917830633479833422623)
  ·
    refine ⟨16879376745950219750133935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11252917830633479833422623 16879376745950219750133935)
    ·
      refine ⟨25319065118925329625200903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16879376745950219750133935 25319065118925329625200903)
      ·
        refine ⟨37978597678387994437801355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25319065118925329625200903 37978597678387994437801355)
        ·
          refine ⟨56967896517581991656702033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37978597678387994437801355 56967896517581991656702033)
          ·
            refine ⟨42725922388186493742526525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56967896517581991656702033 42725922388186493742526525)
            ·
              refine ⟨16022220895569935153447447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42725922388186493742526525 16022220895569935153447447)
              ·
                refine ⟨24033331343354902730171171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16022220895569935153447447 24033331343354902730171171)
                ·
                  refine ⟨36049997015032354095256757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24033331343354902730171171 36049997015032354095256757)
                  ·
                    refine ⟨3379687220159283196430321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36049997015032354095256757 3379687220159283196430321)
                    ·
                      refine ⟨2534765415119462397322741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379687220159283196430321 2534765415119462397322741)
                      ·
                        rfl

theorem cell23_4936438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_4936438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936438 prefixEnd_4936438 := by exact prefixLift 4936438
  have htrace : WordTrace (prefixWord ++ tailWord_4936438) baseStart_4936438 baseEnd_4936438 := by
    simpa [prefixWord, tailWord_4936438, baseEnd_4936438] using wordTrace_append hprefix tailTrace_4936438
  have hstable : (prefixWord ++ tailWord_4936438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936438).length < 2 ^ (prefixWord ++ tailWord_4936438).sum := by decide
  have hdescent : baseEnd_4936438 < baseStart_4936438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936445 : List Nat := [1, 4, 1, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_4936445 : Nat := 118140960795 + 4936445 * 2 ^ 59
def prefixEnd_4936445 : Nat := 4983230072969 + 3 ^ 40 * 4936445 * 2
def baseEnd_4936445 : Nat := 2534769009484043869935209

theorem tailTrace_4936445 : CollatzResearch.WordTrace tailWord_4936445 prefixEnd_4936445 2534769009484043869935209 := by
  unfold tailWord_4936445
  simp only [CollatzResearch.WordTrace]
  refine ⟨180046940601110317530266789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120031293734073545020177859 180046940601110317530266789)
  ·
    refine ⟨33758801362708184536925023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180046940601110317530266789 33758801362708184536925023)
    ·
      refine ⟨50638202044062276805387535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33758801362708184536925023 50638202044062276805387535)
      ·
        refine ⟨75957303066093415208081303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50638202044062276805387535 75957303066093415208081303)
        ·
          refine ⟨113935954599140122812121955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75957303066093415208081303 113935954599140122812121955)
          ·
            refine ⟨170903931898710184218182933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113935954599140122812121955 170903931898710184218182933)
            ·
              refine ⟨8011121807752039885227325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 170903931898710184218182933 8011121807752039885227325)
              ·
                refine ⟨3004170677907014956960247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8011121807752039885227325 3004170677907014956960247)
                ·
                  refine ⟨4506256016860522435440371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004170677907014956960247 4506256016860522435440371)
                  ·
                    refine ⟨6759384025290783653160557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4506256016860522435440371 6759384025290783653160557)
                    ·
                      refine ⟨2534769009484043869935209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6759384025290783653160557 2534769009484043869935209)
                      ·
                        rfl

theorem cell23_4936445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_4936445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936445 prefixEnd_4936445 := by exact prefixLift 4936445
  have htrace : WordTrace (prefixWord ++ tailWord_4936445) baseStart_4936445 baseEnd_4936445 := by
    simpa [prefixWord, tailWord_4936445, baseEnd_4936445] using wordTrace_append hprefix tailTrace_4936445
  have hstable : (prefixWord ++ tailWord_4936445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936445).length < 2 ^ (prefixWord ++ tailWord_4936445).sum := by decide
  have hdescent : baseEnd_4936445 < baseStart_4936445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936474 : List Nat := [3, 1, 1, 3, 2, 1, 2, 10]
def baseStart_4936474 : Nat := 118140960795 + 4936474 * 2 ^ 59
def prefixEnd_4936474 : Nat := 4983230072969 + 3 ^ 40 * 4936474 * 2
def baseEnd_4936474 : Nat := 93880885200852750239725

theorem tailTrace_4936474 : CollatzResearch.WordTrace tailWord_4936474 prefixEnd_4936474 93880885200852750239725 := by
  unfold tailWord_4936474
  simp only [CollatzResearch.WordTrace]
  refine ⟨45011999579501313870768119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120031998878670170322048317 45011999579501313870768119)
  ·
    refine ⟨67517999369251970806152179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45011999579501313870768119 67517999369251970806152179)
    ·
      refine ⟨101276999053877956209228269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67517999369251970806152179 101276999053877956209228269)
      ·
        refine ⟨37978874645204233578460601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101276999053877956209228269 37978874645204233578460601)
        ·
          refine ⟨28484155983903175183845451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37978874645204233578460601 28484155983903175183845451)
          ·
            refine ⟨42726233975854762775768177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28484155983903175183845451 42726233975854762775768177)
            ·
              refine ⟨32044675481891072081826133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42726233975854762775768177 32044675481891072081826133)
              ·
                refine ⟨93880885200852750239725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32044675481891072081826133 93880885200852750239725)
                ·
                  rfl

theorem cell23_4936474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 10].length) (baseStart_4936474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936474 prefixEnd_4936474 := by exact prefixLift 4936474
  have htrace : WordTrace (prefixWord ++ tailWord_4936474) baseStart_4936474 baseEnd_4936474 := by
    simpa [prefixWord, tailWord_4936474, baseEnd_4936474] using wordTrace_append hprefix tailTrace_4936474
  have hstable : (prefixWord ++ tailWord_4936474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936474).length < 2 ^ (prefixWord ++ tailWord_4936474).sum := by decide
  have hdescent : baseEnd_4936474 < baseStart_4936474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936535 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_4936535 : Nat := 118140960795 + 4936535 * 2 ^ 59
def prefixEnd_4936535 : Nat := 4983230072969 + 3 ^ 40 * 4936535 * 2
def baseEnd_4936535 : Nat := 2534815222742948517809795

theorem tailTrace_4936535 : CollatzResearch.WordTrace tailWord_4936535 prefixEnd_4936535 2534815222742948517809795 := by
  unfold tailWord_4936535
  simp only [CollatzResearch.WordTrace]
  refine ⟨180050223170784262901043059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120033482113856175267362039 180050223170784262901043059)
  ·
    refine ⟨270075334756176394351564589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180050223170784262901043059 270075334756176394351564589)
    ·
      refine ⟨101278250533566147881836721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270075334756176394351564589 101278250533566147881836721)
      ·
        refine ⟨75958687900174610911377541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101278250533566147881836721 75958687900174610911377541)
        ·
          refine ⟨14242253981282739545883289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75958687900174610911377541 14242253981282739545883289)
          ·
            refine ⟨10681690485962054659412467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14242253981282739545883289 10681690485962054659412467)
            ·
              refine ⟨16022535728943081989118701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10681690485962054659412467 16022535728943081989118701)
              ·
                refine ⟨6008450898353655745919513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16022535728943081989118701 6008450898353655745919513)
                ·
                  refine ⟨4506338173765241809439635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6008450898353655745919513 4506338173765241809439635)
                  ·
                    refine ⟨6759507260647862714159453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4506338173765241809439635 6759507260647862714159453)
                    ·
                      refine ⟨2534815222742948517809795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6759507260647862714159453 2534815222742948517809795)
                      ·
                        rfl

theorem cell23_4936535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_4936535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936535 prefixEnd_4936535 := by exact prefixLift 4936535
  have htrace : WordTrace (prefixWord ++ tailWord_4936535) baseStart_4936535 baseEnd_4936535 := by
    simpa [prefixWord, tailWord_4936535, baseEnd_4936535] using wordTrace_append hprefix tailTrace_4936535
  have hstable : (prefixWord ++ tailWord_4936535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936535).length < 2 ^ (prefixWord ++ tailWord_4936535).sum := by decide
  have hdescent : baseEnd_4936535 < baseStart_4936535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936561 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_4936561 : Nat := 118140960795 + 4936561 * 2 ^ 59
def prefixEnd_4936561 : Nat := 4983230072969 + 3 ^ 40 * 4936561 * 2
def baseEnd_4936561 : Nat := 2534828573239965416084675

theorem tailTrace_4936561 : CollatzResearch.WordTrace tailWord_4936561 prefixEnd_4936561 2534828573239965416084675 := by
  unfold tailWord_4936561
  simp only [CollatzResearch.WordTrace]
  refine ⟨180051171468690069341489537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120034114312460046227659691 180051171468690069341489537)
  ·
    refine ⟨135038378601517552006117153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180051171468690069341489537 135038378601517552006117153)
    ·
      refine ⟨101278783951138164004587865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135038378601517552006117153 101278783951138164004587865)
      ·
        refine ⟨75959087963353623003440899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101278783951138164004587865 75959087963353623003440899)
        ·
          refine ⟨113938631945030434505161349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75959087963353623003440899 113938631945030434505161349)
          ·
            refine ⟨21363493489693206469717753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113938631945030434505161349 21363493489693206469717753)
            ·
              refine ⟨16022620117269904852288315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21363493489693206469717753 16022620117269904852288315)
              ·
                refine ⟨24033930175904857278432473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16022620117269904852288315 24033930175904857278432473)
                ·
                  refine ⟨18025447631928642958824355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24033930175904857278432473 18025447631928642958824355)
                  ·
                    refine ⟨27038171447892964438236533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18025447631928642958824355 27038171447892964438236533)
                    ·
                      refine ⟨2534828573239965416084675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27038171447892964438236533 2534828573239965416084675)
                      ·
                        rfl

theorem cell23_4936561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_4936561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936561 prefixEnd_4936561 := by exact prefixLift 4936561
  have htrace : WordTrace (prefixWord ++ tailWord_4936561) baseStart_4936561 baseEnd_4936561 := by
    simpa [prefixWord, tailWord_4936561, baseEnd_4936561] using wordTrace_append hprefix tailTrace_4936561
  have hstable : (prefixWord ++ tailWord_4936561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936561).length < 2 ^ (prefixWord ++ tailWord_4936561).sum := by decide
  have hdescent : baseEnd_4936561 < baseStart_4936561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936575 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 2, 2, 2]
def baseStart_4936575 : Nat := 118140960795 + 4936575 * 2 ^ 59
def prefixEnd_4936575 : Nat := 4983230072969 + 3 ^ 40 * 4936575 * 2
def baseEnd_4936575 : Nat := 2534835761969128361309611

theorem tailTrace_4936575 : CollatzResearch.WordTrace tailWord_4936575 prefixEnd_4936575 2534835761969128361309611 := by
  unfold tailWord_4936575
  simp only [CollatzResearch.WordTrace]
  refine ⟨180051682090639349732499179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120034454727092899821666119 180051682090639349732499179)
  ·
    refine ⟨270077523135959024598748769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180051682090639349732499179 270077523135959024598748769)
    ·
      refine ⟨202558142351969268449061577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270077523135959024598748769 202558142351969268449061577)
      ·
        refine ⟨151918606763976951336796183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202558142351969268449061577 151918606763976951336796183)
        ·
          refine ⟨227877910145965427005194275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151918606763976951336796183 227877910145965427005194275)
          ·
            refine ⟨341816865218948140507791413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227877910145965427005194275 341816865218948140507791413)
            ·
              refine ⟨32045331114276388172605445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 341816865218948140507791413 32045331114276388172605445)
              ·
                refine ⟨6008499583926822782363521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32045331114276388172605445 6008499583926822782363521)
                ·
                  refine ⟨4506374687945117086772641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6008499583926822782363521 4506374687945117086772641)
                  ·
                    refine ⟨3379781015958837815079481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4506374687945117086772641 3379781015958837815079481)
                    ·
                      refine ⟨2534835761969128361309611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379781015958837815079481 2534835761969128361309611)
                      ·
                        rfl

theorem cell23_4936575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_4936575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936575 prefixEnd_4936575 := by exact prefixLift 4936575
  have htrace : WordTrace (prefixWord ++ tailWord_4936575) baseStart_4936575 baseEnd_4936575 := by
    simpa [prefixWord, tailWord_4936575, baseEnd_4936575] using wordTrace_append hprefix tailTrace_4936575
  have hstable : (prefixWord ++ tailWord_4936575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936575).length < 2 ^ (prefixWord ++ tailWord_4936575).sum := by decide
  have hdescent : baseEnd_4936575 < baseStart_4936575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936701 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_4936701 : Nat := 118140960795 + 4936701 * 2 ^ 59
def prefixEnd_4936701 : Nat := 4983230072969 + 3 ^ 40 * 4936701 * 2
def baseEnd_4936701 : Nat := 844966820177198289444677

theorem tailTrace_4936701 : CollatzResearch.WordTrace tailWord_4936701 prefixEnd_4936701 844966820177198289444677 := by
  unfold tailWord_4936701
  simp only [CollatzResearch.WordTrace]
  refine ⟨180056277688182873251585957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120037518458788582167723971 180056277688182873251585957)
  ·
    refine ⟨33760552066534288734672367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180056277688182873251585957 33760552066534288734672367)
    ·
      refine ⟨50640828099801433102008551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33760552066534288734672367 50640828099801433102008551)
      ·
        refine ⟨75961242149702149653012827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50640828099801433102008551 75961242149702149653012827)
        ·
          refine ⟨113941863224553224479519241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75961242149702149653012827 113941863224553224479519241)
          ·
            refine ⟨85456397418414918359639431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113941863224553224479519241 85456397418414918359639431)
            ·
              refine ⟨128184596127622377539459147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85456397418414918359639431 128184596127622377539459147)
              ·
                refine ⟨192276894191433566309188721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128184596127622377539459147 192276894191433566309188721)
                ·
                  refine ⟨144207670643575174731891541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192276894191433566309188721 144207670643575174731891541)
                  ·
                    refine ⟨844966820177198289444677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 144207670643575174731891541 844966820177198289444677)
                    ·
                      rfl

theorem cell23_4936701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_4936701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936701 prefixEnd_4936701 := by exact prefixLift 4936701
  have htrace : WordTrace (prefixWord ++ tailWord_4936701) baseStart_4936701 baseEnd_4936701 := by
    simpa [prefixWord, tailWord_4936701, baseEnd_4936701] using wordTrace_append hprefix tailTrace_4936701
  have hstable : (prefixWord ++ tailWord_4936701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936701).length < 2 ^ (prefixWord ++ tailWord_4936701).sum := by decide
  have hdescent : baseEnd_4936701 < baseStart_4936701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936705 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 6]
def baseStart_4936705 : Nat := 118140960795 + 4936705 * 2 ^ 59
def prefixEnd_4936705 : Nat := 4983230072969 + 3 ^ 40 * 4936705 * 2
def baseEnd_4936705 : Nat := 281655834939356983631557

theorem tailTrace_4936705 : CollatzResearch.WordTrace tailWord_4936705 prefixEnd_4936705 281655834939356983631557 := by
  unfold tailWord_4936705
  simp only [CollatzResearch.WordTrace]
  refine ⟨180056423580168381934731569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120037615720112254623154379 180056423580168381934731569)
  ·
    refine ⟨135042317685126286451048677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180056423580168381934731569 135042317685126286451048677)
    ·
      refine ⟨25320434565961178709571627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135042317685126286451048677 25320434565961178709571627)
      ·
        refine ⟨37980651848941768064357441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25320434565961178709571627 37980651848941768064357441)
        ·
          refine ⟨28485488886706326048268081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37980651848941768064357441 28485488886706326048268081)
          ·
            refine ⟨21364116665029744536201061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28485488886706326048268081 21364116665029744536201061)
            ·
              refine ⟨4005771874693077100537699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21364116665029744536201061 4005771874693077100537699)
              ·
                refine ⟨6008657812039615650806549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4005771874693077100537699 6008657812039615650806549)
                ·
                  refine ⟨281655834939356983631557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6008657812039615650806549 281655834939356983631557)
                  ·
                    rfl

theorem cell23_4936705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 6].length) (baseStart_4936705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936705 prefixEnd_4936705 := by exact prefixLift 4936705
  have htrace : WordTrace (prefixWord ++ tailWord_4936705) baseStart_4936705 baseEnd_4936705 := by
    simpa [prefixWord, tailWord_4936705, baseEnd_4936705] using wordTrace_append hprefix tailTrace_4936705
  have hstable : (prefixWord ++ tailWord_4936705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936705).length < 2 ^ (prefixWord ++ tailWord_4936705).sum := by decide
  have hdescent : baseEnd_4936705 < baseStart_4936705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936765 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_4936765 : Nat := 118140960795 + 4936765 * 2 ^ 59
def prefixEnd_4936765 : Nat := 4983230072969 + 3 ^ 40 * 4936765 * 2
def baseEnd_4936765 : Nat := 844977774431160872644579

theorem tailTrace_4936765 : CollatzResearch.WordTrace tailWord_4936765 prefixEnd_4936765 844977774431160872644579 := by
  unfold tailWord_4936765
  simp only [CollatzResearch.WordTrace]
  refine ⟨180058611959951012181915749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120039074639967341454610499 180058611959951012181915749)
  ·
    refine ⟨33760989742490814784109203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180058611959951012181915749 33760989742490814784109203)
    ·
      refine ⟨50641484613736222176163805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33760989742490814784109203 50641484613736222176163805)
      ·
        refine ⟨18990556730151083316061427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50641484613736222176163805 18990556730151083316061427)
        ·
          refine ⟨28485835095226624974092141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18990556730151083316061427 28485835095226624974092141)
          ·
            refine ⟨10682188160709984365284553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28485835095226624974092141 10682188160709984365284553)
            ·
              refine ⟨8011641120532488273963415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10682188160709984365284553 8011641120532488273963415)
              ·
                refine ⟨12017461680798732410945123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8011641120532488273963415 12017461680798732410945123)
                ·
                  refine ⟨18026192521198098616417685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12017461680798732410945123 18026192521198098616417685)
                  ·
                    refine ⟨844977774431160872644579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18026192521198098616417685 844977774431160872644579)
                    ·
                      rfl

theorem cell23_4936765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_4936765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936765 prefixEnd_4936765 := by exact prefixLift 4936765
  have htrace : WordTrace (prefixWord ++ tailWord_4936765) baseStart_4936765 baseEnd_4936765 := by
    simpa [prefixWord, tailWord_4936765, baseEnd_4936765] using wordTrace_append hprefix tailTrace_4936765
  have hstable : (prefixWord ++ tailWord_4936765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936765).length < 2 ^ (prefixWord ++ tailWord_4936765).sum := by decide
  have hdescent : baseEnd_4936765 < baseStart_4936765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936775 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_4936775 : Nat := 118140960795 + 4936775 * 2 ^ 59
def prefixEnd_4936775 : Nat := 4983230072969 + 3 ^ 40 * 4936775 * 2
def baseEnd_4936775 : Nat := 2534938458100027578808691

theorem tailTrace_4936775 : CollatzResearch.WordTrace tailWord_4936775 prefixEnd_4936775 2534938458100027578808691 := by
  unfold tailWord_4936775
  simp only [CollatzResearch.WordTrace]
  refine ⟨180058976689914783889779779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120039317793276522593186519 180058976689914783889779779)
  ·
    refine ⟨270088465034872175834669669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180058976689914783889779779 270088465034872175834669669)
    ·
      refine ⟨50641587194038532969000563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270088465034872175834669669 50641587194038532969000563)
      ·
        refine ⟨75962380791057799453500845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50641587194038532969000563 75962380791057799453500845)
        ·
          refine ⟨28485892796646674795062817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75962380791057799453500845 28485892796646674795062817)
          ·
            refine ⟨21364419597485006096297113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28485892796646674795062817 21364419597485006096297113)
            ·
              refine ⟨16023314698113754572222835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21364419597485006096297113 16023314698113754572222835)
              ·
                refine ⟨24034972047170631858334253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16023314698113754572222835 24034972047170631858334253)
                ·
                  refine ⟨9013114517688986946875345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24034972047170631858334253 9013114517688986946875345)
                  ·
                    refine ⟨6759835888266740210156509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9013114517688986946875345 6759835888266740210156509)
                    ·
                      refine ⟨2534938458100027578808691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6759835888266740210156509 2534938458100027578808691)
                      ·
                        rfl

theorem cell23_4936775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_4936775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936775 prefixEnd_4936775 := by exact prefixLift 4936775
  have htrace : WordTrace (prefixWord ++ tailWord_4936775) baseStart_4936775 baseEnd_4936775 := by
    simpa [prefixWord, tailWord_4936775, baseEnd_4936775] using wordTrace_append hprefix tailTrace_4936775
  have hstable : (prefixWord ++ tailWord_4936775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936775).length < 2 ^ (prefixWord ++ tailWord_4936775).sum := by decide
  have hdescent : baseEnd_4936775 < baseStart_4936775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936832 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 1, 3, 2]
def baseStart_4936832 : Nat := 118140960795 + 4936832 * 2 ^ 59
def prefixEnd_4936832 : Nat := 4983230072969 + 3 ^ 40 * 4936832 * 2
def baseEnd_4936832 : Nat := 2534967726497333855795929

theorem tailTrace_4936832 : CollatzResearch.WordTrace tailWord_4936832 prefixEnd_4936832 2534967726497333855795929 := by
  unfold tailWord_4936832
  simp only [CollatzResearch.WordTrace]
  refine ⟨90030527825354141312302375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120040703767138855083069833 90030527825354141312302375)
  ·
    refine ⟨135045791738031211968453563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90030527825354141312302375 135045791738031211968453563)
    ·
      refine ⟨202568687607046817952680345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135045791738031211968453563 202568687607046817952680345)
      ·
        refine ⟨151926515705285113464510259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202568687607046817952680345 151926515705285113464510259)
        ·
          refine ⟨227889773557927670196765389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151926515705285113464510259 227889773557927670196765389)
          ·
            refine ⟨85458665084222876323787021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227889773557927670196765389 85458665084222876323787021)
            ·
              refine ⟨32046999406583578621420133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85458665084222876323787021 32046999406583578621420133)
              ·
                refine ⟨6008812388734420991516275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32046999406583578621420133 6008812388734420991516275)
                ·
                  refine ⟨9013218583101631487274413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6008812388734420991516275 9013218583101631487274413)
                  ·
                    refine ⟨3379956968663111807727905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9013218583101631487274413 3379956968663111807727905)
                    ·
                      refine ⟨2534967726497333855795929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379956968663111807727905 2534967726497333855795929)
                      ·
                        rfl

theorem cell23_4936832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_4936832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936832 prefixEnd_4936832 := by exact prefixLift 4936832
  have htrace : WordTrace (prefixWord ++ tailWord_4936832) baseStart_4936832 baseEnd_4936832 := by
    simpa [prefixWord, tailWord_4936832, baseEnd_4936832] using wordTrace_append hprefix tailTrace_4936832
  have hstable : (prefixWord ++ tailWord_4936832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936832).length < 2 ^ (prefixWord ++ tailWord_4936832).sum := by decide
  have hdescent : baseEnd_4936832 < baseStart_4936832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936840 : List Nat := [2, 1, 3, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4936840 : Nat := 118140960795 + 4936840 * 2 ^ 59
def prefixEnd_4936840 : Nat := 4983230072969 + 3 ^ 40 * 4936840 * 2
def baseEnd_4936840 : Nat := 2534971834342569824495893

theorem tailTrace_4936840 : CollatzResearch.WordTrace tailWord_4936840 prefixEnd_4936840 2534971834342569824495893 := by
  unfold tailWord_4936840
  simp only [CollatzResearch.WordTrace]
  refine ⟨90030673717339649995447987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120040898289786199993930649 90030673717339649995447987)
  ·
    refine ⟨135046010576009474993171981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90030673717339649995447987 135046010576009474993171981)
    ·
      refine ⟨50642253966003553122439493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135046010576009474993171981 50642253966003553122439493)
      ·
        refine ⟨9495422618625666210457405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50642253966003553122439493 9495422618625666210457405)
        ·
          refine ⟨3560783481984624828921527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9495422618625666210457405 3560783481984624828921527)
          ·
            refine ⟨5341175222976937243382291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560783481984624828921527 5341175222976937243382291)
            ·
              refine ⟨8011762834465405865073437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341175222976937243382291 8011762834465405865073437)
              ·
                refine ⟨3004411062924527199402539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8011762834465405865073437 3004411062924527199402539)
                ·
                  refine ⟨4506616594386790799103809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004411062924527199402539 4506616594386790799103809)
                  ·
                    refine ⟨3379962445790093099327857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4506616594386790799103809 3379962445790093099327857)
                    ·
                      refine ⟨2534971834342569824495893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3379962445790093099327857 2534971834342569824495893)
                      ·
                        rfl

theorem cell23_4936840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4936840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936840 prefixEnd_4936840 := by exact prefixLift 4936840
  have htrace : WordTrace (prefixWord ++ tailWord_4936840) baseStart_4936840 baseEnd_4936840 := by
    simpa [prefixWord, tailWord_4936840, baseEnd_4936840] using wordTrace_append hprefix tailTrace_4936840
  have hstable : (prefixWord ++ tailWord_4936840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936840).length < 2 ^ (prefixWord ++ tailWord_4936840).sum := by decide
  have hdescent : baseEnd_4936840 < baseStart_4936840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4936865 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4936865 : Nat := 118140960795 + 4936865 * 2 ^ 59
def prefixEnd_4936865 : Nat := 4983230072969 + 3 ^ 40 * 4936865 * 2
def baseEnd_4936865 : Nat := 2534984671358932226683277

theorem tailTrace_4936865 : CollatzResearch.WordTrace tailWord_4936865 prefixEnd_4936865 2534984671358932226683277 := by
  unfold tailWord_4936865
  simp only [CollatzResearch.WordTrace]
  refine ⟨180062259259588729260556049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120041506173059152840370699 180062259259588729260556049)
  ·
    refine ⟨135046694444691546945417037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180062259259588729260556049 135046694444691546945417037)
    ·
      refine ⟨50642510416759330104531389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135046694444691546945417037 50642510416759330104531389)
      ·
        refine ⟨18990941406284748789199271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50642510416759330104531389 18990941406284748789199271)
        ·
          refine ⟨28486412109427123183798907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18990941406284748789199271 28486412109427123183798907)
          ·
            refine ⟨42729618164140684775698361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28486412109427123183798907 42729618164140684775698361)
            ·
              refine ⟨32047213623105513581773771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42729618164140684775698361 32047213623105513581773771)
              ·
                refine ⟨48070820434658270372660657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32047213623105513581773771 48070820434658270372660657)
                ·
                  refine ⟨36053115325993702779495493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48070820434658270372660657 36053115325993702779495493)
                  ·
                    refine ⟨6759959123623819271155405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36053115325993702779495493 6759959123623819271155405)
                    ·
                      refine ⟨2534984671358932226683277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6759959123623819271155405 2534984671358932226683277)
                      ·
                        rfl

theorem cell23_4936865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4936865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4936865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4936865 prefixEnd_4936865 := by exact prefixLift 4936865
  have htrace : WordTrace (prefixWord ++ tailWord_4936865) baseStart_4936865 baseEnd_4936865 := by
    simpa [prefixWord, tailWord_4936865, baseEnd_4936865] using wordTrace_append hprefix tailTrace_4936865
  have hstable : (prefixWord ++ tailWord_4936865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4936865).length < 2 ^ (prefixWord ++ tailWord_4936865).sum := by decide
  have hdescent : baseEnd_4936865 < baseStart_4936865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4936865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937030 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_4937030 : Nat := 118140960795 + 4937030 * 2 ^ 59
def prefixEnd_4937030 : Nat := 4983230072969 + 3 ^ 40 * 4937030 * 2
def baseEnd_4937030 : Nat := 845023131888974693706673

theorem tailTrace_4937030 : CollatzResearch.WordTrace tailWord_4937030 prefixEnd_4937030 845023131888974693706673 := by
  unfold tailWord_4937030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627133665749717576259767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120045518202660641626875029 5627133665749717576259767)
  ·
    refine ⟨8440700498624576364389651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5627133665749717576259767 8440700498624576364389651)
    ·
      refine ⟨12661050747936864546584477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8440700498624576364389651 12661050747936864546584477)
      ·
        refine ⟨4747894030476324204969179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12661050747936864546584477 4747894030476324204969179)
        ·
          refine ⟨7121841045714486307453769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4747894030476324204969179 7121841045714486307453769)
          ·
            refine ⟨5341380784285864730590327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7121841045714486307453769 5341380784285864730590327)
            ·
              refine ⟨8012071176428797095885491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341380784285864730590327 8012071176428797095885491)
              ·
                refine ⟨12018106764643195643828237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8012071176428797095885491 12018106764643195643828237)
                ·
                  refine ⟨4506790036741198366435589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12018106764643195643828237 4506790036741198366435589)
                  ·
                    refine ⟨845023131888974693706673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4506790036741198366435589 845023131888974693706673)
                    ·
                      rfl

theorem cell23_4937030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_4937030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937030 prefixEnd_4937030 := by exact prefixLift 4937030
  have htrace : WordTrace (prefixWord ++ tailWord_4937030) baseStart_4937030 baseEnd_4937030 := by
    simpa [prefixWord, tailWord_4937030, baseEnd_4937030] using wordTrace_append hprefix tailTrace_4937030
  have hstable : (prefixWord ++ tailWord_4937030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937030).length < 2 ^ (prefixWord ++ tailWord_4937030).sum := by decide
  have hdescent : baseEnd_4937030 < baseStart_4937030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937036 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_4937036 : Nat := 118140960795 + 4937036 * 2 ^ 59
def prefixEnd_4937036 : Nat := 4983230072969 + 3 ^ 40 * 4937036 * 2
def baseEnd_4937036 : Nat := 2535072476550851057644991

theorem tailTrace_4937036 : CollatzResearch.WordTrace tailWord_4937036 prefixEnd_4937036 2535072476550851057644991 := by
  unfold tailWord_4937036
  simp only [CollatzResearch.WordTrace]
  refine ⟨90034248070984612732515481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120045664094646150310020641 90034248070984612732515481)
  ·
    refine ⟨67525686053238459549386611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90034248070984612732515481 67525686053238459549386611)
    ·
      refine ⟨101288529079857689324079917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67525686053238459549386611 101288529079857689324079917)
      ·
        refine ⟨37983198404946633496529969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101288529079857689324079917 37983198404946633496529969)
        ·
          refine ⟨28487398803709975122397477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37983198404946633496529969 28487398803709975122397477)
          ·
            refine ⟨5341387275695620335449527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28487398803709975122397477 5341387275695620335449527)
            ·
              refine ⟨8012080913543430503174291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341387275695620335449527 8012080913543430503174291)
              ·
                refine ⟨12018121370315145754761437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8012080913543430503174291 12018121370315145754761437)
                ·
                  refine ⟨4506795513868179658035539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12018121370315145754761437 4506795513868179658035539)
                  ·
                    refine ⟨6760193270802269487053309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4506795513868179658035539 6760193270802269487053309)
                    ·
                      refine ⟨2535072476550851057644991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6760193270802269487053309 2535072476550851057644991)
                      ·
                        rfl

theorem cell23_4937036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_4937036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937036 prefixEnd_4937036 := by exact prefixLift 4937036
  have htrace : WordTrace (prefixWord ++ tailWord_4937036) baseStart_4937036 baseEnd_4937036 := by
    simpa [prefixWord, tailWord_4937036, baseEnd_4937036] using wordTrace_append hprefix tailTrace_4937036
  have hstable : (prefixWord ++ tailWord_4937036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937036).length < 2 ^ (prefixWord ++ tailWord_4937036).sum := by decide
  have hdescent : baseEnd_4937036 < baseStart_4937036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937042 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_4937042 : Nat := 118140960795 + 4937042 * 2 ^ 59
def prefixEnd_4937042 : Nat := 4983230072969 + 3 ^ 40 * 4937042 * 2
def baseEnd_4937042 : Nat := 2535075557434778034169963

theorem tailTrace_4937042 : CollatzResearch.WordTrace tailWord_4937042 prefixEnd_4937042 2535075557434778034169963 := by
  unfold tailWord_4937042
  simp only [CollatzResearch.WordTrace]
  refine ⟨45017178744986872122437345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120045809986631658993166253 45017178744986872122437345)
  ·
    refine ⟨33762884058740154091828009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45017178744986872122437345 33762884058740154091828009)
    ·
      refine ⟨25322163044055115568871007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33762884058740154091828009 25322163044055115568871007)
      ·
        refine ⟨37983244566082673353306511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25322163044055115568871007 37983244566082673353306511)
        ·
          refine ⟨56974866849124010029959767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37983244566082673353306511 56974866849124010029959767)
          ·
            refine ⟨85462300273686015044939651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56974866849124010029959767 85462300273686015044939651)
            ·
              refine ⟨128193450410529022567409477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85462300273686015044939651 128193450410529022567409477)
              ·
                refine ⟨24036271951974191731389277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128193450410529022567409477 24036271951974191731389277)
                ·
                  refine ⟨9013601981990321899270979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24036271951974191731389277 9013601981990321899270979)
                  ·
                    refine ⟨13520402972985482848906469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9013601981990321899270979 13520402972985482848906469)
                    ·
                      refine ⟨2535075557434778034169963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13520402972985482848906469 2535075557434778034169963)
                      ·
                        rfl

theorem cell23_4937042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_4937042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937042 prefixEnd_4937042 := by exact prefixLift 4937042
  have htrace : WordTrace (prefixWord ++ tailWord_4937042) baseStart_4937042 baseEnd_4937042 := by
    simpa [prefixWord, tailWord_4937042, baseEnd_4937042] using wordTrace_append hprefix tailTrace_4937042
  have hstable : (prefixWord ++ tailWord_4937042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937042).length < 2 ^ (prefixWord ++ tailWord_4937042).sum := by decide
  have hdescent : baseEnd_4937042 < baseStart_4937042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937059 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 4]
def baseStart_4937059 : Nat := 118140960795 + 4937059 * 2 ^ 59
def prefixEnd_4937059 : Nat := 4983230072969 + 3 ^ 40 * 4937059 * 2
def baseEnd_4937059 : Nat := 2535084286605904467657385

theorem tailTrace_4937059 : CollatzResearch.WordTrace tailWord_4937059 prefixEnd_4937059 2535084286605904467657385 := by
  unfold tailWord_4937059
  simp only [CollatzResearch.WordTrace]
  refine ⟨180069335020885900393118231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120046223347257266928745487 180069335020885900393118231)
  ·
    refine ⟨270104002531328850589677347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180069335020885900393118231 270104002531328850589677347)
    ·
      refine ⟨405156003796993275884516021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270104002531328850589677347 405156003796993275884516021)
      ·
        refine ⟨37983375355968119614173377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 405156003796993275884516021 37983375355968119614173377)
        ·
          refine ⟨28487531516976089710630033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37983375355968119614173377 28487531516976089710630033)
          ·
            refine ⟨21365648637732067282972525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28487531516976089710630033 21365648637732067282972525)
            ·
              refine ⟨8012118239149525231114697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21365648637732067282972525 8012118239149525231114697)
              ·
                refine ⟨6009088679362143923336023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8012118239149525231114697 6009088679362143923336023)
                ·
                  refine ⟨9013633019043215885004035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009088679362143923336023 9013633019043215885004035)
                  ·
                    refine ⟨13520449528564823827506053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9013633019043215885004035 13520449528564823827506053)
                    ·
                      refine ⟨2535084286605904467657385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13520449528564823827506053 2535084286605904467657385)
                      ·
                        rfl

theorem cell23_4937059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_4937059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937059 prefixEnd_4937059 := by exact prefixLift 4937059
  have htrace : WordTrace (prefixWord ++ tailWord_4937059) baseStart_4937059 baseEnd_4937059 := by
    simpa [prefixWord, tailWord_4937059, baseEnd_4937059] using wordTrace_append hprefix tailTrace_4937059
  have hstable : (prefixWord ++ tailWord_4937059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937059).length < 2 ^ (prefixWord ++ tailWord_4937059).sum := by decide
  have hdescent : baseEnd_4937059 < baseStart_4937059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937072 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_4937072 : Nat := 118140960795 + 4937072 * 2 ^ 59
def prefixEnd_4937072 : Nat := 4983230072969 + 3 ^ 40 * 4937072 * 2
def baseEnd_4937072 : Nat := 2535090961854412916794825

theorem tailTrace_4937072 : CollatzResearch.WordTrace tailWord_4937072 prefixEnd_4937072 2535090961854412916794825 := by
  unfold tailWord_4937072
  simp only [CollatzResearch.WordTrace]
  refine ⟨90034904584919401806670735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120046539446559202408894313 90034904584919401806670735)
  ·
    refine ⟨135052356877379102710006103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90034904584919401806670735 135052356877379102710006103)
    ·
      refine ⟨202578535316068654065009155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135052356877379102710006103 202578535316068654065009155)
      ·
        refine ⟨303867802974102981097513733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202578535316068654065009155 303867802974102981097513733)
        ·
          refine ⟨56975213057644308955783825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303867802974102981097513733 56975213057644308955783825)
          ·
            refine ⟨42731409793233231716837869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56975213057644308955783825 42731409793233231716837869)
            ·
              refine ⟨16024278672462461893814201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42731409793233231716837869 16024278672462461893814201)
              ·
                refine ⟨12018209004346846420360651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16024278672462461893814201 12018209004346846420360651)
                ·
                  refine ⟨18027313506520269630540977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12018209004346846420360651 18027313506520269630540977)
                  ·
                    refine ⟨13520485129890202222905733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18027313506520269630540977 13520485129890202222905733)
                    ·
                      refine ⟨2535090961854412916794825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13520485129890202222905733 2535090961854412916794825)
                      ·
                        rfl

theorem cell23_4937072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_4937072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937072 prefixEnd_4937072 := by exact prefixLift 4937072
  have htrace : WordTrace (prefixWord ++ tailWord_4937072) baseStart_4937072 baseEnd_4937072 := by
    simpa [prefixWord, tailWord_4937072, baseEnd_4937072] using wordTrace_append hprefix tailTrace_4937072
  have hstable : (prefixWord ++ tailWord_4937072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937072).length < 2 ^ (prefixWord ++ tailWord_4937072).sum := by decide
  have hdescent : baseEnd_4937072 < baseStart_4937072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937116 : List Nat := [2, 2, 3, 4, 1, 1, 3, 7]
def baseStart_4937116 : Nat := 118140960795 + 4937116 * 2 ^ 59
def prefixEnd_4937116 : Nat := 4983230072969 + 3 ^ 40 * 4937116 * 2
def baseEnd_4937116 : Nat := 93893094629748546097949

theorem tailTrace_4937116 : CollatzResearch.WordTrace tailWord_4937116 prefixEnd_4937116 93893094629748546097949 := by
  unfold tailWord_4937116
  simp only [CollatzResearch.WordTrace]
  refine ⟨90035706990839699563971601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120047609321119599418628801 90035706990839699563971601)
  ·
    refine ⟨67526780243129774672978701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90035706990839699563971601 67526780243129774672978701)
    ·
      refine ⟨25322542591173665502367013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67526780243129774672978701 25322542591173665502367013)
      ·
        refine ⟨4747976735845062281693815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25322542591173665502367013 4747976735845062281693815)
        ·
          refine ⟨7121965103767593422540723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4747976735845062281693815 7121965103767593422540723)
          ·
            refine ⟨10682947655651390133811085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7121965103767593422540723 10682947655651390133811085)
            ·
              refine ⟨4006105370869271300179157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10682947655651390133811085 4006105370869271300179157)
              ·
                refine ⟨93893094629748546097949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4006105370869271300179157 93893094629748546097949)
                ·
                  rfl

theorem cell23_4937116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 7].length) (baseStart_4937116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937116 prefixEnd_4937116 := by exact prefixLift 4937116
  have htrace : WordTrace (prefixWord ++ tailWord_4937116) baseStart_4937116 baseEnd_4937116 := by
    simpa [prefixWord, tailWord_4937116, baseEnd_4937116] using wordTrace_append hprefix tailTrace_4937116
  have hstable : (prefixWord ++ tailWord_4937116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937116).length < 2 ^ (prefixWord ++ tailWord_4937116).sum := by decide
  have hdescent : baseEnd_4937116 < baseStart_4937116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937152 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 3]
def baseStart_4937152 : Nat := 118140960795 + 4937152 * 2 ^ 59
def prefixEnd_4937152 : Nat := 4983230072969 + 3 ^ 40 * 4937152 * 2
def baseEnd_4937152 : Nat := 2535132040306772603794457

theorem tailTrace_4937152 : CollatzResearch.WordTrace tailWord_4937152 prefixEnd_4937152 2535132040306772603794457 := by
  unfold tailWord_4937152
  simp only [CollatzResearch.WordTrace]
  refine ⟨90036363504774488638126855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120048484673032651517502473 90036363504774488638126855)
  ·
    refine ⟨135054545257161732957190283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90036363504774488638126855 135054545257161732957190283)
    ·
      refine ⟨202581817885742599435785425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135054545257161732957190283 202581817885742599435785425)
      ·
        refine ⟨151936363414306949576839069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202581817885742599435785425 151936363414306949576839069)
        ·
          refine ⟨56976136280365106091314651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151936363414306949576839069 56976136280365106091314651)
          ·
            refine ⟨85464204420547659136971977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56976136280365106091314651 85464204420547659136971977)
            ·
              refine ⟨64098153315410744352728983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85464204420547659136971977 64098153315410744352728983)
              ·
                refine ⟨96147229973116116529093475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64098153315410744352728983 96147229973116116529093475)
                ·
                  refine ⟨144220844959674174793640213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96147229973116116529093475 144220844959674174793640213)
                  ·
                    refine ⟨6760352107484726943451885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 144220844959674174793640213 6760352107484726943451885)
                    ·
                      refine ⟨2535132040306772603794457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6760352107484726943451885 2535132040306772603794457)
                      ·
                        rfl

theorem cell23_4937152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_4937152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937152 prefixEnd_4937152 := by exact prefixLift 4937152
  have htrace : WordTrace (prefixWord ++ tailWord_4937152) baseStart_4937152 baseEnd_4937152 := by
    simpa [prefixWord, tailWord_4937152, baseEnd_4937152] using wordTrace_append hprefix tailTrace_4937152
  have hstable : (prefixWord ++ tailWord_4937152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937152).length < 2 ^ (prefixWord ++ tailWord_4937152).sum := by decide
  have hdescent : baseEnd_4937152 < baseStart_4937152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937154 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4937154 : Nat := 118140960795 + 4937154 * 2 ^ 59
def prefixEnd_4937154 : Nat := 4983230072969 + 3 ^ 40 * 4937154 * 2
def baseEnd_4937154 : Nat := 845044355756027198656483

theorem tailTrace_4937154 : CollatzResearch.WordTrace tailWord_4937154 prefixEnd_4937154 845044355756027198656483 := by
  unfold tailWord_4937154
  simp only [CollatzResearch.WordTrace]
  refine ⟨45018199988885432904456629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120048533303694487745217677 45018199988885432904456629)
  ·
    refine ⟨4220456248958009334792809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45018199988885432904456629 4220456248958009334792809)
    ·
      refine ⟨3165342186718507001094607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4220456248958009334792809 3165342186718507001094607)
      ·
        refine ⟨4748013280077760501641911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3165342186718507001094607 4748013280077760501641911)
        ·
          refine ⟨7122019920116640752462867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4748013280077760501641911 7122019920116640752462867)
          ·
            refine ⟨10683029880174961128694301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7122019920116640752462867 10683029880174961128694301)
            ·
              refine ⟨4006136205065610423260363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10683029880174961128694301 4006136205065610423260363)
              ·
                refine ⟨6009204307598415634890545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006136205065610423260363 6009204307598415634890545)
                ·
                  refine ⟨4506903230698811726167909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6009204307598415634890545 4506903230698811726167909)
                  ·
                    refine ⟨845044355756027198656483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4506903230698811726167909 845044355756027198656483)
                    ·
                      rfl

theorem cell23_4937154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4937154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937154 prefixEnd_4937154 := by exact prefixLift 4937154
  have htrace : WordTrace (prefixWord ++ tailWord_4937154) baseStart_4937154 baseEnd_4937154 := by
    simpa [prefixWord, tailWord_4937154, baseEnd_4937154] using wordTrace_append hprefix tailTrace_4937154
  have hstable : (prefixWord ++ tailWord_4937154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937154).length < 2 ^ (prefixWord ++ tailWord_4937154).sum := by decide
  have hdescent : baseEnd_4937154 < baseStart_4937154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937166 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_4937166 : Nat := 118140960795 + 4937166 * 2 ^ 59
def prefixEnd_4937166 : Nat := 4983230072969 + 3 ^ 40 * 4937166 * 2
def baseEnd_4937166 : Nat := 2535139229035935549019393

theorem tailTrace_4937166 : CollatzResearch.WordTrace tailWord_4937166 prefixEnd_4937166 2535139229035935549019393 := by
  unfold tailWord_4937166
  simp only [CollatzResearch.WordTrace]
  refine ⟨22509154703937282208407919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120048825087665505111508901 22509154703937282208407919)
  ·
    refine ⟨33763732055905923312611879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22509154703937282208407919 33763732055905923312611879)
    ·
      refine ⟨50645598083858884968917819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33763732055905923312611879 50645598083858884968917819)
      ·
        refine ⟨75968397125788327453376729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50645598083858884968917819 75968397125788327453376729)
        ·
          refine ⟨56976297844341245590032547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75968397125788327453376729 56976297844341245590032547)
          ·
            refine ⟨85464446766511868385048821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56976297844341245590032547 85464446766511868385048821)
            ·
              refine ⟨8012291884360487661098327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85464446766511868385048821 8012291884360487661098327)
              ·
                refine ⟨12018437826540731491647491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8012291884360487661098327 12018437826540731491647491)
                ·
                  refine ⟨18027656739811097237471237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12018437826540731491647491 18027656739811097237471237)
                  ·
                    refine ⟨3380185638714580732025857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18027656739811097237471237 3380185638714580732025857)
                    ·
                      refine ⟨2535139229035935549019393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380185638714580732025857 2535139229035935549019393)
                      ·
                        rfl

theorem cell23_4937166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_4937166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937166 prefixEnd_4937166 := by exact prefixLift 4937166
  have htrace : WordTrace (prefixWord ++ tailWord_4937166) baseStart_4937166 baseEnd_4937166 := by
    simpa [prefixWord, tailWord_4937166, baseEnd_4937166] using wordTrace_append hprefix tailTrace_4937166
  have hstable : (prefixWord ++ tailWord_4937166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937166).length < 2 ^ (prefixWord ++ tailWord_4937166).sum := by decide
  have hdescent : baseEnd_4937166 < baseStart_4937166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937206 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_4937206 : Nat := 118140960795 + 4937206 * 2 ^ 59
def prefixEnd_4937206 : Nat := 4983230072969 + 3 ^ 40 * 4937206 * 2
def baseEnd_4937206 : Nat := 281684418695790599168801

theorem tailTrace_4937206 : CollatzResearch.WordTrace tailWord_4937206 prefixEnd_4937206 281684418695790599168801 := by
  unfold tailWord_4937206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11254668534459584031169967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120049797700902229665812981 11254668534459584031169967)
  ·
    refine ⟨16882002801689376046754951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11254668534459584031169967 16882002801689376046754951)
    ·
      refine ⟨25323004202534064070132427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16882002801689376046754951 25323004202534064070132427)
      ·
        refine ⟨37984506303801096105198641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25323004202534064070132427 37984506303801096105198641)
        ·
          refine ⟨28488379727850822078898981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37984506303801096105198641 28488379727850822078898981)
          ·
            refine ⟨5341571198972029139793559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28488379727850822078898981 5341571198972029139793559)
            ·
              refine ⟨8012356798458043709690339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341571198972029139793559 8012356798458043709690339)
              ·
                refine ⟨12018535197687065564535509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8012356798458043709690339 12018535197687065564535509)
                ·
                  refine ⟨281684418695790599168801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12018535197687065564535509 281684418695790599168801)
                  ·
                    rfl

theorem cell23_4937206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_4937206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937206 prefixEnd_4937206 := by exact prefixLift 4937206
  have htrace : WordTrace (prefixWord ++ tailWord_4937206) baseStart_4937206 baseEnd_4937206 := by
    simpa [prefixWord, tailWord_4937206, baseEnd_4937206] using wordTrace_append hprefix tailTrace_4937206
  have hstable : (prefixWord ++ tailWord_4937206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937206).length < 2 ^ (prefixWord ++ tailWord_4937206).sum := by decide
  have hdescent : baseEnd_4937206 < baseStart_4937206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937209 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 2, 5, 2]
def baseStart_4937209 : Nat := 118140960795 + 4937209 * 2 ^ 59
def prefixEnd_4937209 : Nat := 4983230072969 + 3 ^ 40 * 4937209 * 2
def baseEnd_4937209 : Nat := 2535161308704078880781695

theorem tailTrace_4937209 : CollatzResearch.WordTrace tailWord_4937209 prefixEnd_4937209 2535161308704078880781695 := by
  unfold tailWord_4937209
  simp only [CollatzResearch.WordTrace]
  refine ⟨180074805970342476011078681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120049870646894984007385787 180074805970342476011078681)
  ·
    refine ⟨135056104477756857008309011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180074805970342476011078681 135056104477756857008309011)
    ·
      refine ⟨202584156716635285512463517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135056104477756857008309011 202584156716635285512463517)
      ·
        refine ⟨75969058768738232067173819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202584156716635285512463517 75969058768738232067173819)
        ·
          refine ⟨113953588153107348100760729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75969058768738232067173819 113953588153107348100760729)
          ·
            refine ⟨85465191114830511075570547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113953588153107348100760729 85465191114830511075570547)
            ·
              refine ⟨128197786672245766613355821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85465191114830511075570547 128197786672245766613355821)
              ·
                refine ⟨48074170002092162480008433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128197786672245766613355821 48074170002092162480008433)
                ·
                  refine ⟨36055627501569121860006325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48074170002092162480008433 36055627501569121860006325)
                  ·
                    refine ⟨3380215078272105174375593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36055627501569121860006325 3380215078272105174375593)
                    ·
                      refine ⟨2535161308704078880781695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380215078272105174375593 2535161308704078880781695)
                      ·
                        rfl

theorem cell23_4937209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_4937209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937209 prefixEnd_4937209 := by exact prefixLift 4937209
  have htrace : WordTrace (prefixWord ++ tailWord_4937209) baseStart_4937209 baseEnd_4937209 := by
    simpa [prefixWord, tailWord_4937209, baseEnd_4937209] using wordTrace_append hprefix tailTrace_4937209
  have hstable : (prefixWord ++ tailWord_4937209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937209).length < 2 ^ (prefixWord ++ tailWord_4937209).sum := by decide
  have hdescent : baseEnd_4937209 < baseStart_4937209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937212 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_4937212 : Nat := 118140960795 + 4937212 * 2 ^ 59
def prefixEnd_4937212 : Nat := 4983230072969 + 3 ^ 40 * 4937212 * 2
def baseEnd_4937212 : Nat := 2535162849146042369044181

theorem tailTrace_4937212 : CollatzResearch.WordTrace tailWord_4937212 prefixEnd_4937212 2535162849146042369044181 := by
  unfold tailWord_4937212
  simp only [CollatzResearch.WordTrace]
  refine ⟨90037457694665803761718945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120049943592887738348958593 90037457694665803761718945)
  ·
    refine ⟨67528093270999352821289209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90037457694665803761718945 67528093270999352821289209)
    ·
      refine ⟨50646069953249514615966907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67528093270999352821289209 50646069953249514615966907)
      ·
        refine ⟨75969104929874271923950361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50646069953249514615966907 75969104929874271923950361)
        ·
          refine ⟨56976828697405703942962771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75969104929874271923950361 56976828697405703942962771)
          ·
            refine ⟨85465243046108555914444157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56976828697405703942962771 85465243046108555914444157)
            ·
              refine ⟨32049466142290708467916559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85465243046108555914444157 32049466142290708467916559)
              ·
                refine ⟨48074199213436062701874839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32049466142290708467916559 48074199213436062701874839)
                ·
                  refine ⟨72111298820154094052812259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48074199213436062701874839 72111298820154094052812259)
                  ·
                    refine ⟨108166948230231141079218389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72111298820154094052812259 108166948230231141079218389)
                    ·
                      refine ⟨2535162849146042369044181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108166948230231141079218389 2535162849146042369044181)
                      ·
                        rfl

theorem cell23_4937212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_4937212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937212 prefixEnd_4937212 := by exact prefixLift 4937212
  have htrace : WordTrace (prefixWord ++ tailWord_4937212) baseStart_4937212 baseEnd_4937212 := by
    simpa [prefixWord, tailWord_4937212, baseEnd_4937212] using wordTrace_append hprefix tailTrace_4937212
  have hstable : (prefixWord ++ tailWord_4937212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937212).length < 2 ^ (prefixWord ++ tailWord_4937212).sum := by decide
  have hdescent : baseEnd_4937212 < baseStart_4937212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937217 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_4937217 : Nat := 118140960795 + 4937217 * 2 ^ 59
def prefixEnd_4937217 : Nat := 4983230072969 + 3 ^ 40 * 4937217 * 2
def baseEnd_4937217 : Nat := 2535165416549314849481659

theorem tailTrace_4937217 : CollatzResearch.WordTrace tailWord_4937217 prefixEnd_4937217 2535165416549314849481659 := by
  unfold tailWord_4937217
  simp only [CollatzResearch.WordTrace]
  refine ⟨180075097754313493377369905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120050065169542328918246603 180075097754313493377369905)
  ·
    refine ⟨135056323315735120033027429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180075097754313493377369905 135056323315735120033027429)
    ·
      refine ⟨25323060621700335006192643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135056323315735120033027429 25323060621700335006192643)
      ·
        refine ⟨37984590932550502509288965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25323060621700335006192643 37984590932550502509288965)
        ·
          refine ⟨7122110799853219220491681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37984590932550502509288965 7122110799853219220491681)
          ·
            refine ⟨5341583099889914415368761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7122110799853219220491681 5341583099889914415368761)
            ·
              refine ⟨4006187324917435811526571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5341583099889914415368761 4006187324917435811526571)
              ·
                refine ⟨6009280987376153717289857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006187324917435811526571 6009280987376153717289857)
                ·
                  refine ⟨4506960740532115287967393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6009280987376153717289857 4506960740532115287967393)
                  ·
                    refine ⟨3380220555399086465975545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4506960740532115287967393 3380220555399086465975545)
                    ·
                      refine ⟨2535165416549314849481659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380220555399086465975545 2535165416549314849481659)
                      ·
                        rfl

theorem cell23_4937217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_4937217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937217 prefixEnd_4937217 := by exact prefixLift 4937217
  have htrace : WordTrace (prefixWord ++ tailWord_4937217) baseStart_4937217 baseEnd_4937217 := by
    simpa [prefixWord, tailWord_4937217, baseEnd_4937217] using wordTrace_append hprefix tailTrace_4937217
  have hstable : (prefixWord ++ tailWord_4937217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937217).length < 2 ^ (prefixWord ++ tailWord_4937217).sum := by decide
  have hdescent : baseEnd_4937217 < baseStart_4937217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937279 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 6]
def baseStart_4937279 : Nat := 118140960795 + 4937279 * 2 ^ 59
def prefixEnd_4937279 : Nat := 4983230072969 + 3 ^ 40 * 4937279 * 2
def baseEnd_4937279 : Nat := 281688583594432622989597

theorem tailTrace_4937279 : CollatzResearch.WordTrace tailWord_4937279 prefixEnd_4937279 281688583594432622989597 := by
  unfold tailWord_4937279
  simp only [CollatzResearch.WordTrace]
  refine ⟨180077359080088877966126891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120051572720059251977417927 180077359080088877966126891)
  ·
    refine ⟨270116038620133316949190337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180077359080088877966126891 270116038620133316949190337)
    ·
      refine ⟨202587028965099987711892753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270116038620133316949190337 202587028965099987711892753)
      ·
        refine ⟨151940271723824990783919565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202587028965099987711892753 151940271723824990783919565)
        ·
          refine ⟨56977601896434371543969837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151940271723824990783919565 56977601896434371543969837)
          ·
            refine ⟨21366600711162889328988689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56977601896434371543969837 21366600711162889328988689)
            ·
              refine ⟨16024950533372166996741517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21366600711162889328988689 16024950533372166996741517)
              ·
                refine ⟨6009356450014562623778069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16024950533372166996741517 6009356450014562623778069)
                ·
                  refine ⟨281688583594432622989597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6009356450014562623778069 281688583594432622989597)
                  ·
                    rfl

theorem cell23_4937279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 6].length) (baseStart_4937279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937279 prefixEnd_4937279 := by exact prefixLift 4937279
  have htrace : WordTrace (prefixWord ++ tailWord_4937279) baseStart_4937279 baseEnd_4937279 := by
    simpa [prefixWord, tailWord_4937279, baseEnd_4937279] using wordTrace_append hprefix tailTrace_4937279
  have hstable : (prefixWord ++ tailWord_4937279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937279).length < 2 ^ (prefixWord ++ tailWord_4937279).sum := by decide
  have hdescent : baseEnd_4937279 < baseStart_4937279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937293 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_4937293 : Nat := 118140960795 + 4937293 * 2 ^ 59
def prefixEnd_4937293 : Nat := 4983230072969 + 3 ^ 40 * 4937293 * 2
def baseEnd_4937293 : Nat := 2535204441079056552131309

theorem tailTrace_4937293 : CollatzResearch.WordTrace tailWord_4937293 prefixEnd_4937293 2535204441079056552131309 := by
  unfold tailWord_4937293
  simp only [CollatzResearch.WordTrace]
  refine ⟨180077869702038158357136533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120051913134692105571424355 180077869702038158357136533)
  ·
    refine ⟨8441150142283038672990775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 180077869702038158357136533 8441150142283038672990775)
    ·
      refine ⟨12661725213424558009486163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441150142283038672990775 12661725213424558009486163)
      ·
        refine ⟨18992587820136837014229245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12661725213424558009486163 18992587820136837014229245)
        ·
          refine ⟨7122220432551313880335967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18992587820136837014229245 7122220432551313880335967)
          ·
            refine ⟨10683330648826970820503951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7122220432551313880335967 10683330648826970820503951)
            ·
              refine ⟨16024995973240456230755927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10683330648826970820503951 16024995973240456230755927)
              ·
                refine ⟨24037493959860684346133891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16024995973240456230755927 24037493959860684346133891)
                ·
                  refine ⟨36056240939791026519200837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24037493959860684346133891 36056240939791026519200837)
                  ·
                    refine ⟨6760545176210817472350157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36056240939791026519200837 6760545176210817472350157)
                    ·
                      refine ⟨2535204441079056552131309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6760545176210817472350157 2535204441079056552131309)
                      ·
                        rfl

theorem cell23_4937293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_4937293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937293 prefixEnd_4937293 := by exact prefixLift 4937293
  have htrace : WordTrace (prefixWord ++ tailWord_4937293) baseStart_4937293 baseEnd_4937293 := by
    simpa [prefixWord, tailWord_4937293, baseEnd_4937293] using wordTrace_append hprefix tailTrace_4937293
  have hstable : (prefixWord ++ tailWord_4937293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937293).length < 2 ^ (prefixWord ++ tailWord_4937293).sum := by decide
  have hdescent : baseEnd_4937293 < baseStart_4937293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937329 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_4937329 : Nat := 118140960795 + 4937329 * 2 ^ 59
def prefixEnd_4937329 : Nat := 4983230072969 + 3 ^ 40 * 4937329 * 2
def baseEnd_4937329 : Nat := 2535222926382618411281143

theorem tailTrace_4937329 : CollatzResearch.WordTrace tailWord_4937329 prefixEnd_4937329 2535222926382618411281143 := by
  unfold tailWord_4937329
  simp only [CollatzResearch.WordTrace]
  refine ⟨180079182729907736505447041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120052788486605157670298027 180079182729907736505447041)
  ·
    refine ⟨135059387047430802379085281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180079182729907736505447041 135059387047430802379085281)
    ·
      refine ⟨101294540285573101784313961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135059387047430802379085281 101294540285573101784313961)
      ·
        refine ⟨75970905214179826338235471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101294540285573101784313961 75970905214179826338235471)
        ·
          refine ⟨113956357821269739507353207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75970905214179826338235471 113956357821269739507353207)
          ·
            refine ⟨170934536731904609261029811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113956357821269739507353207 170934536731904609261029811)
            ·
              refine ⟨256401805097856913891544717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170934536731904609261029811 256401805097856913891544717)
              ·
                refine ⟨96150676911696342709329269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256401805097856913891544717 96150676911696342709329269)
                ·
                  refine ⟨9014125960471532128999619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96150676911696342709329269 9014125960471532128999619)
                  ·
                    refine ⟨13521188940707298193499429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9014125960471532128999619 13521188940707298193499429)
                    ·
                      refine ⟨2535222926382618411281143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13521188940707298193499429 2535222926382618411281143)
                      ·
                        rfl

theorem cell23_4937329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_4937329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937329 prefixEnd_4937329 := by exact prefixLift 4937329
  have htrace : WordTrace (prefixWord ++ tailWord_4937329) baseStart_4937329 baseEnd_4937329 := by
    simpa [prefixWord, tailWord_4937329, baseEnd_4937329] using wordTrace_append hprefix tailTrace_4937329
  have hstable : (prefixWord ++ tailWord_4937329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937329).length < 2 ^ (prefixWord ++ tailWord_4937329).sum := by decide
  have hdescent : baseEnd_4937329 < baseStart_4937329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937333 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4937333 : Nat := 118140960795 + 4937333 * 2 ^ 59
def prefixEnd_4937333 : Nat := 4983230072969 + 3 ^ 40 * 4937333 * 2
def baseEnd_4937333 : Nat := 2535224980305236395631125

theorem tailTrace_4937333 : CollatzResearch.WordTrace tailWord_4937333 prefixEnd_4937333 2535224980305236395631125 := by
  unfold tailWord_4937333
  simp only [CollatzResearch.WordTrace]
  refine ⟨180079328621893245188592653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120052885747928830125728435 180079328621893245188592653)
  ·
    refine ⟨67529748233209966945722245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180079328621893245188592653 67529748233209966945722245)
    ·
      refine ⟨12661827793726868802322921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67529748233209966945722245 12661827793726868802322921)
      ·
        refine ⟨9496370845295151601742191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12661827793726868802322921 9496370845295151601742191)
        ·
          refine ⟨14244556267942727402613287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9496370845295151601742191 14244556267942727402613287)
          ·
            refine ⟨21366834401914091103919931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14244556267942727402613287 21366834401914091103919931)
            ·
              refine ⟨32050251602871136655879897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21366834401914091103919931 32050251602871136655879897)
              ·
                refine ⟨24037688702153352491909923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32050251602871136655879897 24037688702153352491909923)
                ·
                  refine ⟨36056533053230028737864885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24037688702153352491909923 36056533053230028737864885)
                  ·
                    refine ⟨3380299973740315194174833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36056533053230028737864885 3380299973740315194174833)
                    ·
                      refine ⟨2535224980305236395631125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380299973740315194174833 2535224980305236395631125)
                      ·
                        rfl

theorem cell23_4937333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4937333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937333 prefixEnd_4937333 := by exact prefixLift 4937333
  have htrace : WordTrace (prefixWord ++ tailWord_4937333) baseStart_4937333 baseEnd_4937333 := by
    simpa [prefixWord, tailWord_4937333, baseEnd_4937333] using wordTrace_append hprefix tailTrace_4937333
  have hstable : (prefixWord ++ tailWord_4937333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937333).length < 2 ^ (prefixWord ++ tailWord_4937333).sum := by decide
  have hdescent : baseEnd_4937333 < baseStart_4937333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937349 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_4937349 : Nat := 118140960795 + 4937349 * 2 ^ 59
def prefixEnd_4937349 : Nat := 4983230072969 + 3 ^ 40 * 4937349 * 2
def baseEnd_4937349 : Nat := 2535233195995708333031051

theorem tailTrace_4937349 : CollatzResearch.WordTrace tailWord_4937349 prefixEnd_4937349 2535233195995708333031051 := by
  unfold tailWord_4937349
  simp only [CollatzResearch.WordTrace]
  refine ⟨180079912189835279921175101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120053274793223519947450067 180079912189835279921175101)
  ·
    refine ⟨67529967071188229970440663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180079912189835279921175101 67529967071188229970440663)
    ·
      refine ⟨101294950606782344955660995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67529967071188229970440663 101294950606782344955660995)
      ·
        refine ⟨151942425910173517433491493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101294950606782344955660995 151942425910173517433491493)
        ·
          refine ⟨28489204858157534518779655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151942425910173517433491493 28489204858157534518779655)
          ·
            refine ⟨42733807287236301778169483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28489204858157534518779655 42733807287236301778169483)
            ·
              refine ⟨64100710930854452667254225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42733807287236301778169483 64100710930854452667254225)
              ·
                refine ⟨48075533198140839500440669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64100710930854452667254225 48075533198140839500440669)
                ·
                  refine ⟨18028324949302814812665251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48075533198140839500440669 18028324949302814812665251)
                  ·
                    refine ⟨27042487423954222218997877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18028324949302814812665251 27042487423954222218997877)
                    ·
                      refine ⟨2535233195995708333031051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27042487423954222218997877 2535233195995708333031051)
                      ·
                        rfl

theorem cell23_4937349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_4937349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937349 prefixEnd_4937349 := by exact prefixLift 4937349
  have htrace : WordTrace (prefixWord ++ tailWord_4937349) baseStart_4937349 baseEnd_4937349 := by
    simpa [prefixWord, tailWord_4937349, baseEnd_4937349] using wordTrace_append hprefix tailTrace_4937349
  have hstable : (prefixWord ++ tailWord_4937349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937349).length < 2 ^ (prefixWord ++ tailWord_4937349).sum := by decide
  have hdescent : baseEnd_4937349 < baseStart_4937349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937374 : List Nat := [4, 3, 1, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_4937374 : Nat := 118140960795 + 4937374 * 2 ^ 59
def prefixEnd_4937374 : Nat := 4983230072969 + 3 ^ 40 * 4937374 * 2
def baseEnd_4937374 : Nat := 2535246033012070735218437

theorem tailTrace_4937374 : CollatzResearch.WordTrace tailWord_4937374 prefixEnd_4937374 2535246033012070735218437 := by
  unfold tailWord_4937374
  simp only [CollatzResearch.WordTrace]
  refine ⟨22510103001843088648854397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120053882676496472793890117 22510103001843088648854397)
  ·
    refine ⟨8441288625691158243320399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22510103001843088648854397 8441288625691158243320399)
    ·
      refine ⟨12661932938536737364980599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441288625691158243320399 12661932938536737364980599)
      ·
        refine ⟨18992899407805106047470899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12661932938536737364980599 18992899407805106047470899)
        ·
          refine ⟨28489349111707659071206349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18992899407805106047470899 28489349111707659071206349)
          ·
            refine ⟨10683505916890372151702381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28489349111707659071206349 10683505916890372151702381)
            ·
              refine ⟨4006314718833889556888393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10683505916890372151702381 4006314718833889556888393)
              ·
                refine ⟨3004736039125417167666295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4006314718833889556888393 3004736039125417167666295)
                ·
                  refine ⟨4507104058688125751499443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004736039125417167666295 4507104058688125751499443)
                  ·
                    refine ⟨6760656088032188627249165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4507104058688125751499443 6760656088032188627249165)
                    ·
                      refine ⟨2535246033012070735218437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6760656088032188627249165 2535246033012070735218437)
                      ·
                        rfl

theorem cell23_4937374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_4937374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937374 prefixEnd_4937374 := by exact prefixLift 4937374
  have htrace : WordTrace (prefixWord ++ tailWord_4937374) baseStart_4937374 baseEnd_4937374 := by
    simpa [prefixWord, tailWord_4937374, baseEnd_4937374] using wordTrace_append hprefix tailTrace_4937374
  have hstable : (prefixWord ++ tailWord_4937374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937374).length < 2 ^ (prefixWord ++ tailWord_4937374).sum := by decide
  have hdescent : baseEnd_4937374 < baseStart_4937374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937380 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_4937380 : Nat := 118140960795 + 4937380 * 2 ^ 59
def prefixEnd_4937380 : Nat := 4983230072969 + 3 ^ 40 * 4937380 * 2
def baseEnd_4937380 : Nat := 2535249113895997711743409

theorem tailTrace_4937380 : CollatzResearch.WordTrace tailWord_4937380 prefixEnd_4937380 2535249113895997711743409 := by
  unfold tailWord_4937380
  simp only [CollatzResearch.WordTrace]
  refine ⟨90040521426361486107776797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120054028568481981477035729 90040521426361486107776797)
  ·
    refine ⟨33765195534885557290416299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90040521426361486107776797 33765195534885557290416299)
    ·
      refine ⟨50647793302328335935624449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33765195534885557290416299 50647793302328335935624449)
      ·
        refine ⟨37985844976746251951718337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50647793302328335935624449 37985844976746251951718337)
        ·
          refine ⟨28489383732559688963788753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37985844976746251951718337 28489383732559688963788753)
          ·
            refine ⟨21367037799419766722841565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28489383732559688963788753 21367037799419766722841565)
            ·
              refine ⟨8012639174782412521065587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21367037799419766722841565 8012639174782412521065587)
              ·
                refine ⟨12018958762173618781598381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8012639174782412521065587 12018958762173618781598381)
                ·
                  refine ⟨4507109535815107043099393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12018958762173618781598381 4507109535815107043099393)
                  ·
                    refine ⟨3380332151861330282324545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4507109535815107043099393 3380332151861330282324545)
                    ·
                      refine ⟨2535249113895997711743409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380332151861330282324545 2535249113895997711743409)
                      ·
                        rfl

theorem cell23_4937380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_4937380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937380 prefixEnd_4937380 := by exact prefixLift 4937380
  have htrace : WordTrace (prefixWord ++ tailWord_4937380) baseStart_4937380 baseEnd_4937380 := by
    simpa [prefixWord, tailWord_4937380, baseEnd_4937380] using wordTrace_append hprefix tailTrace_4937380
  have hstable : (prefixWord ++ tailWord_4937380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937380).length < 2 ^ (prefixWord ++ tailWord_4937380).sum := by decide
  have hdescent : baseEnd_4937380 < baseStart_4937380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937397 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_4937397 : Nat := 118140960795 + 4937397 * 2 ^ 59
def prefixEnd_4937397 : Nat := 4983230072969 + 3 ^ 40 * 4937397 * 2
def baseEnd_4937397 : Nat := 2535257843067124145230831

theorem tailTrace_4937397 : CollatzResearch.WordTrace tailWord_4937397 prefixEnd_4937397 2535257843067124145230831 := by
  unfold tailWord_4937397
  simp only [CollatzResearch.WordTrace]
  refine ⟨180081662893661384118922445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120054441929107589412614963 180081662893661384118922445)
  ·
    refine ⟨67530623585123019044595917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180081662893661384118922445 67530623585123019044595917)
    ·
      refine ⟨25323983844421132141723469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67530623585123019044595917 25323983844421132141723469)
      ·
        refine ⟨9496493941657924553146301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25323983844421132141723469 9496493941657924553146301)
        ·
          refine ⟨3561185228121721707429863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9496493941657924553146301 3561185228121721707429863)
          ·
            refine ⟨5341777842182582561144795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561185228121721707429863 5341777842182582561144795)
            ·
              refine ⟨8012666763273873841717193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341777842182582561144795 8012666763273873841717193)
              ·
                refine ⟨6009500072455405381287895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8012666763273873841717193 6009500072455405381287895)
                ·
                  refine ⟨9014250108683108071931843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009500072455405381287895 9014250108683108071931843)
                  ·
                    refine ⟨13521375163024662107897765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9014250108683108071931843 13521375163024662107897765)
                    ·
                      refine ⟨2535257843067124145230831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13521375163024662107897765 2535257843067124145230831)
                      ·
                        rfl

theorem cell23_4937397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_4937397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937397 prefixEnd_4937397 := by exact prefixLift 4937397
  have htrace : WordTrace (prefixWord ++ tailWord_4937397) baseStart_4937397 baseEnd_4937397 := by
    simpa [prefixWord, tailWord_4937397, baseEnd_4937397] using wordTrace_append hprefix tailTrace_4937397
  have hstable : (prefixWord ++ tailWord_4937397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937397).length < 2 ^ (prefixWord ++ tailWord_4937397).sum := by decide
  have hdescent : baseEnd_4937397 < baseStart_4937397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937414 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_4937414 : Nat := 118140960795 + 4937414 * 2 ^ 59
def prefixEnd_4937414 : Nat := 4983230072969 + 3 ^ 40 * 4937414 * 2
def baseEnd_4937414 : Nat := 2535266572238250578718253

theorem tailTrace_4937414 : CollatzResearch.WordTrace tailWord_4937414 prefixEnd_4937414 2535266572238250578718253 := by
  unfold tailWord_4937414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627571341706243625696603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120054855289733197348194197 5627571341706243625696603)
  ·
    refine ⟨8441357012559365438544905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5627571341706243625696603 8441357012559365438544905)
    ·
      refine ⟨6331017759419524078908679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8441357012559365438544905 6331017759419524078908679)
      ·
        refine ⟨9496526639129286118363019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6331017759419524078908679 9496526639129286118363019)
        ·
          refine ⟨14244789958693929177544529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9496526639129286118363019 14244789958693929177544529)
          ·
            refine ⟨10683592469020446883158397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14244789958693929177544529 10683592469020446883158397)
            ·
              refine ⟨4006347175882667581184399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10683592469020446883158397 4006347175882667581184399)
              ·
                refine ⟨6009520763824001371776599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006347175882667581184399 6009520763824001371776599)
                ·
                  refine ⟨9014281145736002057664899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009520763824001371776599 9014281145736002057664899)
                  ·
                    refine ⟨13521421718604003086497349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9014281145736002057664899 13521421718604003086497349)
                    ·
                      refine ⟨2535266572238250578718253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13521421718604003086497349 2535266572238250578718253)
                      ·
                        rfl

theorem cell23_4937414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_4937414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937414 prefixEnd_4937414 := by exact prefixLift 4937414
  have htrace : WordTrace (prefixWord ++ tailWord_4937414) baseStart_4937414 baseEnd_4937414 := by
    simpa [prefixWord, tailWord_4937414, baseEnd_4937414] using wordTrace_append hprefix tailTrace_4937414
  have hstable : (prefixWord ++ tailWord_4937414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937414).length < 2 ^ (prefixWord ++ tailWord_4937414).sum := by decide
  have hdescent : baseEnd_4937414 < baseStart_4937414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937419 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 4]
def baseStart_4937419 : Nat := 118140960795 + 4937419 * 2 ^ 59
def prefixEnd_4937419 : Nat := 4983230072969 + 3 ^ 40 * 4937419 * 2
def baseEnd_4937419 : Nat := 2535269139641523059155729

theorem tailTrace_4937419 : CollatzResearch.WordTrace tailWord_4937419 prefixEnd_4937419 2535269139641523059155729 := by
  unfold tailWord_4937419
  simp only [CollatzResearch.WordTrace]
  refine ⟨180082465299581681876223311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120054976866387787917482207 180082465299581681876223311)
  ·
    refine ⟨270123697949372522814334967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180082465299581681876223311 270123697949372522814334967)
    ·
      refine ⟨405185546924058784221502451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270123697949372522814334967 405185546924058784221502451)
      ·
        refine ⟨607778320386088176332253677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405185546924058784221502451 607778320386088176332253677)
        ·
          refine ⟨227916870144783066124595129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 607778320386088176332253677 227916870144783066124595129)
          ·
            refine ⟨170937652608587299593446347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227916870144783066124595129 170937652608587299593446347)
            ·
              refine ⟨256406478912880949390169521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170937652608587299593446347 256406478912880949390169521)
              ·
                refine ⟨192304859184660712042627141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256406478912880949390169521 192304859184660712042627141)
                ·
                  refine ⟨36057161097123883507992589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192304859184660712042627141 36057161097123883507992589)
                  ·
                    refine ⟨13521435411421456315497221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36057161097123883507992589 13521435411421456315497221)
                    ·
                      refine ⟨2535269139641523059155729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13521435411421456315497221 2535269139641523059155729)
                      ·
                        rfl

theorem cell23_4937419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 4].length) (baseStart_4937419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937419 prefixEnd_4937419 := by exact prefixLift 4937419
  have htrace : WordTrace (prefixWord ++ tailWord_4937419) baseStart_4937419 baseEnd_4937419 := by
    simpa [prefixWord, tailWord_4937419, baseEnd_4937419] using wordTrace_append hprefix tailTrace_4937419
  have hstable : (prefixWord ++ tailWord_4937419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937419).length < 2 ^ (prefixWord ++ tailWord_4937419).sum := by decide
  have hdescent : baseEnd_4937419 < baseStart_4937419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937423 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 1, 3, 2]
def baseStart_4937423 : Nat := 118140960795 + 4937423 * 2 ^ 59
def prefixEnd_4937423 : Nat := 4983230072969 + 3 ^ 40 * 4937423 * 2
def baseEnd_4937423 : Nat := 2535271193564141043505711

theorem tailTrace_4937423 : CollatzResearch.WordTrace tailWord_4937423 prefixEnd_4937423 2535271193564141043505711 := by
  unfold tailWord_4937423
  simp only [CollatzResearch.WordTrace]
  refine ⟨180082611191567190559368923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120055074127711460372912615 180082611191567190559368923)
  ·
    refine ⟨270123916787350785839053385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180082611191567190559368923 270123916787350785839053385)
    ·
      refine ⟨202592937590513089379290039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270123916787350785839053385 202592937590513089379290039)
      ·
        refine ⟨303889406385769634068935059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202592937590513089379290039 303889406385769634068935059)
        ·
          refine ⟨455834109578654451103402589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303889406385769634068935059 455834109578654451103402589)
          ·
            refine ⟨170937791091995419163775971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455834109578654451103402589 170937791091995419163775971)
            ·
              refine ⟨256406686637993128745663957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170937791091995419163775971 256406686637993128745663957)
              ·
                refine ⟨6009531718077963954976499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 256406686637993128745663957 6009531718077963954976499)
                ·
                  refine ⟨9014297577116945932464749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009531718077963954976499 9014297577116945932464749)
                  ·
                    refine ⟨3380361591418854724674281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9014297577116945932464749 3380361591418854724674281)
                    ·
                      refine ⟨2535271193564141043505711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380361591418854724674281 2535271193564141043505711)
                      ·
                        rfl

theorem cell23_4937423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 3, 2].length) (baseStart_4937423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937423 prefixEnd_4937423 := by exact prefixLift 4937423
  have htrace : WordTrace (prefixWord ++ tailWord_4937423) baseStart_4937423 baseEnd_4937423 := by
    simpa [prefixWord, tailWord_4937423, baseEnd_4937423] using wordTrace_append hprefix tailTrace_4937423
  have hstable : (prefixWord ++ tailWord_4937423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937423).length < 2 ^ (prefixWord ++ tailWord_4937423).sum := by decide
  have hdescent : baseEnd_4937423 < baseStart_4937423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937459 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 9]
def baseStart_4937459 : Nat := 118140960795 + 4937459 * 2 ^ 59
def prefixEnd_4937459 : Nat := 4983230072969 + 3 ^ 40 * 4937459 * 2
def baseEnd_4937459 : Nat := 281698853207522544739505

theorem tailTrace_4937459 : CollatzResearch.WordTrace tailWord_4937459 prefixEnd_4937459 281698853207522544739505 := by
  unfold tailWord_4937459
  simp only [CollatzResearch.WordTrace]
  refine ⟨180083924219436768707679431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120055949479624512471786287 180083924219436768707679431)
  ·
    refine ⟨270125886329155153061519147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180083924219436768707679431 270125886329155153061519147)
    ·
      refine ⟨405188829493732729592278721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270125886329155153061519147 405188829493732729592278721)
      ·
        refine ⟨303891622120299547194209041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405188829493732729592278721 303891622120299547194209041)
        ·
          refine ⟨227918716590224660395656781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303891622120299547194209041 227918716590224660395656781)
          ·
            refine ⟨85469518721334247648371293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227918716590224660395656781 85469518721334247648371293)
            ·
              refine ⟨32051069520500342868139235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85469518721334247648371293 32051069520500342868139235)
              ·
                refine ⟨48076604280750514302208853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32051069520500342868139235 48076604280750514302208853)
                ·
                  refine ⟨281698853207522544739505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48076604280750514302208853 281698853207522544739505)
                  ·
                    rfl

theorem cell23_4937459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 9].length) (baseStart_4937459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937459 prefixEnd_4937459 := by exact prefixLift 4937459
  have htrace : WordTrace (prefixWord ++ tailWord_4937459) baseStart_4937459 baseEnd_4937459 := by
    simpa [prefixWord, tailWord_4937459, baseEnd_4937459] using wordTrace_append hprefix tailTrace_4937459
  have hstable : (prefixWord ++ tailWord_4937459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937459).length < 2 ^ (prefixWord ++ tailWord_4937459).sum := by decide
  have hdescent : baseEnd_4937459 < baseStart_4937459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937493 : List Nat := [1, 3, 2, 1, 2, 3, 2, 4, 5]
def baseStart_4937493 : Nat := 118140960795 + 4937493 * 2 ^ 59
def prefixEnd_4937493 : Nat := 4983230072969 + 3 ^ 40 * 4937493 * 2
def baseEnd_4937493 : Nat := 281700793023328418847821

theorem tailTrace_4937493 : CollatzResearch.WordTrace tailWord_4937493 prefixEnd_4937493 281700793023328418847821 := by
  unfold tailWord_4937493
  simp only [CollatzResearch.WordTrace]
  refine ⟨180085164301313592514417133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120056776200875728342944755 180085164301313592514417133)
  ·
    refine ⟨67531936612992597192906425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180085164301313592514417133 67531936612992597192906425)
    ·
      refine ⟨50648952459744447894679819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67531936612992597192906425 50648952459744447894679819)
      ·
        refine ⟨75973428689616671842019729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50648952459744447894679819 75973428689616671842019729)
        ·
          refine ⟨56980071517212503881514797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75973428689616671842019729 56980071517212503881514797)
          ·
            refine ⟨21367526818954688955568049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56980071517212503881514797 21367526818954688955568049)
            ·
              refine ⟨16025645114216016716676037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21367526818954688955568049 16025645114216016716676037)
              ·
                refine ⟨3004808458915503134376757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16025645114216016716676037 3004808458915503134376757)
                ·
                  refine ⟨281700793023328418847821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3004808458915503134376757 281700793023328418847821)
                  ·
                    rfl

theorem cell23_4937493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_4937493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937493 prefixEnd_4937493 := by exact prefixLift 4937493
  have htrace : WordTrace (prefixWord ++ tailWord_4937493) baseStart_4937493 baseEnd_4937493 := by
    simpa [prefixWord, tailWord_4937493, baseEnd_4937493] using wordTrace_append hprefix tailTrace_4937493
  have hstable : (prefixWord ++ tailWord_4937493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937493).length < 2 ^ (prefixWord ++ tailWord_4937493).sum := by decide
  have hdescent : baseEnd_4937493 < baseStart_4937493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937506 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_4937506 : Nat := 118140960795 + 4937506 * 2 ^ 59
def prefixEnd_4937506 : Nat := 4983230072969 + 3 ^ 40 * 4937506 * 2
def baseEnd_4937506 : Nat := 845104604152821406255943

theorem tailTrace_4937506 : CollatzResearch.WordTrace tailWord_4937506 prefixEnd_4937506 845104604152821406255943 := by
  unfold tailWord_4937506
  simp only [CollatzResearch.WordTrace]
  refine ⟨45021409612566623933660093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120057092300177663823093581 45021409612566623933660093)
  ·
    refine ⟨16883028604712483975122535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45021409612566623933660093 16883028604712483975122535)
    ·
      refine ⟨25324542907068725962683803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16883028604712483975122535 25324542907068725962683803)
      ·
        refine ⟨37986814360603088944025705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25324542907068725962683803 37986814360603088944025705)
        ·
          refine ⟨28490110770452316708019279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37986814360603088944025705 28490110770452316708019279)
          ·
            refine ⟨42735166155678475062028919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28490110770452316708019279 42735166155678475062028919)
            ·
              refine ⟨64102749233517712593043379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42735166155678475062028919 64102749233517712593043379)
              ·
                refine ⟨96154123850276568889565069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64102749233517712593043379 96154123850276568889565069)
                ·
                  refine ⟨36057796443853713333586901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96154123850276568889565069 36057796443853713333586901)
                  ·
                    refine ⟨845104604152821406255943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36057796443853713333586901 845104604152821406255943)
                    ·
                      rfl

theorem cell23_4937506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_4937506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937506 prefixEnd_4937506 := by exact prefixLift 4937506
  have htrace : WordTrace (prefixWord ++ tailWord_4937506) baseStart_4937506 baseEnd_4937506 := by
    simpa [prefixWord, tailWord_4937506, baseEnd_4937506] using wordTrace_append hprefix tailTrace_4937506
  have hstable : (prefixWord ++ tailWord_4937506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937506).length < 2 ^ (prefixWord ++ tailWord_4937506).sum := by decide
  have hdescent : baseEnd_4937506 < baseStart_4937506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937543 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_4937543 : Nat := 118140960795 + 4937543 * 2 ^ 59
def prefixEnd_4937543 : Nat := 4983230072969 + 3 ^ 40 * 4937543 * 2
def baseEnd_4937543 : Nat := 2535332811242680574005159

theorem tailTrace_4937543 : CollatzResearch.WordTrace tailWord_4937543 prefixEnd_4937543 2535332811242680574005159 := by
  unfold tailWord_4937543
  simp only [CollatzResearch.WordTrace]
  refine ⟨180086987951132451053737283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120057991967421634035824855 180086987951132451053737283)
  ·
    refine ⟨270130481926698676580605925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180086987951132451053737283 270130481926698676580605925)
    ·
      refine ⟨50649465361256001858863611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270130481926698676580605925 50649465361256001858863611)
      ·
        refine ⟨75974198041884002788295417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50649465361256001858863611 75974198041884002788295417)
        ·
          refine ⟨56980648531413002091221563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75974198041884002788295417 56980648531413002091221563)
          ·
            refine ⟨85470972797119503136832345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56980648531413002091221563 85470972797119503136832345)
            ·
              refine ⟨64103229597839627352624259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85470972797119503136832345 64103229597839627352624259)
              ·
                refine ⟨96154844396759441028936389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64103229597839627352624259 96154844396759441028936389)
                ·
                  refine ⟨18029033324392395192925573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96154844396759441028936389 18029033324392395192925573)
                  ·
                    refine ⟨3380443748323574098673545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18029033324392395192925573 3380443748323574098673545)
                    ·
                      refine ⟨2535332811242680574005159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380443748323574098673545 2535332811242680574005159)
                      ·
                        rfl

theorem cell23_4937543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_4937543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937543 prefixEnd_4937543 := by exact prefixLift 4937543
  have htrace : WordTrace (prefixWord ++ tailWord_4937543) baseStart_4937543 baseEnd_4937543 := by
    simpa [prefixWord, tailWord_4937543, baseEnd_4937543] using wordTrace_append hprefix tailTrace_4937543
  have hstable : (prefixWord ++ tailWord_4937543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937543).length < 2 ^ (prefixWord ++ tailWord_4937543).sum := by decide
  have hdescent : baseEnd_4937543 < baseStart_4937543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937580 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_4937580 : Nat := 118140960795 + 4937580 * 2 ^ 59
def prefixEnd_4937580 : Nat := 4983230072969 + 3 ^ 40 * 4937580 * 2
def baseEnd_4937580 : Nat := 2535351810026896929242489

theorem tailTrace_4937580 : CollatzResearch.WordTrace tailWord_4937580 prefixEnd_4937580 2535351810026896929242489 := by
  unfold tailWord_4937580
  simp only [CollatzResearch.WordTrace]
  refine ⟨90044168725999203186417097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120058891634665604248556129 90044168725999203186417097)
  ·
    refine ⟨67533126544499402389812823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90044168725999203186417097 67533126544499402389812823)
    ·
      refine ⟨101299689816749103584719235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67533126544499402389812823 101299689816749103584719235)
      ·
        refine ⟨151949534725123655377078853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101299689816749103584719235 151949534725123655377078853)
        ·
          refine ⟨28490537760960685383202285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151949534725123655377078853 28490537760960685383202285)
          ·
            refine ⟨10683951660360257018700857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28490537760960685383202285 10683951660360257018700857)
            ·
              refine ⟨8012963745270192764025643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10683951660360257018700857 8012963745270192764025643)
              ·
                refine ⟨12019445617905289146038465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8012963745270192764025643 12019445617905289146038465)
                ·
                  refine ⟨9014584213428966859528849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12019445617905289146038465 9014584213428966859528849)
                  ·
                    refine ⟨6760938160071725144646637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9014584213428966859528849 6760938160071725144646637)
                    ·
                      refine ⟨2535351810026896929242489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6760938160071725144646637 2535351810026896929242489)
                      ·
                        rfl

theorem cell23_4937580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_4937580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937580 prefixEnd_4937580 := by exact prefixLift 4937580
  have htrace : WordTrace (prefixWord ++ tailWord_4937580) baseStart_4937580 baseEnd_4937580 := by
    simpa [prefixWord, tailWord_4937580, baseEnd_4937580] using wordTrace_append hprefix tailTrace_4937580
  have hstable : (prefixWord ++ tailWord_4937580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937580).length < 2 ^ (prefixWord ++ tailWord_4937580).sum := by decide
  have hdescent : baseEnd_4937580 < baseStart_4937580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937586 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_4937586 : Nat := 118140960795 + 4937586 * 2 ^ 59
def prefixEnd_4937586 : Nat := 4983230072969 + 3 ^ 40 * 4937586 * 2
def baseEnd_4937586 : Nat := 2535354890910823905767461

theorem tailTrace_4937586 : CollatzResearch.WordTrace tailWord_4937586 prefixEnd_4937586 2535354890910823905767461 := by
  unfold tailWord_4937586
  simp only [CollatzResearch.WordTrace]
  refine ⟨45022139072494167349388153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120059037526651112931701741 45022139072494167349388153)
  ·
    refine ⟨33766604304370625512041115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45022139072494167349388153 33766604304370625512041115)
    ·
      refine ⟨50649906456555938268061673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33766604304370625512041115 50649906456555938268061673)
      ·
        refine ⟨37987429842416953701046255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50649906456555938268061673 37987429842416953701046255)
        ·
          refine ⟨56981144763625430551569383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37987429842416953701046255 56981144763625430551569383)
          ·
            refine ⟨85471717145438145827354075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56981144763625430551569383 85471717145438145827354075)
            ·
              refine ⟨128207575718157218741031113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85471717145438145827354075 128207575718157218741031113)
              ·
                refine ⟨96155681788617914055773335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128207575718157218741031113 96155681788617914055773335)
                ·
                  refine ⟨144233522682926871083660003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96155681788617914055773335 144233522682926871083660003)
                  ·
                    refine ⟨216350284024390306625490005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 144233522682926871083660003 216350284024390306625490005)
                    ·
                      refine ⟨2535354890910823905767461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 216350284024390306625490005 2535354890910823905767461)
                      ·
                        rfl

theorem cell23_4937586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_4937586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937586 prefixEnd_4937586 := by exact prefixLift 4937586
  have htrace : WordTrace (prefixWord ++ tailWord_4937586) baseStart_4937586 baseEnd_4937586 := by
    simpa [prefixWord, tailWord_4937586, baseEnd_4937586] using wordTrace_append hprefix tailTrace_4937586
  have hstable : (prefixWord ++ tailWord_4937586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937586).length < 2 ^ (prefixWord ++ tailWord_4937586).sum := by decide
  have hdescent : baseEnd_4937586 < baseStart_4937586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937616 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_4937616 : Nat := 118140960795 + 4937616 * 2 ^ 59
def prefixEnd_4937616 : Nat := 4983230072969 + 3 ^ 40 * 4937616 * 2
def baseEnd_4937616 : Nat := 2535370295330458788392323

theorem tailTrace_4937616 : CollatzResearch.WordTrace tailWord_4937616 prefixEnd_4937616 2535370295330458788392323 := by
  unfold tailWord_4937616
  simp only [CollatzResearch.WordTrace]
  refine ⟨90044825239933992260572351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120059766986578656347429801 90044825239933992260572351)
  ·
    refine ⟨135067237859900988390858527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90044825239933992260572351 135067237859900988390858527)
    ·
      refine ⟨202600856789851482586287791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135067237859900988390858527 202600856789851482586287791)
      ·
        refine ⟨303901285184777223879431687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202600856789851482586287791 303901285184777223879431687)
        ·
          refine ⟨455851927777165835819147531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303901285184777223879431687 455851927777165835819147531)
          ·
            refine ⟨683777891665748753728721297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455851927777165835819147531 683777891665748753728721297)
            ·
              refine ⟨512833418749311565296540973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683777891665748753728721297 512833418749311565296540973)
              ·
                refine ⟨192312532030991836986202865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 512833418749311565296540973 192312532030991836986202865)
                ·
                  refine ⟨144234399023243877739652149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192312532030991836986202865 144234399023243877739652149)
                  ·
                    refine ⟨13521974908429113538092389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 144234399023243877739652149 13521974908429113538092389)
                    ·
                      refine ⟨2535370295330458788392323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13521974908429113538092389 2535370295330458788392323)
                      ·
                        rfl

theorem cell23_4937616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_4937616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937616 prefixEnd_4937616 := by exact prefixLift 4937616
  have htrace : WordTrace (prefixWord ++ tailWord_4937616) baseStart_4937616 baseEnd_4937616 := by
    simpa [prefixWord, tailWord_4937616, baseEnd_4937616] using wordTrace_append hprefix tailTrace_4937616
  have hstable : (prefixWord ++ tailWord_4937616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937616).length < 2 ^ (prefixWord ++ tailWord_4937616).sum := by decide
  have hdescent : baseEnd_4937616 < baseStart_4937616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937656 : List Nat := [2, 1, 2, 1, 2, 3, 12]
def baseStart_4937656 : Nat := 118140960795 + 4937656 * 2 ^ 59
def prefixEnd_4937656 : Nat := 4983230072969 + 3 ^ 40 * 4937656 * 2
def baseEnd_4937656 : Nat := 31301121414279489282619

theorem tailTrace_4937656 : CollatzResearch.WordTrace tailWord_4937656 prefixEnd_4937656 31301121414279489282619 := by
  unfold tailWord_4937656
  simp only [CollatzResearch.WordTrace]
  refine ⟨90045554699861535676300411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120060739599815380901733881 90045554699861535676300411)
  ·
    refine ⟨135068332049792303514450617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90045554699861535676300411 135068332049792303514450617)
    ·
      refine ⟨101301249037344227635837963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135068332049792303514450617 101301249037344227635837963)
      ·
        refine ⟨151951873556016341453756945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101301249037344227635837963 151951873556016341453756945)
        ·
          refine ⟨113963905167012256090317709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151951873556016341453756945 113963905167012256090317709)
          ·
            refine ⟨42736464437629596033869141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113963905167012256090317709 42736464437629596033869141)
            ·
              refine ⟨31301121414279489282619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 42736464437629596033869141 31301121414279489282619)
              ·
                rfl

theorem cell23_4937656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 12].length) (baseStart_4937656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937656 prefixEnd_4937656 := by exact prefixLift 4937656
  have htrace : WordTrace (prefixWord ++ tailWord_4937656) baseStart_4937656 baseEnd_4937656 := by
    simpa [prefixWord, tailWord_4937656, baseEnd_4937656] using wordTrace_append hprefix tailTrace_4937656
  have hstable : (prefixWord ++ tailWord_4937656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937656).length < 2 ^ (prefixWord ++ tailWord_4937656).sum := by decide
  have hdescent : baseEnd_4937656 < baseStart_4937656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937700 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_4937700 : Nat := 118140960795 + 4937700 * 2 ^ 59
def prefixEnd_4937700 : Nat := 4983230072969 + 3 ^ 40 * 4937700 * 2
def baseEnd_4937700 : Nat := 2535413427705436459741937

theorem tailTrace_4937700 : CollatzResearch.WordTrace tailWord_4937700 prefixEnd_4937700 2535413427705436459741937 := by
  unfold tailWord_4937700
  simp only [CollatzResearch.WordTrace]
  refine ⟨90046357105781833433601277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120061809474375777911468369 90046357105781833433601277)
  ·
    refine ⟨33767383914668187537600479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90046357105781833433601277 33767383914668187537600479)
    ·
      refine ⟨50651075872002281306400719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33767383914668187537600479 50651075872002281306400719)
      ·
        refine ⟨75976613808003421959601079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50651075872002281306400719 75976613808003421959601079)
        ·
          refine ⟨113964920712005132939401619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75976613808003421959601079 113964920712005132939401619)
          ·
            refine ⟨170947381068007699409102429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113964920712005132939401619 170947381068007699409102429)
            ·
              refine ⟨64105267900502887278413411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170947381068007699409102429 64105267900502887278413411)
              ·
                refine ⟨96157901850754330917620117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64105267900502887278413411 96157901850754330917620117)
                ·
                  refine ⟨4507401649254109261763443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96157901850754330917620117 4507401649254109261763443)
                  ·
                    refine ⟨6761102473881163892645165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4507401649254109261763443 6761102473881163892645165)
                    ·
                      refine ⟨2535413427705436459741937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6761102473881163892645165 2535413427705436459741937)
                      ·
                        rfl

theorem cell23_4937700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_4937700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937700 prefixEnd_4937700 := by exact prefixLift 4937700
  have htrace : WordTrace (prefixWord ++ tailWord_4937700) baseStart_4937700 baseEnd_4937700 := by
    simpa [prefixWord, tailWord_4937700, baseEnd_4937700] using wordTrace_append hprefix tailTrace_4937700
  have hstable : (prefixWord ++ tailWord_4937700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937700).length < 2 ^ (prefixWord ++ tailWord_4937700).sum := by decide
  have hdescent : baseEnd_4937700 < baseStart_4937700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937718 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_4937718 : Nat := 118140960795 + 4937718 * 2 ^ 59
def prefixEnd_4937718 : Nat := 4983230072969 + 3 ^ 40 * 4937718 * 2
def baseEnd_4937718 : Nat := 2535422670357217389316855

theorem tailTrace_4937718 : CollatzResearch.WordTrace tailWord_4937718 prefixEnd_4937718 2535422670357217389316855 := by
  unfold tailWord_4937718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255835670343653496334863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120062247150332303960905205 11255835670343653496334863)
  ·
    refine ⟨16883753505515480244502295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11255835670343653496334863 16883753505515480244502295)
    ·
      refine ⟨25325630258273220366753443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16883753505515480244502295 25325630258273220366753443)
      ·
        refine ⟨37988445387409830550130165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25325630258273220366753443 37988445387409830550130165)
        ·
          refine ⟨3561416755069671614074703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37988445387409830550130165 3561416755069671614074703)
          ·
            refine ⟨5342125132604507421112055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561416755069671614074703 5342125132604507421112055)
            ·
              refine ⟨8013187698906761131668083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342125132604507421112055 8013187698906761131668083)
              ·
                refine ⟨12019781548360141697502125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8013187698906761131668083 12019781548360141697502125)
                ·
                  refine ⟨4507418080635053136563297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12019781548360141697502125 4507418080635053136563297)
                  ·
                    refine ⟨3380563560476289852422473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4507418080635053136563297 3380563560476289852422473)
                    ·
                      refine ⟨2535422670357217389316855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380563560476289852422473 2535422670357217389316855)
                      ·
                        rfl

theorem cell23_4937718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_4937718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937718 prefixEnd_4937718 := by exact prefixLift 4937718
  have htrace : WordTrace (prefixWord ++ tailWord_4937718) baseStart_4937718 baseEnd_4937718 := by
    simpa [prefixWord, tailWord_4937718, baseEnd_4937718] using wordTrace_append hprefix tailTrace_4937718
  have hstable : (prefixWord ++ tailWord_4937718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937718).length < 2 ^ (prefixWord ++ tailWord_4937718).sum := by decide
  have hdescent : baseEnd_4937718 < baseStart_4937718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937753 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_4937753 : Nat := 118140960795 + 4937753 * 2 ^ 59
def prefixEnd_4937753 : Nat := 4983230072969 + 3 ^ 40 * 4937753 * 2
def baseEnd_4937753 : Nat := 2535440642180124752379193

theorem tailTrace_4937753 : CollatzResearch.WordTrace tailWord_4937753 prefixEnd_4937753 2535440642180124752379193 := by
  unfold tailWord_4937753
  simp only [CollatzResearch.WordTrace]
  refine ⟨180094647280371656918881913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120063098186914437945921275 180094647280371656918881913)
  ·
    refine ⟨135070985460278742689161435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180094647280371656918881913 135070985460278742689161435)
    ·
      refine ⟨202606478190418114033742153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135070985460278742689161435 202606478190418114033742153)
      ·
        refine ⟨151954858642813585525306615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202606478190418114033742153 151954858642813585525306615)
        ·
          refine ⟨227932287964220378287959923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151954858642813585525306615 227932287964220378287959923)
          ·
            refine ⟨341898431946330567431939885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227932287964220378287959923 341898431946330567431939885)
            ·
              refine ⟨128211911979873962786977457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341898431946330567431939885 128211911979873962786977457)
              ·
                refine ⟨96158933984905472090233093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128211911979873962786977457 96158933984905472090233093)
                ·
                  refine ⟨18029800122169776016918705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96158933984905472090233093 18029800122169776016918705)
                  ·
                    refine ⟨13522350091627332012689029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18029800122169776016918705 13522350091627332012689029)
                    ·
                      refine ⟨2535440642180124752379193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13522350091627332012689029 2535440642180124752379193)
                      ·
                        rfl

theorem cell23_4937753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_4937753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937753 prefixEnd_4937753 := by exact prefixLift 4937753
  have htrace : WordTrace (prefixWord ++ tailWord_4937753) baseStart_4937753 baseEnd_4937753 := by
    simpa [prefixWord, tailWord_4937753, baseEnd_4937753] using wordTrace_append hprefix tailTrace_4937753
  have hstable : (prefixWord ++ tailWord_4937753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937753).length < 2 ^ (prefixWord ++ tailWord_4937753).sum := by decide
  have hdescent : baseEnd_4937753 < baseStart_4937753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937757 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_4937757 : Nat := 118140960795 + 4937757 * 2 ^ 59
def prefixEnd_4937757 : Nat := 4983230072969 + 3 ^ 40 * 4937757 * 2
def baseEnd_4937757 : Nat := 2535442696102742736729175

theorem tailTrace_4937757 : CollatzResearch.WordTrace tailWord_4937757 prefixEnd_4937757 2535442696102742736729175 := by
  unfold tailWord_4937757
  simp only [CollatzResearch.WordTrace]
  refine ⟨180094793172357165602027525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120063195448238110401351683 180094793172357165602027525)
  ·
    refine ⟨33767773719816968550380161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180094793172357165602027525 33767773719816968550380161)
    ·
      refine ⟨25325830289862726412785121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33767773719816968550380161 25325830289862726412785121)
      ·
        refine ⟨18994372717397044809588841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25325830289862726412785121 18994372717397044809588841)
        ·
          refine ⟨14245779538047783607191631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18994372717397044809588841 14245779538047783607191631)
          ·
            refine ⟨21368669307071675410787447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14245779538047783607191631 21368669307071675410787447)
            ·
              refine ⟨32053003960607513116181171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21368669307071675410787447 32053003960607513116181171)
              ·
                refine ⟨48079505940911269674271757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32053003960607513116181171 48079505940911269674271757)
                ·
                  refine ⟨18029814727841726127851909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48079505940911269674271757 18029814727841726127851909)
                  ·
                    refine ⟨3380590261470323648972233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18029814727841726127851909 3380590261470323648972233)
                    ·
                      refine ⟨2535442696102742736729175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380590261470323648972233 2535442696102742736729175)
                      ·
                        rfl

theorem cell23_4937757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_4937757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937757 prefixEnd_4937757 := by exact prefixLift 4937757
  have htrace : WordTrace (prefixWord ++ tailWord_4937757) baseStart_4937757 baseEnd_4937757 := by
    simpa [prefixWord, tailWord_4937757, baseEnd_4937757] using wordTrace_append hprefix tailTrace_4937757
  have hstable : (prefixWord ++ tailWord_4937757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937757).length < 2 ^ (prefixWord ++ tailWord_4937757).sum := by decide
  have hdescent : baseEnd_4937757 < baseStart_4937757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937761 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_4937761 : Nat := 118140960795 + 4937761 * 2 ^ 59
def prefixEnd_4937761 : Nat := 4983230072969 + 3 ^ 40 * 4937761 * 2
def baseEnd_4937761 : Nat := 2535444750025360721079157

theorem tailTrace_4937761 : CollatzResearch.WordTrace tailWord_4937761 prefixEnd_4937761 2535444750025360721079157 := by
  unfold tailWord_4937761
  simp only [CollatzResearch.WordTrace]
  refine ⟨180094939064342674285173137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120063292709561782856782091 180094939064342674285173137)
  ·
    refine ⟨135071204298257005713879853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180094939064342674285173137 135071204298257005713879853)
    ·
      refine ⟨50651701611846377142704945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135071204298257005713879853 50651701611846377142704945)
      ·
        refine ⟨37988776208884782857028709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50651701611846377142704945 37988776208884782857028709)
        ·
          refine ⟨7122895539165896785692883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37988776208884782857028709 7122895539165896785692883)
          ·
            refine ⟨10684343308748845178539325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7122895539165896785692883 10684343308748845178539325)
            ·
              refine ⟨4006628740780816941952247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10684343308748845178539325 4006628740780816941952247)
              ·
                refine ⟨6009943111171225412928371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006628740780816941952247 6009943111171225412928371)
                ·
                  refine ⟨9014914666756838119392557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009943111171225412928371 9014914666756838119392557)
                  ·
                    refine ⟨3380593000033814294772209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9014914666756838119392557 3380593000033814294772209)
                    ·
                      refine ⟨2535444750025360721079157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380593000033814294772209 2535444750025360721079157)
                      ·
                        rfl

theorem cell23_4937761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_4937761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937761 prefixEnd_4937761 := by exact prefixLift 4937761
  have htrace : WordTrace (prefixWord ++ tailWord_4937761) baseStart_4937761 baseEnd_4937761 := by
    simpa [prefixWord, tailWord_4937761, baseEnd_4937761] using wordTrace_append hprefix tailTrace_4937761
  have hstable : (prefixWord ++ tailWord_4937761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937761).length < 2 ^ (prefixWord ++ tailWord_4937761).sum := by decide
  have hdescent : baseEnd_4937761 < baseStart_4937761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937847 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 2, 4, 2]
def baseStart_4937847 : Nat := 118140960795 + 4937847 * 2 ^ 59
def prefixEnd_4937847 : Nat := 4983230072969 + 3 ^ 40 * 4937847 * 2
def baseEnd_4937847 : Nat := 2535488909361647384603761

theorem tailTrace_4937847 : CollatzResearch.WordTrace tailWord_4937847 prefixEnd_4937847 2535488909361647384603761 := by
  unfold tailWord_4937847
  simp only [CollatzResearch.WordTrace]
  refine ⟨180098075742031110972803795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120065383828020740648535863 180098075742031110972803795)
  ·
    refine ⟨270147113613046666459205693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180098075742031110972803795 270147113613046666459205693)
    ·
      refine ⟨101305167604892499922202135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270147113613046666459205693 101305167604892499922202135)
      ·
        refine ⟨151957751407338749883303203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101305167604892499922202135 151957751407338749883303203)
        ·
          refine ⟨227936627111008124824954805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151957751407338749883303203 227936627111008124824954805)
          ·
            refine ⟨21369058791657011702339513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 227936627111008124824954805 21369058791657011702339513)
            ·
              refine ⟨16026794093742758776754635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21369058791657011702339513 16026794093742758776754635)
              ·
                refine ⟨24040191140614138165131953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16026794093742758776754635 24040191140614138165131953)
                ·
                  refine ⟨18030143355460603623848965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24040191140614138165131953 18030143355460603623848965)
                  ·
                    refine ⟨3380651879148863179471681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18030143355460603623848965 3380651879148863179471681)
                    ·
                      refine ⟨2535488909361647384603761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380651879148863179471681 2535488909361647384603761)
                      ·
                        rfl

theorem cell23_4937847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_4937847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937847 prefixEnd_4937847 := by exact prefixLift 4937847
  have htrace : WordTrace (prefixWord ++ tailWord_4937847) baseStart_4937847 baseEnd_4937847 := by
    simpa [prefixWord, tailWord_4937847, baseEnd_4937847] using wordTrace_append hprefix tailTrace_4937847
  have hstable : (prefixWord ++ tailWord_4937847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937847).length < 2 ^ (prefixWord ++ tailWord_4937847).sum := by decide
  have hdescent : baseEnd_4937847 < baseStart_4937847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937860 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_4937860 : Nat := 118140960795 + 4937860 * 2 ^ 59
def prefixEnd_4937860 : Nat := 4983230072969 + 3 ^ 40 * 4937860 * 2
def baseEnd_4937860 : Nat := 2535495584610155833741201

theorem tailTrace_4937860 : CollatzResearch.WordTrace tailWord_4937860 prefixEnd_4937860 2535495584610155833741201 := by
  unfold tailWord_4937860
  simp only [CollatzResearch.WordTrace]
  refine ⟨90049274945492007096513517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120065699927322676128684689 90049274945492007096513517)
  ·
    refine ⟨33768478104559502661192569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90049274945492007096513517 33768478104559502661192569)
    ·
      refine ⟨25326358578419626995894427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33768478104559502661192569 25326358578419626995894427)
      ·
        refine ⟨37989537867629440493841641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25326358578419626995894427 37989537867629440493841641)
        ·
          refine ⟨28492153400722080370381231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37989537867629440493841641 28492153400722080370381231)
          ·
            refine ⟨42738230101083120555571847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28492153400722080370381231 42738230101083120555571847)
            ·
              refine ⟨64107345151624680833357771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42738230101083120555571847 64107345151624680833357771)
              ·
                refine ⟨96161017727437021250036657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64107345151624680833357771 96161017727437021250036657)
                ·
                  refine ⟨72120763295577765937527493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96161017727437021250036657 72120763295577765937527493)
                  ·
                    refine ⟨13522643117920831113286405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72120763295577765937527493 13522643117920831113286405)
                    ·
                      refine ⟨2535495584610155833741201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13522643117920831113286405 2535495584610155833741201)
                      ·
                        rfl

theorem cell23_4937860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_4937860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937860 prefixEnd_4937860 := by exact prefixLift 4937860
  have htrace : WordTrace (prefixWord ++ tailWord_4937860) baseStart_4937860 baseEnd_4937860 := by
    simpa [prefixWord, tailWord_4937860, baseEnd_4937860] using wordTrace_append hprefix tailTrace_4937860
  have hstable : (prefixWord ++ tailWord_4937860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937860).length < 2 ^ (prefixWord ++ tailWord_4937860).sum := by decide
  have hdescent : baseEnd_4937860 < baseStart_4937860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937907 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 6, 3, 2]
def baseStart_4937907 : Nat := 118140960795 + 4937907 * 2 ^ 59
def prefixEnd_4937907 : Nat := 4983230072969 + 3 ^ 40 * 4937907 * 2
def baseEnd_4937907 : Nat := 2535519718200917149853485

theorem tailTrace_4937907 : CollatzResearch.WordTrace tailWord_4937907 prefixEnd_4937907 2535519718200917149853485 := by
  unfold tailWord_4937907
  simp only [CollatzResearch.WordTrace]
  refine ⟨180100264121813741219987975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120066842747875827479991983 180100264121813741219987975)
  ·
    refine ⟨270150396182720611829981963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180100264121813741219987975 270150396182720611829981963)
    ·
      refine ⟨405225594274080917744972945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270150396182720611829981963 405225594274080917744972945)
      ·
        refine ⟨303919195705560688308729709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405225594274080917744972945 303919195705560688308729709)
        ·
          refine ⟨113969698389585258115773641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303919195705560688308729709 113969698389585258115773641)
          ·
            refine ⟨85477273792188943586830231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113969698389585258115773641 85477273792188943586830231)
            ·
              refine ⟨128215910688283415380245347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85477273792188943586830231 128215910688283415380245347)
              ·
                refine ⟨192323866032425123070368021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128215910688283415380245347 192323866032425123070368021)
                ·
                  refine ⟨9015181220269927643923501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192323866032425123070368021 9015181220269927643923501)
                  ·
                    refine ⟨3380692957601222866471313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9015181220269927643923501 3380692957601222866471313)
                    ·
                      refine ⟨2535519718200917149853485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380692957601222866471313 2535519718200917149853485)
                      ·
                        rfl

theorem cell23_4937907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 3, 2].length) (baseStart_4937907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937907 prefixEnd_4937907 := by exact prefixLift 4937907
  have htrace : WordTrace (prefixWord ++ tailWord_4937907) baseStart_4937907 baseEnd_4937907 := by
    simpa [prefixWord, tailWord_4937907, baseEnd_4937907] using wordTrace_append hprefix tailTrace_4937907
  have hstable : (prefixWord ++ tailWord_4937907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937907).length < 2 ^ (prefixWord ++ tailWord_4937907).sum := by decide
  have hdescent : baseEnd_4937907 < baseStart_4937907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937937 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_4937937 : Nat := 118140960795 + 4937937 * 2 ^ 59
def prefixEnd_4937937 : Nat := 4983230072969 + 3 ^ 40 * 4937937 * 2
def baseEnd_4937937 : Nat := 2535535122620552032478347

theorem tailTrace_4937937 : CollatzResearch.WordTrace tailWord_4937937 prefixEnd_4937937 2535535122620552032478347 := by
  unfold tailWord_4937937
  simp only [CollatzResearch.WordTrace]
  refine ⟨180101358311705056343580065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120067572207803370895720043 180101358311705056343580065)
  ·
    refine ⟨135076018733778792257685049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180101358311705056343580065 135076018733778792257685049)
    ·
      refine ⟨101307014050334094193263787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135076018733778792257685049 101307014050334094193263787)
      ·
        refine ⟨151960521075501141289895681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101307014050334094193263787 151960521075501141289895681)
        ·
          refine ⟨113970390806625855967421761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151960521075501141289895681 113970390806625855967421761)
          ·
            refine ⟨85477793104969391975566321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113970390806625855967421761 85477793104969391975566321)
            ·
              refine ⟨64108344828727043981674741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85477793104969391975566321 64108344828727043981674741)
              ·
                refine ⟨6010157327693160373282007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64108344828727043981674741 6010157327693160373282007)
                ·
                  refine ⟨9015235991539740559923011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6010157327693160373282007 9015235991539740559923011)
                  ·
                    refine ⟨13522853987309610839884517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9015235991539740559923011 13522853987309610839884517)
                    ·
                      refine ⟨2535535122620552032478347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13522853987309610839884517 2535535122620552032478347)
                      ·
                        rfl

theorem cell23_4937937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_4937937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937937 prefixEnd_4937937 := by exact prefixLift 4937937
  have htrace : WordTrace (prefixWord ++ tailWord_4937937) baseStart_4937937 baseEnd_4937937 := by
    simpa [prefixWord, tailWord_4937937, baseEnd_4937937] using wordTrace_append hprefix tailTrace_4937937
  have hstable : (prefixWord ++ tailWord_4937937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937937).length < 2 ^ (prefixWord ++ tailWord_4937937).sum := by decide
  have hdescent : baseEnd_4937937 < baseStart_4937937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937947 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 2, 4]
def baseStart_4937947 : Nat := 118140960795 + 4937947 * 2 ^ 59
def prefixEnd_4937947 : Nat := 4983230072969 + 3 ^ 40 * 4937947 * 2
def baseEnd_4937947 : Nat := 845180085809032331117767

theorem tailTrace_4937947 : CollatzResearch.WordTrace tailWord_4937947 prefixEnd_4937947 845180085809032331117767 := by
  unfold tailWord_4937947
  simp only [CollatzResearch.WordTrace]
  refine ⟨180101723041668828051444095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120067815361112552034296063 180101723041668828051444095)
  ·
    refine ⟨270152584562503242077166143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180101723041668828051444095 270152584562503242077166143)
    ·
      refine ⟨405228876843754863115749215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270152584562503242077166143 405228876843754863115749215)
      ·
        refine ⟨607843315265632294673623823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405228876843754863115749215 607843315265632294673623823)
        ·
          refine ⟨911764972898448442010435735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607843315265632294673623823 911764972898448442010435735)
          ·
            refine ⟨1367647459347672663015653603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911764972898448442010435735 1367647459347672663015653603)
            ·
              refine ⟨2051471189021508994523480405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367647459347672663015653603 2051471189021508994523480405)
              ·
                refine ⟨6010169499086452132393009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2051471189021508994523480405 6010169499086452132393009)
                ·
                  refine ⟨4507627124314839099294757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6010169499086452132393009 4507627124314839099294757)
                  ·
                    refine ⟨845180085809032331117767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4507627124314839099294757 845180085809032331117767)
                    ·
                      rfl

theorem cell23_4937947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 4].length) (baseStart_4937947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937947 prefixEnd_4937947 := by exact prefixLift 4937947
  have htrace : WordTrace (prefixWord ++ tailWord_4937947) baseStart_4937947 baseEnd_4937947 := by
    simpa [prefixWord, tailWord_4937947, baseEnd_4937947] using wordTrace_append hprefix tailTrace_4937947
  have hstable : (prefixWord ++ tailWord_4937947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937947).length < 2 ^ (prefixWord ++ tailWord_4937947).sum := by decide
  have hdescent : baseEnd_4937947 < baseStart_4937947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937967 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_4937967 : Nat := 118140960795 + 4937967 * 2 ^ 59
def prefixEnd_4937967 : Nat := 4983230072969 + 3 ^ 40 * 4937967 * 2
def baseEnd_4937967 : Nat := 2535550527040186915103209

theorem tailTrace_4937967 : CollatzResearch.WordTrace tailWord_4937967 prefixEnd_4937967 2535550527040186915103209 := by
  unfold tailWord_4937967
  simp only [CollatzResearch.WordTrace]
  refine ⟨180102452501596371467172155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120068301667730914311448103 180102452501596371467172155)
  ·
    refine ⟨270153678752394557200758233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180102452501596371467172155 270153678752394557200758233)
    ·
      refine ⟨202615259064295917900568675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270153678752394557200758233 202615259064295917900568675)
      ·
        refine ⟨303922888596443876850853013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202615259064295917900568675 303922888596443876850853013)
        ·
          refine ⟨14246385402958306727383735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 303922888596443876850853013 14246385402958306727383735)
          ·
            refine ⟨21369578104437460091075603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14246385402958306727383735 21369578104437460091075603)
            ·
              refine ⟨32054367156656190136613405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21369578104437460091075603 32054367156656190136613405)
              ·
                refine ⟨12020387683746071301230027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32054367156656190136613405 12020387683746071301230027)
                ·
                  refine ⟨18030581525619106951845041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12020387683746071301230027 18030581525619106951845041)
                  ·
                    refine ⟨13522936144214330213883781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18030581525619106951845041 13522936144214330213883781)
                    ·
                      refine ⟨2535550527040186915103209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13522936144214330213883781 2535550527040186915103209)
                      ·
                        rfl

theorem cell23_4937967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_4937967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937967 prefixEnd_4937967 := by exact prefixLift 4937967
  have htrace : WordTrace (prefixWord ++ tailWord_4937967) baseStart_4937967 baseEnd_4937967 := by
    simpa [prefixWord, tailWord_4937967, baseEnd_4937967] using wordTrace_append hprefix tailTrace_4937967
  have hstable : (prefixWord ++ tailWord_4937967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937967).length < 2 ^ (prefixWord ++ tailWord_4937967).sum := by decide
  have hdescent : baseEnd_4937967 < baseStart_4937967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937974 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_4937974 : Nat := 118140960795 + 4937974 * 2 ^ 59
def prefixEnd_4937974 : Nat := 4983230072969 + 3 ^ 40 * 4937974 * 2
def baseEnd_4937974 : Nat := 2535554121404768387715677

theorem tailTrace_4937974 : CollatzResearch.WordTrace tailWord_4937974 prefixEnd_4937974 2535554121404768387715677 := by
  unfold tailWord_4937974
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256419238285688228917311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120068471875047341108451317 11256419238285688228917311)
  ·
    refine ⟨16884628857428532343375967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11256419238285688228917311 16884628857428532343375967)
    ·
      refine ⟨25326943286142798515063951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16884628857428532343375967 25326943286142798515063951)
      ·
        refine ⟨37990414929214197772595927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25326943286142798515063951 37990414929214197772595927)
        ·
          refine ⟨56985622393821296658893891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37990414929214197772595927 56985622393821296658893891)
          ·
            refine ⟨85478433590731944988340837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56985622393821296658893891 85478433590731944988340837)
            ·
              refine ⟨16027206298262239685313907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85478433590731944988340837 16027206298262239685313907)
              ·
                refine ⟨24040809447393359527970861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16027206298262239685313907 24040809447393359527970861)
                ·
                  refine ⟨9015303542772509822989073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24040809447393359527970861 9015303542772509822989073)
                  ·
                    refine ⟨6761477657079382367241805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9015303542772509822989073 6761477657079382367241805)
                    ·
                      refine ⟨2535554121404768387715677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6761477657079382367241805 2535554121404768387715677)
                      ·
                        rfl

theorem cell23_4937974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_4937974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937974 prefixEnd_4937974 := by exact prefixLift 4937974
  have htrace : WordTrace (prefixWord ++ tailWord_4937974) baseStart_4937974 baseEnd_4937974 := by
    simpa [prefixWord, tailWord_4937974, baseEnd_4937974] using wordTrace_append hprefix tailTrace_4937974
  have hstable : (prefixWord ++ tailWord_4937974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937974).length < 2 ^ (prefixWord ++ tailWord_4937974).sum := by decide
  have hdescent : baseEnd_4937974 < baseStart_4937974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937987 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 3]
def baseStart_4937987 : Nat := 118140960795 + 4937987 * 2 ^ 59
def prefixEnd_4937987 : Nat := 4983230072969 + 3 ^ 40 * 4937987 * 2
def baseEnd_4937987 : Nat := 2535560796653276836853117

theorem tailTrace_4937987 : CollatzResearch.WordTrace tailWord_4937987 prefixEnd_4937987 2535560796653276836853117 := by
  unfold tailWord_4937987
  simp only [CollatzResearch.WordTrace]
  refine ⟨180103181961523914882900215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120068787974349276588600143 180103181961523914882900215)
  ·
    refine ⟨270154772942285872324350323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180103181961523914882900215 270154772942285872324350323)
    ·
      refine ⟨405232159413428808486525485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270154772942285872324350323 405232159413428808486525485)
      ·
        refine ⟨151962059780035803182447057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 405232159413428808486525485 151962059780035803182447057)
        ·
          refine ⟨113971544835026852386835293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151962059780035803182447057 113971544835026852386835293)
          ·
            refine ⟨42739329313135069645063235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113971544835026852386835293 42739329313135069645063235)
            ·
              refine ⟨64108993969702604467594853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42739329313135069645063235 64108993969702604467594853)
              ·
                refine ⟨12020436369319238337674035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64108993969702604467594853 12020436369319238337674035)
                ·
                  refine ⟨18030654553978857506511053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12020436369319238337674035 18030654553978857506511053)
                  ·
                    refine ⟨6761495457742071564941645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18030654553978857506511053 6761495457742071564941645)
                    ·
                      refine ⟨2535560796653276836853117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6761495457742071564941645 2535560796653276836853117)
                      ·
                        rfl

theorem cell23_4937987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_4937987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937987 prefixEnd_4937987 := by exact prefixLift 4937987
  have htrace : WordTrace (prefixWord ++ tailWord_4937987) baseStart_4937987 baseEnd_4937987 := by
    simpa [prefixWord, tailWord_4937987, baseEnd_4937987] using wordTrace_append hprefix tailTrace_4937987
  have hstable : (prefixWord ++ tailWord_4937987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937987).length < 2 ^ (prefixWord ++ tailWord_4937987).sum := by decide
  have hdescent : baseEnd_4937987 < baseStart_4937987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4937988 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_4937988 : Nat := 118140960795 + 4937988 * 2 ^ 59
def prefixEnd_4937988 : Nat := 4983230072969 + 3 ^ 40 * 4937988 * 2
def baseEnd_4937988 : Nat := 2535561310133931332940613

theorem tailTrace_4937988 : CollatzResearch.WordTrace tailWord_4937988 prefixEnd_4937988 2535561310133931332940613 := by
  unfold tailWord_4937988
  simp only [CollatzResearch.WordTrace]
  refine ⟨90051609217260146026843309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120068812289680194702457745 90051609217260146026843309)
  ·
    refine ⟨33769353456472554760066241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90051609217260146026843309 33769353456472554760066241)
    ·
      refine ⟨25327015092354416070049681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33769353456472554760066241 25327015092354416070049681)
      ·
        refine ⟨18995261319265812052537261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25327015092354416070049681 18995261319265812052537261)
        ·
          refine ⟨7123222994724679519701473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18995261319265812052537261 7123222994724679519701473)
          ·
            refine ⟨5342417246043509639776105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7123222994724679519701473 5342417246043509639776105)
            ·
              refine ⟨4006812934532632229832079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5342417246043509639776105 4006812934532632229832079)
              ·
                refine ⟨6010219401798948344748119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006812934532632229832079 6010219401798948344748119)
                ·
                  refine ⟨9015329102698422517122179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6010219401798948344748119 9015329102698422517122179)
                  ·
                    refine ⟨13522993654047633775683269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9015329102698422517122179 13522993654047633775683269)
                    ·
                      refine ⟨2535561310133931332940613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13522993654047633775683269 2535561310133931332940613)
                      ·
                        rfl

theorem cell23_4937988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_4937988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4937988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4937988 prefixEnd_4937988 := by exact prefixLift 4937988
  have htrace : WordTrace (prefixWord ++ tailWord_4937988) baseStart_4937988 baseEnd_4937988 := by
    simpa [prefixWord, tailWord_4937988, baseEnd_4937988] using wordTrace_append hprefix tailTrace_4937988
  have hstable : (prefixWord ++ tailWord_4937988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4937988).length < 2 ^ (prefixWord ++ tailWord_4937988).sum := by decide
  have hdescent : baseEnd_4937988 < baseStart_4937988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4937988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938021 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_4938021 : Nat := 118140960795 + 4938021 * 2 ^ 59
def prefixEnd_4938021 : Nat := 4983230072969 + 3 ^ 40 * 4938021 * 2
def baseEnd_4938021 : Nat := 2535578254995529703827961

theorem tailTrace_4938021 : CollatzResearch.WordTrace tailWord_4938021 prefixEnd_4938021 2535578254995529703827961 := by
  unfold tailWord_4938021
  simp only [CollatzResearch.WordTrace]
  refine ⟨180104422043400738689637917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120069614695600492459758611 180104422043400738689637917)
  ·
    refine ⟨67539158266275277008614219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180104422043400738689637917 67539158266275277008614219)
    ·
      refine ⟨101308737399412915512921329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67539158266275277008614219 101308737399412915512921329)
      ·
        refine ⟨75981553049559686634690997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101308737399412915512921329 75981553049559686634690997)
        ·
          refine ⟨7123270598396220622002281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75981553049559686634690997 7123270598396220622002281)
          ·
            refine ⟨5342452948797165466501711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7123270598396220622002281 5342452948797165466501711)
            ·
              refine ⟨8013679423195748199752567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342452948797165466501711 8013679423195748199752567)
              ·
                refine ⟨12020519134793622299628851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8013679423195748199752567 12020519134793622299628851)
                ·
                  refine ⟨18030778702190433449443277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12020519134793622299628851 18030778702190433449443277)
                  ·
                    refine ⟨6761542013321412543541229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18030778702190433449443277 6761542013321412543541229)
                    ·
                      refine ⟨2535578254995529703827961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6761542013321412543541229 2535578254995529703827961)
                      ·
                        rfl

theorem cell23_4938021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_4938021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938021 prefixEnd_4938021 := by exact prefixLift 4938021
  have htrace : WordTrace (prefixWord ++ tailWord_4938021) baseStart_4938021 baseEnd_4938021 := by
    simpa [prefixWord, tailWord_4938021, baseEnd_4938021] using wordTrace_append hprefix tailTrace_4938021
  have hstable : (prefixWord ++ tailWord_4938021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938021).length < 2 ^ (prefixWord ++ tailWord_4938021).sum := by decide
  have hdescent : baseEnd_4938021 < baseStart_4938021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938044 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_4938044 : Nat := 118140960795 + 4938044 * 2 ^ 59
def prefixEnd_4938044 : Nat := 4983230072969 + 3 ^ 40 * 4938044 * 2
def baseEnd_4938044 : Nat := 2535590065050583113840355

theorem tailTrace_4938044 : CollatzResearch.WordTrace tailWord_4938044 prefixEnd_4938044 2535590065050583113840355 := by
  unfold tailWord_4938044
  simp only [CollatzResearch.WordTrace]
  refine ⟨90052630461158706808862593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120070173948211609078483457 90052630461158706808862593)
  ·
    refine ⟨67539472845869030106646945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90052630461158706808862593 67539472845869030106646945)
    ·
      refine ⟨50654604634401772579985209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67539472845869030106646945 50654604634401772579985209)
      ·
        refine ⟨37990953475801329434988907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50654604634401772579985209 37990953475801329434988907)
        ·
          refine ⟨56986430213701994152483361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37990953475801329434988907 56986430213701994152483361)
          ·
            refine ⟨42739822660276495614362521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56986430213701994152483361 42739822660276495614362521)
            ·
              refine ⟨32054866995207371710771891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42739822660276495614362521 32054866995207371710771891)
              ·
                refine ⟨48082300492811057566157837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32054866995207371710771891 48082300492811057566157837)
                ·
                  refine ⟨18030862684804146587309189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48082300492811057566157837 18030862684804146587309189)
                  ·
                    refine ⟨3380786753400777485120473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18030862684804146587309189 3380786753400777485120473)
                    ·
                      refine ⟨2535590065050583113840355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380786753400777485120473 2535590065050583113840355)
                      ·
                        rfl

theorem cell23_4938044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_4938044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938044 prefixEnd_4938044 := by exact prefixLift 4938044
  have htrace : WordTrace (prefixWord ++ tailWord_4938044) baseStart_4938044 baseEnd_4938044 := by
    simpa [prefixWord, tailWord_4938044, baseEnd_4938044] using wordTrace_append hprefix tailTrace_4938044
  have hstable : (prefixWord ++ tailWord_4938044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938044).length < 2 ^ (prefixWord ++ tailWord_4938044).sum := by decide
  have hdescent : baseEnd_4938044 < baseStart_4938044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938047 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_4938047 : Nat := 118140960795 + 4938047 * 2 ^ 59
def prefixEnd_4938047 : Nat := 4983230072969 + 3 ^ 40 * 4938047 * 2
def baseEnd_4938047 : Nat := 2535591605492546602102841

theorem tailTrace_4938047 : CollatzResearch.WordTrace tailWord_4938047 prefixEnd_4938047 2535591605492546602102841 := by
  unfold tailWord_4938047
  simp only [CollatzResearch.WordTrace]
  refine ⟨180105370341306545130084395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120070246894204363420056263 180105370341306545130084395)
  ·
    refine ⟨270158055511959817695126593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180105370341306545130084395 270158055511959817695126593)
    ·
      refine ⟨202618541633969863271344945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270158055511959817695126593 202618541633969863271344945)
      ·
        refine ⟨151963906225477397453508709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202618541633969863271344945 151963906225477397453508709)
        ·
          refine ⟨28493232417277012022532883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151963906225477397453508709 28493232417277012022532883)
          ·
            refine ⟨42739848625915518033799325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28493232417277012022532883 42739848625915518033799325)
            ·
              refine ⟨16027443234718319262674747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42739848625915518033799325 16027443234718319262674747)
              ·
                refine ⟨24041164852077478894012121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16027443234718319262674747 24041164852077478894012121)
                ·
                  refine ⟨18030873639058109170509091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24041164852077478894012121 18030873639058109170509091)
                  ·
                    refine ⟨27046310458587163755763637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18030873639058109170509091 27046310458587163755763637)
                    ·
                      refine ⟨2535591605492546602102841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27046310458587163755763637 2535591605492546602102841)
                      ·
                        rfl

theorem cell23_4938047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_4938047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938047 prefixEnd_4938047 := by exact prefixLift 4938047
  have htrace : WordTrace (prefixWord ++ tailWord_4938047) baseStart_4938047 baseEnd_4938047 := by
    simpa [prefixWord, tailWord_4938047, baseEnd_4938047] using wordTrace_append hprefix tailTrace_4938047
  have hstable : (prefixWord ++ tailWord_4938047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938047).length < 2 ^ (prefixWord ++ tailWord_4938047).sum := by decide
  have hdescent : baseEnd_4938047 < baseStart_4938047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938107 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 5]
def baseStart_4938107 : Nat := 118140960795 + 4938107 * 2 ^ 59
def prefixEnd_4938107 : Nat := 4983230072969 + 3 ^ 40 * 4938107 * 2
def baseEnd_4938107 : Nat := 2535622414331816367352565

theorem tailTrace_4938107 : CollatzResearch.WordTrace tailWord_4938107 prefixEnd_4938107 2535622414331816367352565 := by
  unfold tailWord_4938107
  simp only [CollatzResearch.WordTrace]
  refine ⟨180107558721089175377268575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120071705814059450251512383 180107558721089175377268575)
  ·
    refine ⟨270161338081633763065902863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180107558721089175377268575 270161338081633763065902863)
    ·
      refine ⟨405242007122450644598854295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270161338081633763065902863 405242007122450644598854295)
      ·
        refine ⟨607863010683675966898281443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405242007122450644598854295 607863010683675966898281443)
        ·
          refine ⟨911794516025513950347422165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607863010683675966898281443 911794516025513950347422165)
          ·
            refine ⟨21370183969347983211267707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 911794516025513950347422165 21370183969347983211267707)
            ·
              refine ⟨32055275954021974816901561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21370183969347983211267707 32055275954021974816901561)
              ·
                refine ⟨24041456965516481112676171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32055275954021974816901561 24041456965516481112676171)
                ·
                  refine ⟨36062185448274721669014257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24041456965516481112676171 36062185448274721669014257)
                  ·
                    refine ⟨27046639086206041251760693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36062185448274721669014257 27046639086206041251760693)
                    ·
                      refine ⟨2535622414331816367352565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27046639086206041251760693 2535622414331816367352565)
                      ·
                        rfl

theorem cell23_4938107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_4938107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938107 prefixEnd_4938107 := by exact prefixLift 4938107
  have htrace : WordTrace (prefixWord ++ tailWord_4938107) baseStart_4938107 baseEnd_4938107 := by
    simpa [prefixWord, tailWord_4938107, baseEnd_4938107] using wordTrace_append hprefix tailTrace_4938107
  have hstable : (prefixWord ++ tailWord_4938107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938107).length < 2 ^ (prefixWord ++ tailWord_4938107).sum := by decide
  have hdescent : baseEnd_4938107 < baseStart_4938107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938117 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_4938117 : Nat := 118140960795 + 4938117 * 2 ^ 59
def prefixEnd_4938117 : Nat := 4983230072969 + 3 ^ 40 * 4938117 * 2
def baseEnd_4938117 : Nat := 2535627549138361328227519

theorem tailTrace_4938117 : CollatzResearch.WordTrace tailWord_4938117 prefixEnd_4938117 2535627549138361328227519 := by
  unfold tailWord_4938117
  simp only [CollatzResearch.WordTrace]
  refine ⟨180107923451052947085132605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120071948967368631390088403 180107923451052947085132605)
  ·
    refine ⟨67540471294144855156924727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180107923451052947085132605 67540471294144855156924727)
    ·
      refine ⟨101310706941217282735387091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67540471294144855156924727 101310706941217282735387091)
      ·
        refine ⟨151966060411825924103080637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101310706941217282735387091 151966060411825924103080637)
        ·
          refine ⟨56987272654434721538655239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151966060411825924103080637 56987272654434721538655239)
          ·
            refine ⟨85480908981652082307982859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56987272654434721538655239 85480908981652082307982859)
            ·
              refine ⟨128221363472478123461974289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85480908981652082307982859 128221363472478123461974289)
              ·
                refine ⟨96166022604358592596480717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128221363472478123461974289 96166022604358592596480717)
                ·
                  refine ⟨36062258476634472223680269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96166022604358592596480717 36062258476634472223680269)
                  ·
                    refine ⟨13523346928737927083880101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36062258476634472223680269 13523346928737927083880101)
                    ·
                      refine ⟨2535627549138361328227519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13523346928737927083880101 2535627549138361328227519)
                      ·
                        rfl

theorem cell23_4938117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_4938117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938117 prefixEnd_4938117 := by exact prefixLift 4938117
  have htrace : WordTrace (prefixWord ++ tailWord_4938117) baseStart_4938117 baseEnd_4938117 := by
    simpa [prefixWord, tailWord_4938117, baseEnd_4938117] using wordTrace_append hprefix tailTrace_4938117
  have hstable : (prefixWord ++ tailWord_4938117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938117).length < 2 ^ (prefixWord ++ tailWord_4938117).sum := by decide
  have hdescent : baseEnd_4938117 < baseStart_4938117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938144 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 5, 4]
def baseStart_4938144 : Nat := 118140960795 + 4938144 * 2 ^ 59
def prefixEnd_4938144 : Nat := 4983230072969 + 3 ^ 40 * 4938144 * 2
def baseEnd_4938144 : Nat := 845213804372010907529965

theorem tailTrace_4938144 : CollatzResearch.WordTrace tailWord_4938144 prefixEnd_4938144 845213804372010907529965 := by
  unfold tailWord_4938144
  simp only [CollatzResearch.WordTrace]
  refine ⟨90054454110977565348182743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120072605481303420464243657 90054454110977565348182743)
  ·
    refine ⟨135081681166466348022274115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90054454110977565348182743 135081681166466348022274115)
    ·
      refine ⟨202622521749699522033411173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135081681166466348022274115 202622521749699522033411173)
      ·
        refine ⟨37991722828068660381264595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202622521749699522033411173 37991722828068660381264595)
        ·
          refine ⟨56987584242102990571896893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37991722828068660381264595 56987584242102990571896893)
          ·
            refine ⟨21370344090788621464461335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56987584242102990571896893 21370344090788621464461335)
            ·
              refine ⟨32055516136182932196692003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21370344090788621464461335 32055516136182932196692003)
              ·
                refine ⟨48083274204274398295038005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32055516136182932196692003 48083274204274398295038005)
                ·
                  refine ⟨4507806956650724840159813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48083274204274398295038005 4507806956650724840159813)
                  ·
                    refine ⟨845213804372010907529965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4507806956650724840159813 845213804372010907529965)
                    ·
                      rfl

theorem cell23_4938144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 4].length) (baseStart_4938144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938144 prefixEnd_4938144 := by exact prefixLift 4938144
  have htrace : WordTrace (prefixWord ++ tailWord_4938144) baseStart_4938144 baseEnd_4938144 := by
    simpa [prefixWord, tailWord_4938144, baseEnd_4938144] using wordTrace_append hprefix tailTrace_4938144
  have hstable : (prefixWord ++ tailWord_4938144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938144).length < 2 ^ (prefixWord ++ tailWord_4938144).sum := by decide
  have hdescent : baseEnd_4938144 < baseStart_4938144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938151 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_4938151 : Nat := 118140960795 + 4938151 * 2 ^ 59
def prefixEnd_4938151 : Nat := 4983230072969 + 3 ^ 40 * 4938151 * 2
def baseEnd_4938151 : Nat := 2535645007480614195202363

theorem tailTrace_4938151 : CollatzResearch.WordTrace tailWord_4938151 prefixEnd_4938151 2535645007480614195202363 := by
  unfold tailWord_4938151
  simp only [CollatzResearch.WordTrace]
  refine ⟨180109163532929770891870307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120072775688619847261246871 180109163532929770891870307)
  ·
    refine ⟨270163745299394656337805461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180109163532929770891870307 270163745299394656337805461)
    ·
      refine ⟨12663925560909124515834631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 270163745299394656337805461 12663925560909124515834631)
      ·
        refine ⟨18995888341363686773751947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12663925560909124515834631 18995888341363686773751947)
        ·
          refine ⟨28493832512045530160627921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18995888341363686773751947 28493832512045530160627921)
          ·
            refine ⟨21370374384034147620470941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28493832512045530160627921 21370374384034147620470941)
            ·
              refine ⟨8013890394012805357676603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21370374384034147620470941 8013890394012805357676603)
              ·
                refine ⟨12020835591019208036514905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8013890394012805357676603 12020835591019208036514905)
                ·
                  refine ⟨9015626693264406027386179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12020835591019208036514905 9015626693264406027386179)
                  ·
                    refine ⟨13523440039896609041079269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9015626693264406027386179 13523440039896609041079269)
                    ·
                      refine ⟨2535645007480614195202363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13523440039896609041079269 2535645007480614195202363)
                      ·
                        rfl

theorem cell23_4938151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_4938151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938151 prefixEnd_4938151 := by exact prefixLift 4938151
  have htrace : WordTrace (prefixWord ++ tailWord_4938151) baseStart_4938151 baseEnd_4938151 := by
    simpa [prefixWord, tailWord_4938151, baseEnd_4938151] using wordTrace_append hprefix tailTrace_4938151
  have hstable : (prefixWord ++ tailWord_4938151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938151).length < 2 ^ (prefixWord ++ tailWord_4938151).sum := by decide
  have hdescent : baseEnd_4938151 < baseStart_4938151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938201 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 3]
def baseStart_4938201 : Nat := 118140960795 + 4938201 * 2 ^ 59
def prefixEnd_4938201 : Nat := 4983230072969 + 3 ^ 40 * 4938201 * 2
def baseEnd_4938201 : Nat := 2535670681513338999577133

theorem tailTrace_4938201 : CollatzResearch.WordTrace tailWord_4938201 prefixEnd_4938201 2535670681513338999577133 := by
  unfold tailWord_4938201
  simp only [CollatzResearch.WordTrace]
  refine ⟨180110987182748629431190457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120073991455165752954126971 180110987182748629431190457)
  ·
    refine ⟨135083240387061472073392843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180110987182748629431190457 135083240387061472073392843)
    ·
      refine ⟨202624860580592208110089265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135083240387061472073392843 202624860580592208110089265)
      ·
        refine ⟨151968645435444156082566949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202624860580592208110089265 151968645435444156082566949)
        ·
          refine ⟨28494121019145779265481303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151968645435444156082566949 28494121019145779265481303)
          ·
            refine ⟨42741181528718668898221955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28494121019145779265481303 42741181528718668898221955)
            ·
              refine ⟨64111772293078003347332933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42741181528718668898221955 64111772293078003347332933)
              ·
                refine ⟨12020957304952125627624925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64111772293078003347332933 12020957304952125627624925)
                ·
                  refine ⟨4507858989357047110359347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12020957304952125627624925 4507858989357047110359347)
                  ·
                    refine ⟨6761788484035570665539021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4507858989357047110359347 6761788484035570665539021)
                    ·
                      refine ⟨2535670681513338999577133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6761788484035570665539021 2535670681513338999577133)
                      ·
                        rfl

theorem cell23_4938201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_4938201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938201 prefixEnd_4938201 := by exact prefixLift 4938201
  have htrace : WordTrace (prefixWord ++ tailWord_4938201) baseStart_4938201 baseEnd_4938201 := by
    simpa [prefixWord, tailWord_4938201, baseEnd_4938201] using wordTrace_append hprefix tailTrace_4938201
  have hstable : (prefixWord ++ tailWord_4938201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938201).length < 2 ^ (prefixWord ++ tailWord_4938201).sum := by decide
  have hdescent : baseEnd_4938201 < baseStart_4938201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938242 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 6]
def baseStart_4938242 : Nat := 118140960795 + 4938242 * 2 ^ 59
def prefixEnd_4938242 : Nat := 4983230072969 + 3 ^ 40 * 4938242 * 2
def baseEnd_4938242 : Nat := 281743526024463704351605

theorem tailTrace_4938242 : CollatzResearch.WordTrace tailWord_4938242 prefixEnd_4938242 281743526024463704351605 := by
  unfold tailWord_4938242
  simp only [CollatzResearch.WordTrace]
  refine ⟨45028120643900023358358245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120074988383733395622288653 45028120643900023358358245)
  ·
    refine ⟨8442772620731254379692171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45028120643900023358358245 8442772620731254379692171)
    ·
      refine ⟨12664158931096881569538257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8442772620731254379692171 12664158931096881569538257)
      ·
        refine ⟨9498119198322661177153693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12664158931096881569538257 9498119198322661177153693)
        ·
          refine ⟨3561794699370997941432635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9498119198322661177153693 3561794699370997941432635)
          ·
            refine ⟨5342692049056496912148953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561794699370997941432635 5342692049056496912148953)
            ·
              refine ⟨4007019036792372684111715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5342692049056496912148953 4007019036792372684111715)
              ·
                refine ⟨6010528555188559026167573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4007019036792372684111715 6010528555188559026167573)
                ·
                  refine ⟨281743526024463704351605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6010528555188559026167573 281743526024463704351605)
                  ·
                    rfl

theorem cell23_4938242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_4938242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938242 prefixEnd_4938242 := by exact prefixLift 4938242
  have htrace : WordTrace (prefixWord ++ tailWord_4938242) baseStart_4938242 baseEnd_4938242 := by
    simpa [prefixWord, tailWord_4938242, baseEnd_4938242] using wordTrace_append hprefix tailTrace_4938242
  have hstable : (prefixWord ++ tailWord_4938242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938242).length < 2 ^ (prefixWord ++ tailWord_4938242).sum := by decide
  have hdescent : baseEnd_4938242 < baseStart_4938242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938261 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_4938261 : Nat := 118140960795 + 4938261 * 2 ^ 59
def prefixEnd_4938261 : Nat := 4983230072969 + 3 ^ 40 * 4938261 * 2
def baseEnd_4938261 : Nat := 2535701490352608764826857

theorem tailTrace_4938261 : CollatzResearch.WordTrace tailWord_4938261 prefixEnd_4938261 2535701490352608764826857 := by
  unfold tailWord_4938261
  simp only [CollatzResearch.WordTrace]
  refine ⟨180113175562531259678374637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120075450375020839785583091 180113175562531259678374637)
  ·
    refine ⟨67542440835949222379390489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180113175562531259678374637 67542440835949222379390489)
    ·
      refine ⟨50656830626961916784542867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67542440835949222379390489 50656830626961916784542867)
      ·
        refine ⟨75985245940442875176814301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50656830626961916784542867 75985245940442875176814301)
        ·
          refine ⟨28494467227666078191305363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75985245940442875176814301 28494467227666078191305363)
          ·
            refine ⟨42741700841499117286958045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28494467227666078191305363 42741700841499117286958045)
            ·
              refine ⟨16028137815562168982609267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42741700841499117286958045 16028137815562168982609267)
              ·
                refine ⟨24042206723343253473913901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16028137815562168982609267 24042206723343253473913901)
                ·
                  refine ⟨9015827521253720052717713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24042206723343253473913901 9015827521253720052717713)
                  ·
                    refine ⟨6761870640940290039538285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9015827521253720052717713 6761870640940290039538285)
                    ·
                      refine ⟨2535701490352608764826857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6761870640940290039538285 2535701490352608764826857)
                      ·
                        rfl

theorem cell23_4938261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_4938261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938261 prefixEnd_4938261 := by exact prefixLift 4938261
  have htrace : WordTrace (prefixWord ++ tailWord_4938261) baseStart_4938261 baseEnd_4938261 := by
    simpa [prefixWord, tailWord_4938261, baseEnd_4938261] using wordTrace_append hprefix tailTrace_4938261
  have hstable : (prefixWord ++ tailWord_4938261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938261).length < 2 ^ (prefixWord ++ tailWord_4938261).sum := by decide
  have hdescent : baseEnd_4938261 < baseStart_4938261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938264 : List Nat := [2, 1, 2, 3, 3, 1, 2, 9]
def baseStart_4938264 : Nat := 118140960795 + 4938264 * 2 ^ 59
def prefixEnd_4938264 : Nat := 4983230072969 + 3 ^ 40 * 4938264 * 2
def baseEnd_4938264 : Nat := 93914927066465639003309

theorem tailTrace_4938264 : CollatzResearch.WordTrace tailWord_4938264 prefixEnd_4938264 93914927066465639003309 := by
  unfold tailWord_4938264
  simp only [CollatzResearch.WordTrace]
  refine ⟨90056642490760195595366923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120075523321013594127155897 90056642490760195595366923)
  ·
    refine ⟨135084963736140293393050385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90056642490760195595366923 135084963736140293393050385)
    ·
      refine ⟨101313722802105220044787789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135084963736140293393050385 101313722802105220044787789)
      ·
        refine ⟨37992646050789457516795421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101313722802105220044787789 37992646050789457516795421)
        ·
          refine ⟨14247242269046046568798283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37992646050789457516795421 14247242269046046568798283)
          ·
            refine ⟨21370863403569069853197425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14247242269046046568798283 21370863403569069853197425)
            ·
              refine ⟨16028147552676802389898069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21370863403569069853197425 16028147552676802389898069)
              ·
                refine ⟨93914927066465639003309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16028147552676802389898069 93914927066465639003309)
                ·
                  rfl

theorem cell23_4938264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 9].length) (baseStart_4938264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938264 prefixEnd_4938264 := by exact prefixLift 4938264
  have htrace : WordTrace (prefixWord ++ tailWord_4938264) baseStart_4938264 baseEnd_4938264 := by
    simpa [prefixWord, tailWord_4938264, baseEnd_4938264] using wordTrace_append hprefix tailTrace_4938264
  have hstable : (prefixWord ++ tailWord_4938264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938264).length < 2 ^ (prefixWord ++ tailWord_4938264).sum := by decide
  have hdescent : baseEnd_4938264 < baseStart_4938264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938286 : List Nat := [4, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_4938286 : Nat := 118140960795 + 4938286 * 2 ^ 59
def prefixEnd_4938286 : Nat := 4983230072969 + 3 ^ 40 * 4938286 * 2
def baseEnd_4938286 : Nat := 2535714327368971167014243

theorem tailTrace_4938286 : CollatzResearch.WordTrace tailWord_4938286 prefixEnd_4938286 2535714327368971167014243 := by
  unfold tailWord_4938286
  simp only [CollatzResearch.WordTrace]
  refine ⟨22514260923430086118504339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120076058258293792632023141 22514260923430086118504339)
  ·
    refine ⟨33771391385145129177756509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22514260923430086118504339 33771391385145129177756509)
    ·
      refine ⟨12664271769429423441658691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33771391385145129177756509 12664271769429423441658691)
      ·
        refine ⟨18996407654144135162488037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12664271769429423441658691 18996407654144135162488037)
        ·
          refine ⟨3561826435152025342966507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18996407654144135162488037 3561826435152025342966507)
          ·
            refine ⟨5342739652728038014449761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561826435152025342966507 5342739652728038014449761)
            ·
              refine ⟨4007054739546028510837321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5342739652728038014449761 4007054739546028510837321)
              ·
                refine ⟨3005291054659521383127991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4007054739546028510837321 3005291054659521383127991)
                ·
                  refine ⟨4507936581989282074691987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005291054659521383127991 4507936581989282074691987)
                  ·
                    refine ⟨6761904872983923112037981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4507936581989282074691987 6761904872983923112037981)
                    ·
                      refine ⟨2535714327368971167014243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6761904872983923112037981 2535714327368971167014243)
                      ·
                        rfl

theorem cell23_4938286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_4938286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938286 prefixEnd_4938286 := by exact prefixLift 4938286
  have htrace : WordTrace (prefixWord ++ tailWord_4938286) baseStart_4938286 baseEnd_4938286 := by
    simpa [prefixWord, tailWord_4938286, baseEnd_4938286] using wordTrace_append hprefix tailTrace_4938286
  have hstable : (prefixWord ++ tailWord_4938286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938286).length < 2 ^ (prefixWord ++ tailWord_4938286).sum := by decide
  have hdescent : baseEnd_4938286 < baseStart_4938286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938318 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_4938318 : Nat := 118140960795 + 4938318 * 2 ^ 59
def prefixEnd_4938318 : Nat := 4983230072969 + 3 ^ 40 * 4938318 * 2
def baseEnd_4938318 : Nat := 2535730758749915041814095

theorem tailTrace_4938318 : CollatzResearch.WordTrace tailWord_4938318 prefixEnd_4938318 2535730758749915041814095 := by
  unfold tailWord_4938318
  simp only [CollatzResearch.WordTrace]
  refine ⟨22514406815415594801649951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120076836348883172275466405 22514406815415594801649951)
  ·
    refine ⟨33771610223123392202474927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22514406815415594801649951 33771610223123392202474927)
    ·
      refine ⟨50657415334685088303712391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33771610223123392202474927 50657415334685088303712391)
      ·
        refine ⟨75986123002027632455568587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50657415334685088303712391 75986123002027632455568587)
        ·
          refine ⟨113979184503041448683352881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75986123002027632455568587 113979184503041448683352881)
          ·
            refine ⟨85484388377281086512514661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113979184503041448683352881 85484388377281086512514661)
            ·
              refine ⟨16028322820740203721096499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85484388377281086512514661 16028322820740203721096499)
              ·
                refine ⟨24042484231110305581644749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16028322820740203721096499 24042484231110305581644749)
                ·
                  refine ⟨9015931586666364593116781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24042484231110305581644749 9015931586666364593116781)
                  ·
                    refine ⟨3380974344999886722418793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9015931586666364593116781 3380974344999886722418793)
                    ·
                      refine ⟨2535730758749915041814095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3380974344999886722418793 2535730758749915041814095)
                      ·
                        rfl

theorem cell23_4938318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_4938318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938318 prefixEnd_4938318 := by exact prefixLift 4938318
  have htrace : WordTrace (prefixWord ++ tailWord_4938318) baseStart_4938318 baseEnd_4938318 := by
    simpa [prefixWord, tailWord_4938318, baseEnd_4938318] using wordTrace_append hprefix tailTrace_4938318
  have hstable : (prefixWord ++ tailWord_4938318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938318).length < 2 ^ (prefixWord ++ tailWord_4938318).sum := by decide
  have hdescent : baseEnd_4938318 < baseStart_4938318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938361 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_4938361 : Nat := 118140960795 + 4938361 * 2 ^ 59
def prefixEnd_4938361 : Nat := 4983230072969 + 3 ^ 40 * 4938361 * 2
def baseEnd_4938361 : Nat := 2535752838418058373576397

theorem tailTrace_4938361 : CollatzResearch.WordTrace tailWord_4938361 prefixEnd_4938361 2535752838418058373576397 := by
  unfold tailWord_4938361
  simp only [CollatzResearch.WordTrace]
  refine ⟨180116822862168976757014937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120077881908112651171343291 180116822862168976757014937)
  ·
    refine ⟨135087617146626732567761203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180116822862168976757014937 135087617146626732567761203)
    ·
      refine ⟨202631425719940098851641805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135087617146626732567761203 202631425719940098851641805)
      ·
        refine ⟨75986784644977537069365677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202631425719940098851641805 75986784644977537069365677)
        ·
          refine ⟨28495044241866576401012129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75986784644977537069365677 28495044241866576401012129)
          ·
            refine ⟨21371283181399932300759097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28495044241866576401012129 21371283181399932300759097)
            ·
              refine ⟨16028462386049949225569323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21371283181399932300759097 16028462386049949225569323)
              ·
                refine ⟨24042693579074923838353985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16028462386049949225569323 24042693579074923838353985)
                ·
                  refine ⟨18032020184306192878765489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24042693579074923838353985 18032020184306192878765489)
                  ·
                    refine ⟨13524015138229644659074117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18032020184306192878765489 13524015138229644659074117)
                    ·
                      refine ⟨2535752838418058373576397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13524015138229644659074117 2535752838418058373576397)
                      ·
                        rfl

theorem cell23_4938361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_4938361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938361 prefixEnd_4938361 := by exact prefixLift 4938361
  have htrace : WordTrace (prefixWord ++ tailWord_4938361) baseStart_4938361 baseEnd_4938361 := by
    simpa [prefixWord, tailWord_4938361, baseEnd_4938361] using wordTrace_append hprefix tailTrace_4938361
  have hstable : (prefixWord ++ tailWord_4938361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938361).length < 2 ^ (prefixWord ++ tailWord_4938361).sum := by decide
  have hdescent : baseEnd_4938361 < baseStart_4938361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938458 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_4938458 : Nat := 118140960795 + 4938458 * 2 ^ 59
def prefixEnd_4938458 : Nat := 4983230072969 + 3 ^ 40 * 4938458 * 2
def baseEnd_4938458 : Nat := 2535802646041544494063451

theorem tailTrace_4938458 : CollatzResearch.WordTrace tailWord_4938458 prefixEnd_4938458 2535802646041544494063451 := by
  unfold tailWord_4938458
  simp only [CollatzResearch.WordTrace]
  refine ⟨45030090185704390580824007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120080240495211708215530685 45030090185704390580824007)
  ·
    refine ⟨67545135278556585871236011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45030090185704390580824007 67545135278556585871236011)
    ·
      refine ⟨101317702917834878806854017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67545135278556585871236011 101317702917834878806854017)
      ·
        refine ⟨75988277188376159105140513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101317702917834878806854017 75988277188376159105140513)
        ·
          refine ⟨56991207891282119328855385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75988277188376159105140513 56991207891282119328855385)
          ·
            refine ⟨42743405918461589496641539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56991207891282119328855385 42743405918461589496641539)
            ·
              refine ⟨64115108877692384244962309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42743405918461589496641539 64115108877692384244962309)
              ·
                refine ⟨12021582914567322045930433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64115108877692384244962309 12021582914567322045930433)
                ·
                  refine ⟨9016187185925491534447825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12021582914567322045930433 9016187185925491534447825)
                  ·
                    refine ⟨6762140389444118650835869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9016187185925491534447825 6762140389444118650835869)
                    ·
                      refine ⟨2535802646041544494063451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6762140389444118650835869 2535802646041544494063451)
                      ·
                        rfl

theorem cell23_4938458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_4938458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938458 prefixEnd_4938458 := by exact prefixLift 4938458
  have htrace : WordTrace (prefixWord ++ tailWord_4938458) baseStart_4938458 baseEnd_4938458 := by
    simpa [prefixWord, tailWord_4938458, baseEnd_4938458] using wordTrace_append hprefix tailTrace_4938458
  have hstable : (prefixWord ++ tailWord_4938458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938458).length < 2 ^ (prefixWord ++ tailWord_4938458).sum := by decide
  have hdescent : baseEnd_4938458 < baseStart_4938458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938478 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_4938478 : Nat := 118140960795 + 4938478 * 2 ^ 59
def prefixEnd_4938478 : Nat := 4983230072969 + 3 ^ 40 * 4938478 * 2
def baseEnd_4938478 : Nat := 281756990628292712868151

theorem tailTrace_4938478 : CollatzResearch.WordTrace tailWord_4938478 prefixEnd_4938478 281756990628292712868151 := by
  unfold tailWord_4938478
  simp only [CollatzResearch.WordTrace]
  refine ⟨22515136275343138217378011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120080726801830070492682725 22515136275343138217378011)
  ·
    refine ⟨33772704413014707326067017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22515136275343138217378011 33772704413014707326067017)
    ·
      refine ⟨25329528309761030494550263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33772704413014707326067017 25329528309761030494550263)
      ·
        refine ⟨37994292464641545741825395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25329528309761030494550263 37994292464641545741825395)
        ·
          refine ⟨56991438696962318612738093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37994292464641545741825395 56991438696962318612738093)
          ·
            refine ⟨21371789511360869479776785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56991438696962318612738093 21371789511360869479776785)
            ·
              refine ⟨16028842133520652109832589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21371789511360869479776785 16028842133520652109832589)
              ·
                refine ⟨6010815800070244541187221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16028842133520652109832589 6010815800070244541187221)
                ·
                  refine ⟨281756990628292712868151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6010815800070244541187221 281756990628292712868151)
                  ·
                    rfl

theorem cell23_4938478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_4938478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938478 prefixEnd_4938478 := by exact prefixLift 4938478
  have htrace : WordTrace (prefixWord ++ tailWord_4938478) baseStart_4938478 baseEnd_4938478 := by
    simpa [prefixWord, tailWord_4938478, baseEnd_4938478] using wordTrace_append hprefix tailTrace_4938478
  have hstable : (prefixWord ++ tailWord_4938478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938478).length < 2 ^ (prefixWord ++ tailWord_4938478).sum := by decide
  have hdescent : baseEnd_4938478 < baseStart_4938478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938522 : List Nat := [3, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3]
def baseStart_4938522 : Nat := 118140960795 + 4938522 * 2 ^ 59
def prefixEnd_4938522 : Nat := 4983230072969 + 3 ^ 40 * 4938522 * 2
def baseEnd_4938522 : Nat := 2535835508803432243663157

theorem tailTrace_4938522 : CollatzResearch.WordTrace tailWord_4938522 prefixEnd_4938522 2535835508803432243663157 := by
  unfold tailWord_4938522
  simp only [CollatzResearch.WordTrace]
  refine ⟨45030673753646425313406455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120081796676390467502417213 45030673753646425313406455)
  ·
    refine ⟨67546010630469637970109683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45030673753646425313406455 67546010630469637970109683)
    ·
      refine ⟨101319015945704456955164525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67546010630469637970109683 101319015945704456955164525)
      ·
        refine ⟨37994630979639171358186697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101319015945704456955164525 37994630979639171358186697)
        ·
          refine ⟨28495973234729378518640023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37994630979639171358186697 28495973234729378518640023)
          ·
            refine ⟨42743959852094067777960035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28495973234729378518640023 42743959852094067777960035)
            ·
              refine ⟨64115939778141101666940053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42743959852094067777960035 64115939778141101666940053)
              ·
                refine ⟨3005434677100364140637815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64115939778141101666940053 3005434677100364140637815)
                ·
                  refine ⟨4508152015650546210956723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005434677100364140637815 4508152015650546210956723)
                  ·
                    refine ⟨6762228023475819316435085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4508152015650546210956723 6762228023475819316435085)
                    ·
                      refine ⟨2535835508803432243663157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6762228023475819316435085 2535835508803432243663157)
                      ·
                        rfl

theorem cell23_4938522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_4938522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938522 prefixEnd_4938522 := by exact prefixLift 4938522
  have htrace : WordTrace (prefixWord ++ tailWord_4938522) baseStart_4938522 baseEnd_4938522 := by
    simpa [prefixWord, tailWord_4938522, baseEnd_4938522] using wordTrace_append hprefix tailTrace_4938522
  have hstable : (prefixWord ++ tailWord_4938522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938522).length < 2 ^ (prefixWord ++ tailWord_4938522).sum := by decide
  have hdescent : baseEnd_4938522 < baseStart_4938522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938542 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_4938542 : Nat := 118140960795 + 4938542 * 2 ^ 59
def prefixEnd_4938542 : Nat := 4983230072969 + 3 ^ 40 * 4938542 * 2
def baseEnd_4938542 : Nat := 845281926138840721804355

theorem tailTrace_4938542 : CollatzResearch.WordTrace tailWord_4938542 prefixEnd_4938542 845281926138840721804355 := by
  unfold tailWord_4938542
  simp only [CollatzResearch.WordTrace]
  refine ⟨22515428059314155583669235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120082282983008829779569253 22515428059314155583669235)
  ·
    refine ⟨33773142088971233375503853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22515428059314155583669235 33773142088971233375503853)
    ·
      refine ⟨12664928283364212515813945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33773142088971233375503853 12664928283364212515813945)
      ·
        refine ⟨9498696212523159386860459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12664928283364212515813945 9498696212523159386860459)
        ·
          refine ⟨14248044318784739080290689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9498696212523159386860459 14248044318784739080290689)
          ·
            refine ⟨10686033239088554310218017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14248044318784739080290689 10686033239088554310218017)
            ·
              refine ⟨8014524929316415732663513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10686033239088554310218017 8014524929316415732663513)
              ·
                refine ⟨6010893696987311799497635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8014524929316415732663513 6010893696987311799497635)
                ·
                  refine ⟨9016340545480967699246453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6010893696987311799497635 9016340545480967699246453)
                  ·
                    refine ⟨845281926138840721804355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9016340545480967699246453 845281926138840721804355)
                    ·
                      rfl

theorem cell23_4938542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_4938542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938542 prefixEnd_4938542 := by exact prefixLift 4938542
  have htrace : WordTrace (prefixWord ++ tailWord_4938542) baseStart_4938542 baseEnd_4938542 := by
    simpa [prefixWord, tailWord_4938542, baseEnd_4938542] using wordTrace_append hprefix tailTrace_4938542
  have hstable : (prefixWord ++ tailWord_4938542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938542).length < 2 ^ (prefixWord ++ tailWord_4938542).sum := by decide
  have hdescent : baseEnd_4938542 < baseStart_4938542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938545 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_4938545 : Nat := 118140960795 + 4938545 * 2 ^ 59
def prefixEnd_4938545 : Nat := 4983230072969 + 3 ^ 40 * 4938545 * 2
def baseEnd_4938545 : Nat := 2535847318858485653675551

theorem tailTrace_4938545 : CollatzResearch.WordTrace tailWord_4938545 prefixEnd_4938545 2535847318858485653675551 := by
  unfold tailWord_4938545
  simp only [CollatzResearch.WordTrace]
  refine ⟨180123533893502376181713089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120082355929001584121142059 180123533893502376181713089)
  ·
    refine ⟨135092650420126782136284817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180123533893502376181713089 135092650420126782136284817)
    ·
      refine ⟨101319487815095086602213613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135092650420126782136284817 101319487815095086602213613)
      ·
        refine ⟨37994807930660657475830105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101319487815095086602213613 37994807930660657475830105)
        ·
          refine ⟨28496105947995493106872579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37994807930660657475830105 28496105947995493106872579)
          ·
            refine ⟨42744158921993239660308869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28496105947995493106872579 42744158921993239660308869)
            ·
              refine ⟨8014529797873732436307913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42744158921993239660308869 8014529797873732436307913)
              ·
                refine ⟨6010897348405299327230935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8014529797873732436307913 6010897348405299327230935)
                ·
                  refine ⟨9016346022607948990846403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6010897348405299327230935 9016346022607948990846403)
                  ·
                    refine ⟨13524519033911923486269605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9016346022607948990846403 13524519033911923486269605)
                    ·
                      refine ⟨2535847318858485653675551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13524519033911923486269605 2535847318858485653675551)
                      ·
                        rfl

theorem cell23_4938545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_4938545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938545 prefixEnd_4938545 := by exact prefixLift 4938545
  have htrace : WordTrace (prefixWord ++ tailWord_4938545) baseStart_4938545 baseEnd_4938545 := by
    simpa [prefixWord, tailWord_4938545, baseEnd_4938545] using wordTrace_append hprefix tailTrace_4938545
  have hstable : (prefixWord ++ tailWord_4938545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938545).length < 2 ^ (prefixWord ++ tailWord_4938545).sum := by decide
  have hdescent : baseEnd_4938545 < baseStart_4938545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938551 : List Nat := [1, 1, 3, 1, 2, 1, 5, 9]
def baseStart_4938551 : Nat := 118140960795 + 4938551 * 2 ^ 59
def prefixEnd_4938551 : Nat := 4983230072969 + 3 ^ 40 * 4938551 * 2
def baseEnd_4938551 : Nat := 93920385175644912229649

theorem tailTrace_4938551 : CollatzResearch.WordTrace tailWord_4938551 prefixEnd_4938551 93920385175644912229649 := by
  unfold tailWord_4938551
  simp only [CollatzResearch.WordTrace]
  refine ⟨180123752731480639206431507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120082501820987092804287671 180123752731480639206431507)
  ·
    refine ⟨270185629097220958809647261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180123752731480639206431507 270185629097220958809647261)
    ·
      refine ⟨101319610911457859553617723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270185629097220958809647261 101319610911457859553617723)
      ·
        refine ⟨151979416367186789330426585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101319610911457859553617723 151979416367186789330426585)
        ·
          refine ⟨113984562275390091997819939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151979416367186789330426585 113984562275390091997819939)
          ·
            refine ⟨170976843413085137996729909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113984562275390091997819939 170976843413085137996729909)
            ·
              refine ⟨16029079069976731687193429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170976843413085137996729909 16029079069976731687193429)
              ·
                refine ⟨93920385175644912229649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16029079069976731687193429 93920385175644912229649)
                ·
                  rfl

theorem cell23_4938551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 9].length) (baseStart_4938551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938551 prefixEnd_4938551 := by exact prefixLift 4938551
  have htrace : WordTrace (prefixWord ++ tailWord_4938551) baseStart_4938551 baseEnd_4938551 := by
    simpa [prefixWord, tailWord_4938551, baseEnd_4938551] using wordTrace_append hprefix tailTrace_4938551
  have hstable : (prefixWord ++ tailWord_4938551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938551).length < 2 ^ (prefixWord ++ tailWord_4938551).sum := by decide
  have hdescent : baseEnd_4938551 < baseStart_4938551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938566 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4938566 : Nat := 118140960795 + 4938566 * 2 ^ 59
def prefixEnd_4938566 : Nat := 4983230072969 + 3 ^ 40 * 4938566 * 2
def baseEnd_4938566 : Nat := 2535858101952230071512955

theorem tailTrace_4938566 : CollatzResearch.WordTrace tailWord_4938566 prefixEnd_4938566 2535858101952230071512955 := by
  unfold tailWord_4938566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628884369575821774007111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120082866550950864512151701 5628884369575821774007111)
  ·
    refine ⟨8443326554363732661010667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5628884369575821774007111 8443326554363732661010667)
    ·
      refine ⟨12664989831545598991516001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8443326554363732661010667 12664989831545598991516001)
      ·
        refine ⟨9498742373659199243637001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12664989831545598991516001 9498742373659199243637001)
        ·
          refine ⟨7124056780244399432727751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9498742373659199243637001 7124056780244399432727751)
          ·
            refine ⟨10686085170366599149091627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7124056780244399432727751 10686085170366599149091627)
            ·
              refine ⟨16029127755549898723637441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10686085170366599149091627 16029127755549898723637441)
              ·
                refine ⟨12021845816662424042728081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16029127755549898723637441 12021845816662424042728081)
                ·
                  refine ⟨9016384362496818032046061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12021845816662424042728081 9016384362496818032046061)
                  ·
                    refine ⟨3381144135936306762017273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9016384362496818032046061 3381144135936306762017273)
                    ·
                      refine ⟨2535858101952230071512955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381144135936306762017273 2535858101952230071512955)
                      ·
                        rfl

theorem cell23_4938566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4938566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938566 prefixEnd_4938566 := by exact prefixLift 4938566
  have htrace : WordTrace (prefixWord ++ tailWord_4938566) baseStart_4938566 baseEnd_4938566 := by
    simpa [prefixWord, tailWord_4938566, baseEnd_4938566] using wordTrace_append hprefix tailTrace_4938566
  have hstable : (prefixWord ++ tailWord_4938566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938566).length < 2 ^ (prefixWord ++ tailWord_4938566).sum := by decide
  have hdescent : baseEnd_4938566 < baseStart_4938566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938573 : List Nat := [1, 6, 1, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_4938573 : Nat := 118140960795 + 4938573 * 2 ^ 59
def prefixEnd_4938573 : Nat := 4983230072969 + 3 ^ 40 * 4938573 * 2
def baseEnd_4938573 : Nat := 2535861696316811544125423

theorem tailTrace_4938573 : CollatzResearch.WordTrace tailWord_4938573 prefixEnd_4938573 2535861696316811544125423 := by
  unfold tailWord_4938573
  simp only [CollatzResearch.WordTrace]
  refine ⟨180124555137400936963732373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120083036758267291309154915 180124555137400936963732373)
  ·
    refine ⟨8443338522065668920174955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 180124555137400936963732373 8443338522065668920174955)
    ·
      refine ⟨12665007783098503380262433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8443338522065668920174955 12665007783098503380262433)
      ·
        refine ⟨9498755837323877535196825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12665007783098503380262433 9498755837323877535196825)
        ·
          refine ⟨7124066877992908151397619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9498755837323877535196825 7124066877992908151397619)
          ·
            refine ⟨10686100316989362227096429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7124066877992908151397619 10686100316989362227096429)
            ·
              refine ⟨4007287618871010835161161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10686100316989362227096429 4007287618871010835161161)
              ·
                refine ⟨3005465714153258126370871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4007287618871010835161161 3005465714153258126370871)
                ·
                  refine ⟨4508198571229887189556307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005465714153258126370871 4508198571229887189556307)
                  ·
                    refine ⟨6762297856844830784334461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4508198571229887189556307 6762297856844830784334461)
                    ·
                      refine ⟨2535861696316811544125423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6762297856844830784334461 2535861696316811544125423)
                      ·
                        rfl

theorem cell23_4938573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_4938573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938573 prefixEnd_4938573 := by exact prefixLift 4938573
  have htrace : WordTrace (prefixWord ++ tailWord_4938573) baseStart_4938573 baseEnd_4938573 := by
    simpa [prefixWord, tailWord_4938573, baseEnd_4938573] using wordTrace_append hprefix tailTrace_4938573
  have hstable : (prefixWord ++ tailWord_4938573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938573).length < 2 ^ (prefixWord ++ tailWord_4938573).sum := by decide
  have hdescent : baseEnd_4938573 < baseStart_4938573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938601 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_4938601 : Nat := 118140960795 + 4938601 * 2 ^ 59
def prefixEnd_4938601 : Nat := 4983230072969 + 3 ^ 40 * 4938601 * 2
def baseEnd_4938601 : Nat := 2535876073775137434575293

theorem tailTrace_4938601 : CollatzResearch.WordTrace tailWord_4938601 prefixEnd_4938601 2535876073775137434575293 := by
  unfold tailWord_4938601
  simp only [CollatzResearch.WordTrace]
  refine ⟨180125576381299497745751657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120083717587532998497167771 180125576381299497745751657)
  ·
    refine ⟨135094182285974623309313743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180125576381299497745751657 135094182285974623309313743)
    ·
      refine ⟨202641273428961934963970615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135094182285974623309313743 202641273428961934963970615)
      ·
        refine ⟨303961910143442902445955923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202641273428961934963970615 303961910143442902445955923)
        ·
          refine ⟨455942865215164353668933885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303961910143442902445955923 455942865215164353668933885)
          ·
            refine ⟨170978574455686632625850207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455942865215164353668933885 170978574455686632625850207)
            ·
              refine ⟨256467861683529948938775311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170978574455686632625850207 256467861683529948938775311)
              ·
                refine ⟨384701792525294923408162967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256467861683529948938775311 384701792525294923408162967)
                ·
                  refine ⟨577052688787942385112244451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384701792525294923408162967 577052688787942385112244451)
                  ·
                    refine ⟨865579033181913577668366677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 577052688787942385112244451 865579033181913577668366677)
                    ·
                      refine ⟨2535876073775137434575293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 865579033181913577668366677 2535876073775137434575293)
                      ·
                        rfl

theorem cell23_4938601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_4938601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938601 prefixEnd_4938601 := by exact prefixLift 4938601
  have htrace : WordTrace (prefixWord ++ tailWord_4938601) baseStart_4938601 baseEnd_4938601 := by
    simpa [prefixWord, tailWord_4938601, baseEnd_4938601] using wordTrace_append hprefix tailTrace_4938601
  have hstable : (prefixWord ++ tailWord_4938601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938601).length < 2 ^ (prefixWord ++ tailWord_4938601).sum := by decide
  have hdescent : baseEnd_4938601 < baseStart_4938601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938628 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_4938628 : Nat := 118140960795 + 4938628 * 2 ^ 59
def prefixEnd_4938628 : Nat := 4983230072969 + 3 ^ 40 * 4938628 * 2
def baseEnd_4938628 : Nat := 845296645917602942979223

theorem tailTrace_4938628 : CollatzResearch.WordTrace tailWord_4938628 prefixEnd_4938628 845296645917602942979223 := by
  unfold tailWord_4938628
  simp only [CollatzResearch.WordTrace]
  refine ⟨90063280576100840678492269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120084374101467787571323025 90063280576100840678492269)
  ·
    refine ⟨33773730216037815254434601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90063280576100840678492269 33773730216037815254434601)
    ·
      refine ⟨25330297662028361440825951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33773730216037815254434601 25330297662028361440825951)
      ·
        refine ⟨37995446493042542161238927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25330297662028361440825951 37995446493042542161238927)
        ·
          refine ⟨56993169739563813241858391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37995446493042542161238927 56993169739563813241858391)
          ·
            refine ⟨85489754609345719862787587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56993169739563813241858391 85489754609345719862787587)
            ·
              refine ⟨128234631914018579794181381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85489754609345719862787587 128234631914018579794181381)
              ·
                refine ⟨24043993483878483711409009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128234631914018579794181381 24043993483878483711409009)
                ·
                  refine ⟨18032995112908862783556757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24043993483878483711409009 18032995112908862783556757)
                  ·
                    refine ⟨845296645917602942979223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18032995112908862783556757 845296645917602942979223)
                    ·
                      rfl

theorem cell23_4938628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_4938628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938628 prefixEnd_4938628 := by exact prefixLift 4938628
  have htrace : WordTrace (prefixWord ++ tailWord_4938628) baseStart_4938628 baseEnd_4938628 := by
    simpa [prefixWord, tailWord_4938628, baseEnd_4938628] using wordTrace_append hprefix tailTrace_4938628
  have hstable : (prefixWord ++ tailWord_4938628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938628).length < 2 ^ (prefixWord ++ tailWord_4938628).sum := by decide
  have hdescent : baseEnd_4938628 < baseStart_4938628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938646 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4938646 : Nat := 118140960795 + 4938646 * 2 ^ 59
def prefixEnd_4938646 : Nat := 4983230072969 + 3 ^ 40 * 4938646 * 2
def baseEnd_4938646 : Nat := 2535899180404589758512587

theorem tailTrace_4938646 : CollatzResearch.WordTrace tailWord_4938646 prefixEnd_4938646 2535899180404589758512587 := by
  unfold tailWord_4938646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257951104133529401946237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120084811777424313620759861 11257951104133529401946237)
  ·
    refine ⟨4221731664050073525729839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11257951104133529401946237 4221731664050073525729839)
    ·
      refine ⟨6332597496075110288594759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4221731664050073525729839 6332597496075110288594759)
      ·
        refine ⟨9498896244112665432892139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6332597496075110288594759 9498896244112665432892139)
        ·
          refine ⟨14248344366168998149338209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9498896244112665432892139 14248344366168998149338209)
          ·
            refine ⟨10686258274626748612003657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14248344366168998149338209 10686258274626748612003657)
            ·
              refine ⟨8014693705970061459002743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10686258274626748612003657 8014693705970061459002743)
              ·
                refine ⟨12022040558955092188504115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8014693705970061459002743 12022040558955092188504115)
                ·
                  refine ⟨18033060838432638282756173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12022040558955092188504115 18033060838432638282756173)
                  ·
                    refine ⟨6762397814412239356033565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18033060838432638282756173 6762397814412239356033565)
                    ·
                      refine ⟨2535899180404589758512587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6762397814412239356033565 2535899180404589758512587)
                      ·
                        rfl

theorem cell23_4938646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4938646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938646 prefixEnd_4938646 := by exact prefixLift 4938646
  have htrace : WordTrace (prefixWord ++ tailWord_4938646) baseStart_4938646 baseEnd_4938646 := by
    simpa [prefixWord, tailWord_4938646, baseEnd_4938646] using wordTrace_append hprefix tailTrace_4938646
  have hstable : (prefixWord ++ tailWord_4938646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938646).length < 2 ^ (prefixWord ++ tailWord_4938646).sum := by decide
  have hdescent : baseEnd_4938646 < baseStart_4938646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938673 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 1, 3, 2]
def baseStart_4938673 : Nat := 118140960795 + 4938673 * 2 ^ 59
def prefixEnd_4938673 : Nat := 4983230072969 + 3 ^ 40 * 4938673 * 2
def baseEnd_4938673 : Nat := 2535913044382261152874963

theorem tailTrace_4938673 : CollatzResearch.WordTrace tailWord_4938673 prefixEnd_4938673 2535913044382261152874963 := by
  unfold tailWord_4938673
  simp only [CollatzResearch.WordTrace]
  refine ⟨180128202437038654042372673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120085468291359102694915115 180128202437038654042372673)
  ·
    refine ⟨135096151827778990531779505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180128202437038654042372673 135096151827778990531779505)
    ·
      refine ⟨101322113870834242898834629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135096151827778990531779505 101322113870834242898834629)
      ·
        refine ⟨18997896350781420543531493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101322113870834242898834629 18997896350781420543531493)
        ·
          refine ⟨3562105565771516351912155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18997896350781420543531493 3562105565771516351912155)
          ·
            refine ⟨5343158348657274527868233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562105565771516351912155 5343158348657274527868233)
            ·
              refine ⟨4007368761492955895901175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5343158348657274527868233 4007368761492955895901175)
              ·
                refine ⟨6011053142239433843851763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4007368761492955895901175 6011053142239433843851763)
                ·
                  refine ⟨9016579713359150765777645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6011053142239433843851763 9016579713359150765777645)
                  ·
                    refine ⟨3381217392509681537166617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9016579713359150765777645 3381217392509681537166617)
                    ·
                      refine ⟨2535913044382261152874963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381217392509681537166617 2535913044382261152874963)
                      ·
                        rfl

theorem cell23_4938673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_4938673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938673 prefixEnd_4938673 := by exact prefixLift 4938673
  have htrace : WordTrace (prefixWord ++ tailWord_4938673) baseStart_4938673 baseEnd_4938673 := by
    simpa [prefixWord, tailWord_4938673, baseEnd_4938673] using wordTrace_append hprefix tailTrace_4938673
  have hstable : (prefixWord ++ tailWord_4938673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938673).length < 2 ^ (prefixWord ++ tailWord_4938673).sum := by decide
  have hdescent : baseEnd_4938673 < baseStart_4938673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938695 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_4938695 : Nat := 118140960795 + 4938695 * 2 ^ 59
def prefixEnd_4938695 : Nat := 4983230072969 + 3 ^ 40 * 4938695 * 2
def baseEnd_4938695 : Nat := 2535924340956660066799861

theorem tailTrace_4938695 : CollatzResearch.WordTrace tailWord_4938695 prefixEnd_4938695 2535924340956660066799861 := by
  unfold tailWord_4938695
  simp only [CollatzResearch.WordTrace]
  refine ⟨180129004842958951799673539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120086003228639301199782359 180129004842958951799673539)
  ·
    refine ⟨270193507264438427699510309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180129004842958951799673539 270193507264438427699510309)
    ·
      refine ⟨50661282612082205193658183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270193507264438427699510309 50661282612082205193658183)
      ·
        refine ⟨75991923918123307790487275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50661282612082205193658183 75991923918123307790487275)
        ·
          refine ⟨113987885877184961685730913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75991923918123307790487275 113987885877184961685730913)
          ·
            refine ⟨85490914407888721264298185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113987885877184961685730913 85490914407888721264298185)
            ·
              refine ⟨64118185805916540948223639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85490914407888721264298185 64118185805916540948223639)
              ·
                refine ⟨96177278708874811422335459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64118185805916540948223639 96177278708874811422335459)
                ·
                  refine ⟨144265918063312217133503189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96177278708874811422335459 144265918063312217133503189)
                  ·
                    refine ⟨3381232454608880089066481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 144265918063312217133503189 3381232454608880089066481)
                    ·
                      refine ⟨2535924340956660066799861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381232454608880089066481 2535924340956660066799861)
                      ·
                        rfl

theorem cell23_4938695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_4938695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938695 prefixEnd_4938695 := by exact prefixLift 4938695
  have htrace : WordTrace (prefixWord ++ tailWord_4938695) baseStart_4938695 baseEnd_4938695 := by
    simpa [prefixWord, tailWord_4938695, baseEnd_4938695] using wordTrace_append hprefix tailTrace_4938695
  have hstable : (prefixWord ++ tailWord_4938695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938695).length < 2 ^ (prefixWord ++ tailWord_4938695).sum := by decide
  have hdescent : baseEnd_4938695 < baseStart_4938695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938698 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_4938698 : Nat := 118140960795 + 4938698 * 2 ^ 59
def prefixEnd_4938698 : Nat := 4983230072969 + 3 ^ 40 * 4938698 * 2
def baseEnd_4938698 : Nat := 2535925881398623555062347

theorem tailTrace_4938698 : CollatzResearch.WordTrace tailWord_4938698 prefixEnd_4938698 2535925881398623555062347 := by
  unfold tailWord_4938698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45032278565487020828008187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120086076174632055541355165 45032278565487020828008187)
  ·
    refine ⟨67548417848230531242012281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45032278565487020828008187 67548417848230531242012281)
    ·
      refine ⟨50661313386172898431509211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67548417848230531242012281 50661313386172898431509211)
      ·
        refine ⟨75991970079259347647263817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50661313386172898431509211 75991970079259347647263817)
        ·
          refine ⟨56993977559444510735447863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75991970079259347647263817 56993977559444510735447863)
          ·
            refine ⟨85490966339166766103171795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56993977559444510735447863 85490966339166766103171795)
            ·
              refine ⟨128236449508750149154757693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85490966339166766103171795 128236449508750149154757693)
              ·
                refine ⟨48088668565781305933034135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128236449508750149154757693 48088668565781305933034135)
                ·
                  refine ⟨72133002848671958899551203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48088668565781305933034135 72133002848671958899551203)
                  ·
                    refine ⟨108199504273007938349326805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72133002848671958899551203 108199504273007938349326805)
                    ·
                      refine ⟨2535925881398623555062347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108199504273007938349326805 2535925881398623555062347)
                      ·
                        rfl

theorem cell23_4938698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_4938698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938698 prefixEnd_4938698 := by exact prefixLift 4938698
  have htrace : WordTrace (prefixWord ++ tailWord_4938698) baseStart_4938698 baseEnd_4938698 := by
    simpa [prefixWord, tailWord_4938698, baseEnd_4938698] using wordTrace_append hprefix tailTrace_4938698
  have hstable : (prefixWord ++ tailWord_4938698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938698).length < 2 ^ (prefixWord ++ tailWord_4938698).sum := by decide
  have hdescent : baseEnd_4938698 < baseStart_4938698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938722 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4938722 : Nat := 118140960795 + 4938722 * 2 ^ 59
def prefixEnd_4938722 : Nat := 4983230072969 + 3 ^ 40 * 4938722 * 2
def baseEnd_4938722 : Nat := 845312734978110487054079

theorem tailTrace_4938722 : CollatzResearch.WordTrace tailWord_4938722 prefixEnd_4938722 845312734978110487054079 := by
  unfold tailWord_4938722
  simp only [CollatzResearch.WordTrace]
  refine ⟨45032497403465283852726605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120086659742574090273937613 45032497403465283852726605)
  ·
    refine ⟨16887186526299481444772477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45032497403465283852726605 16887186526299481444772477)
    ·
      refine ⟨6332694947362305541789679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16887186526299481444772477 6332694947362305541789679)
      ·
        refine ⟨9499042421043458312684519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6332694947362305541789679 9499042421043458312684519)
        ·
          refine ⟨14248563631565187469026779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9499042421043458312684519 14248563631565187469026779)
          ·
            refine ⟨21372845447347781203540169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14248563631565187469026779 21372845447347781203540169)
            ·
              refine ⟨16029634085510835902655127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21372845447347781203540169 16029634085510835902655127)
              ·
                refine ⟨24044451128266253853982691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16029634085510835902655127 24044451128266253853982691)
                ·
                  refine ⟨36066676692399380780974037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24044451128266253853982691 36066676692399380780974037)
                  ·
                    refine ⟨845312734978110487054079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36066676692399380780974037 845312734978110487054079)
                    ·
                      rfl

theorem cell23_4938722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4938722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938722 prefixEnd_4938722 := by exact prefixLift 4938722
  have htrace : WordTrace (prefixWord ++ tailWord_4938722) baseStart_4938722 baseEnd_4938722 := by
    simpa [prefixWord, tailWord_4938722, baseEnd_4938722] using wordTrace_append hprefix tailTrace_4938722
  have hstable : (prefixWord ++ tailWord_4938722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938722).length < 2 ^ (prefixWord ++ tailWord_4938722).sum := by decide
  have hdescent : baseEnd_4938722 < baseStart_4938722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938742 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_4938742 : Nat := 118140960795 + 4938742 * 2 ^ 59
def prefixEnd_4938742 : Nat := 4983230072969 + 3 ^ 40 * 4938742 * 2
def baseEnd_4938742 : Nat := 2535948474547421382912145

theorem tailTrace_4938742 : CollatzResearch.WordTrace tailWord_4938742 prefixEnd_4938742 2535948474547421382912145 := by
  unfold tailWord_4938742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11258169942111792426664655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120087146049192452551089653 11258169942111792426664655)
  ·
    refine ⟨16887254913167688639996983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11258169942111792426664655 16887254913167688639996983)
    ·
      refine ⟨25330882369751532959995475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16887254913167688639996983 25330882369751532959995475)
      ·
        refine ⟨37996323554627299439993213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25330882369751532959995475 37996323554627299439993213)
        ·
          refine ⟨14248621332985237289997455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37996323554627299439993213 14248621332985237289997455)
          ·
            refine ⟨21372931999477855934996183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14248621332985237289997455 21372931999477855934996183)
            ·
              refine ⟨32059397999216783902494275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21372931999477855934996183 32059397999216783902494275)
              ·
                refine ⟨48089096998825175853741413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32059397999216783902494275 48089096998825175853741413)
                ·
                  refine ⟨9016705687279720472576515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48089096998825175853741413 9016705687279720472576515)
                  ·
                    refine ⟨13525058530919580708864773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9016705687279720472576515 13525058530919580708864773)
                    ·
                      refine ⟨2535948474547421382912145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13525058530919580708864773 2535948474547421382912145)
                      ·
                        rfl

theorem cell23_4938742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_4938742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938742 prefixEnd_4938742 := by exact prefixLift 4938742
  have htrace : WordTrace (prefixWord ++ tailWord_4938742) baseStart_4938742 baseEnd_4938742 := by
    simpa [prefixWord, tailWord_4938742, baseEnd_4938742] using wordTrace_append hprefix tailTrace_4938742
  have hstable : (prefixWord ++ tailWord_4938742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938742).length < 2 ^ (prefixWord ++ tailWord_4938742).sum := by decide
  have hdescent : baseEnd_4938742 < baseStart_4938742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938849 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_4938849 : Nat := 118140960795 + 4938849 * 2 ^ 59
def prefixEnd_4938849 : Nat := 4983230072969 + 3 ^ 40 * 4938849 * 2
def baseEnd_4938849 : Nat := 2536003416977452464274153

theorem tailTrace_4938849 : CollatzResearch.WordTrace tailWord_4938849 prefixEnd_4938849 2536003416977452464274153 := by
  unfold tailWord_4938849
  simp only [CollatzResearch.WordTrace]
  refine ⟨180134621684401036100779601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120089747789600690733853067 180134621684401036100779601)
  ·
    refine ⟨135100966263300777075584701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180134621684401036100779601 135100966263300777075584701)
    ·
      refine ⟨50662862348737791403344263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135100966263300777075584701 50662862348737791403344263)
      ·
        refine ⟨75994293523106687105016395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50662862348737791403344263 75994293523106687105016395)
        ·
          refine ⟨113991440284660030657524593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75994293523106687105016395 113991440284660030657524593)
          ·
            refine ⟨85493580213495022993143445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113991440284660030657524593 85493580213495022993143445)
            ·
              refine ⟨4007511572507579202803599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85493580213495022993143445 4007511572507579202803599)
              ·
                refine ⟨6011267358761368804205399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4007511572507579202803599 6011267358761368804205399)
                ·
                  refine ⟨9016901038142053206308099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6011267358761368804205399 9016901038142053206308099)
                  ·
                    refine ⟨13525351557213079809462149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9016901038142053206308099 13525351557213079809462149)
                    ·
                      refine ⟨2536003416977452464274153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13525351557213079809462149 2536003416977452464274153)
                      ·
                        rfl

theorem cell23_4938849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_4938849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938849 prefixEnd_4938849 := by exact prefixLift 4938849
  have htrace : WordTrace (prefixWord ++ tailWord_4938849) baseStart_4938849 baseEnd_4938849 := by
    simpa [prefixWord, tailWord_4938849, baseEnd_4938849] using wordTrace_append hprefix tailTrace_4938849
  have hstable : (prefixWord ++ tailWord_4938849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938849).length < 2 ^ (prefixWord ++ tailWord_4938849).sum := by decide
  have hdescent : baseEnd_4938849 < baseStart_4938849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938855 : List Nat := [1, 1, 5, 1, 1, 4, 10]
def baseStart_4938855 : Nat := 118140960795 + 4938855 * 2 ^ 59
def prefixEnd_4938855 : Nat := 4983230072969 + 3 ^ 40 * 4938855 * 2
def baseEnd_4938855 : Nat := 31308722195819499269125

theorem tailTrace_4938855 : CollatzResearch.WordTrace tailWord_4938855 prefixEnd_4938855 31308722195819499269125 := by
  unfold tailWord_4938855
  simp only [CollatzResearch.WordTrace]
  refine ⟨180134840522379299125498019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120089893681586199416998679 180134840522379299125498019)
  ·
    refine ⟨270202260783568948688247029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180134840522379299125498019 270202260783568948688247029)
    ·
      refine ⟨25331461948459588939523159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 270202260783568948688247029 25331461948459588939523159)
      ·
        refine ⟨37997192922689383409284739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25331461948459588939523159 37997192922689383409284739)
        ·
          refine ⟨56995789384034075113927109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37997192922689383409284739 56995789384034075113927109)
          ·
            refine ⟨10686710509506389083861333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56995789384034075113927109 10686710509506389083861333)
            ·
              refine ⟨31308722195819499269125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10686710509506389083861333 31308722195819499269125)
              ·
                rfl

theorem cell23_4938855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 10].length) (baseStart_4938855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938855 prefixEnd_4938855 := by exact prefixLift 4938855
  have htrace : WordTrace (prefixWord ++ tailWord_4938855) baseStart_4938855 baseEnd_4938855 := by
    simpa [prefixWord, tailWord_4938855, baseEnd_4938855] using wordTrace_append hprefix tailTrace_4938855
  have hstable : (prefixWord ++ tailWord_4938855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938855).length < 2 ^ (prefixWord ++ tailWord_4938855).sum := by decide
  have hdescent : baseEnd_4938855 < baseStart_4938855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938866 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_4938866 : Nat := 118140960795 + 4938866 * 2 ^ 59
def prefixEnd_4938866 : Nat := 4983230072969 + 3 ^ 40 * 4938866 * 2
def baseEnd_4938866 : Nat := 2536012146148578897761575

theorem tailTrace_4938866 : CollatzResearch.WordTrace tailWord_4938866 prefixEnd_4938866 2536012146148578897761575 := by
  unfold tailWord_4938866
  simp only [CollatzResearch.WordTrace]
  refine ⟨45033810431334862001037113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120090161150226298669432301 45033810431334862001037113)
  ·
    refine ⟨33775357823501146500777835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45033810431334862001037113 33775357823501146500777835)
    ·
      refine ⟨50663036735251719751166753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33775357823501146500777835 50663036735251719751166753)
      ·
        refine ⟨37997277551438789813375065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50663036735251719751166753 37997277551438789813375065)
        ·
          refine ⟨28497958163579092360031299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37997277551438789813375065 28497958163579092360031299)
          ·
            refine ⟨42746937245368638540046949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28497958163579092360031299 42746937245368638540046949)
            ·
              refine ⟨8015050733506619726258803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42746937245368638540046949 8015050733506619726258803)
              ·
                refine ⟨12022576100259929589388205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8015050733506619726258803 12022576100259929589388205)
                ·
                  refine ⟨4508466037597473596020577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12022576100259929589388205 4508466037597473596020577)
                  ·
                    refine ⟨3381349528198105197015433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4508466037597473596020577 3381349528198105197015433)
                    ·
                      refine ⟨2536012146148578897761575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381349528198105197015433 2536012146148578897761575)
                      ·
                        rfl

theorem cell23_4938866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_4938866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938866 prefixEnd_4938866 := by exact prefixLift 4938866
  have htrace : WordTrace (prefixWord ++ tailWord_4938866) baseStart_4938866 baseEnd_4938866 := by
    simpa [prefixWord, tailWord_4938866, baseEnd_4938866] using wordTrace_append hprefix tailTrace_4938866
  have hstable : (prefixWord ++ tailWord_4938866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938866).length < 2 ^ (prefixWord ++ tailWord_4938866).sum := by decide
  have hdescent : baseEnd_4938866 < baseStart_4938866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938892 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 2, 7, 2]
def baseStart_4938892 : Nat := 118140960795 + 4938892 * 2 ^ 59
def prefixEnd_4938892 : Nat := 4983230072969 + 3 ^ 40 * 4938892 * 2
def baseEnd_4938892 : Nat := 2536025496645595796036455

theorem tailTrace_4938892 : CollatzResearch.WordTrace tailWord_4938892 prefixEnd_4938892 2536025496645595796036455 := by
  unfold tailWord_4938892
  simp only [CollatzResearch.WordTrace]
  refine ⟨90068095011622627222297465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120090793348830169629729953 90068095011622627222297465)
  ·
    refine ⟨67551071258716970416723099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90068095011622627222297465 67551071258716970416723099)
    ·
      refine ⟨101326606888075455625084649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67551071258716970416723099 101326606888075455625084649)
      ·
        refine ⟨75994955166056591718813487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101326606888075455625084649 75994955166056591718813487)
        ·
          refine ⟨113992432749084887578220231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75994955166056591718813487 113992432749084887578220231)
          ·
            refine ⟨170988649123627331367330347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113992432749084887578220231 170988649123627331367330347)
            ·
              refine ⟨256482973685440997050995521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170988649123627331367330347 256482973685440997050995521)
              ·
                refine ⟨192362230264080747788246641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256482973685440997050995521 192362230264080747788246641)
                ·
                  refine ⟨144271672698060560841184981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192362230264080747788246641 144271672698060560841184981)
                  ·
                    refine ⟨3381367328860794394715273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 144271672698060560841184981 3381367328860794394715273)
                    ·
                      refine ⟨2536025496645595796036455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381367328860794394715273 2536025496645595796036455)
                      ·
                        rfl

theorem cell23_4938892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_4938892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938892 prefixEnd_4938892 := by exact prefixLift 4938892
  have htrace : WordTrace (prefixWord ++ tailWord_4938892) baseStart_4938892 baseEnd_4938892 := by
    simpa [prefixWord, tailWord_4938892, baseEnd_4938892] using wordTrace_append hprefix tailTrace_4938892
  have hstable : (prefixWord ++ tailWord_4938892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938892).length < 2 ^ (prefixWord ++ tailWord_4938892).sum := by decide
  have hdescent : baseEnd_4938892 < baseStart_4938892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938905 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_4938905 : Nat := 118140960795 + 4938905 * 2 ^ 59
def prefixEnd_4938905 : Nat := 4983230072969 + 3 ^ 40 * 4938905 * 2
def baseEnd_4938905 : Nat := 2536032171894104245173895

theorem tailTrace_4938905 : CollatzResearch.WordTrace tailWord_4938905 prefixEnd_4938905 2536032171894104245173895 := by
  unfold tailWord_4938905
  simp only [CollatzResearch.WordTrace]
  refine ⟨180136664172198157664818169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120091109448132105109878779 180136664172198157664818169)
  ·
    refine ⟨135102498129148618248613627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180136664172198157664818169 135102498129148618248613627)
    ·
      refine ⟨202653747193722927372920441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135102498129148618248613627 202653747193722927372920441)
      ·
        refine ⟨151990310395292195529690331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202653747193722927372920441 151990310395292195529690331)
        ·
          refine ⟨227985465592938293294535497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151990310395292195529690331 227985465592938293294535497)
          ·
            refine ⟨170989099194703719970901623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227985465592938293294535497 170989099194703719970901623)
            ·
              refine ⟨256483648792055579956352435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170989099194703719970901623 256483648792055579956352435)
              ·
                refine ⟨384725473188083369934528653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256483648792055579956352435 384725473188083369934528653)
                ·
                  refine ⟨144272052445531263725448245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 384725473188083369934528653 144272052445531263725448245)
                  ·
                    refine ⟨13525504916768555974260773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 144272052445531263725448245 13525504916768555974260773)
                    ·
                      refine ⟨2536032171894104245173895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13525504916768555974260773 2536032171894104245173895)
                      ·
                        rfl

theorem cell23_4938905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_4938905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938905 prefixEnd_4938905 := by exact prefixLift 4938905
  have htrace : WordTrace (prefixWord ++ tailWord_4938905) baseStart_4938905 baseEnd_4938905 := by
    simpa [prefixWord, tailWord_4938905, baseEnd_4938905] using wordTrace_append hprefix tailTrace_4938905
  have hstable : (prefixWord ++ tailWord_4938905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938905).length < 2 ^ (prefixWord ++ tailWord_4938905).sum := by decide
  have hdescent : baseEnd_4938905 < baseStart_4938905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938915 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 4, 6]
def baseStart_4938915 : Nat := 118140960795 + 4938915 * 2 ^ 59
def prefixEnd_4938915 : Nat := 4983230072969 + 3 ^ 40 * 4938915 * 2
def baseEnd_4938915 : Nat := 845345768900216402016283

theorem tailTrace_4938915 : CollatzResearch.WordTrace tailWord_4938915 prefixEnd_4938915 845345768900216402016283 := by
  unfold tailWord_4938915
  simp only [CollatzResearch.WordTrace]
  refine ⟨180137028902161929372682199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120091352601441286248454799 180137028902161929372682199)
  ·
    refine ⟨270205543353242894059023299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180137028902161929372682199 270205543353242894059023299)
    ·
      refine ⟨405308315029864341088534949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270205543353242894059023299 405308315029864341088534949)
      ·
        refine ⟨75995309068099563954100303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 405308315029864341088534949 75995309068099563954100303)
        ·
          refine ⟨113992963602149345931150455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75995309068099563954100303 113992963602149345931150455)
          ·
            refine ⟨170989445403224018896725683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113992963602149345931150455 170989445403224018896725683)
            ·
              refine ⟨256484168104836028345088525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170989445403224018896725683 256484168104836028345088525)
              ·
                refine ⟨96181563039313510629408197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256484168104836028345088525 96181563039313510629408197)
                ·
                  refine ⟨18034043069871283243014037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96181563039313510629408197 18034043069871283243014037)
                  ·
                    refine ⟨845345768900216402016283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18034043069871283243014037 845345768900216402016283)
                    ·
                      rfl

theorem cell23_4938915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 6].length) (baseStart_4938915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938915 prefixEnd_4938915 := by exact prefixLift 4938915
  have htrace : WordTrace (prefixWord ++ tailWord_4938915) baseStart_4938915 baseEnd_4938915 := by
    simpa [prefixWord, tailWord_4938915, baseEnd_4938915] using wordTrace_append hprefix tailTrace_4938915
  have hstable : (prefixWord ++ tailWord_4938915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938915).length < 2 ^ (prefixWord ++ tailWord_4938915).sum := by decide
  have hdescent : baseEnd_4938915 < baseStart_4938915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938939 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 6, 2, 2]
def baseStart_4938939 : Nat := 118140960795 + 4938939 * 2 ^ 59
def prefixEnd_4938939 : Nat := 4983230072969 + 3 ^ 40 * 4938939 * 2
def baseEnd_4938939 : Nat := 2536049630236357112148739

theorem tailTrace_4938939 : CollatzResearch.WordTrace tailWord_4938939 prefixEnd_4938939 2536049630236357112148739 := by
  unfold tailWord_4938939
  simp only [CollatzResearch.WordTrace]
  refine ⟨180137904254074981471555871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120091936169383320981037247 180137904254074981471555871)
  ·
    refine ⟨270206856381112472207333807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180137904254074981471555871 270206856381112472207333807)
    ·
      refine ⟨405310284571668708311000711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270206856381112472207333807 405310284571668708311000711)
      ·
        refine ⟨607965426857503062466501067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405310284571668708311000711 607965426857503062466501067)
        ·
          refine ⟨911948140286254593699751601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607965426857503062466501067 911948140286254593699751601)
          ·
            refine ⟨683961105214690945274813701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911948140286254593699751601 683961105214690945274813701)
            ·
              refine ⟨128242707227754552239027569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 683961105214690945274813701 128242707227754552239027569)
              ·
                refine ⟨96182030420815914179270677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128242707227754552239027569 96182030420815914179270677)
                ·
                  refine ⟨4508532675975745977153313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96182030420815914179270677 4508532675975745977153313)
                  ·
                    refine ⟨3381399506981809482864985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4508532675975745977153313 3381399506981809482864985)
                    ·
                      refine ⟨2536049630236357112148739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381399506981809482864985 2536049630236357112148739)
                      ·
                        rfl

theorem cell23_4938939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 2, 2].length) (baseStart_4938939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938939 prefixEnd_4938939 := by exact prefixLift 4938939
  have htrace : WordTrace (prefixWord ++ tailWord_4938939) baseStart_4938939 baseEnd_4938939 := by
    simpa [prefixWord, tailWord_4938939, baseEnd_4938939] using wordTrace_append hprefix tailTrace_4938939
  have hstable : (prefixWord ++ tailWord_4938939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938939).length < 2 ^ (prefixWord ++ tailWord_4938939).sum := by decide
  have hdescent : baseEnd_4938939 < baseStart_4938939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938950 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4938950 : Nat := 118140960795 + 4938950 * 2 ^ 59
def prefixEnd_4938950 : Nat := 4983230072969 + 3 ^ 40 * 4938950 * 2
def baseEnd_4938950 : Nat := 2536055278523556569111189

theorem tailTrace_4938950 : CollatzResearch.WordTrace tailWord_4938950 prefixEnd_4938950 2536055278523556569111189 := by
  unfold tailWord_4938950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5629322045532347823443947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120092203638023420233470869 5629322045532347823443947)
  ·
    refine ⟨8443983068298521735165921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5629322045532347823443947 8443983068298521735165921)
    ·
      refine ⟨6332987301223891301374441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8443983068298521735165921 6332987301223891301374441)
      ·
        refine ⟨4749740475917918476030831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6332987301223891301374441 4749740475917918476030831)
        ·
          refine ⟨7124610713876877714046247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4749740475917918476030831 7124610713876877714046247)
          ·
            refine ⟨10686916070815316571069371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7124610713876877714046247 10686916070815316571069371)
            ·
              refine ⟨16030374106222974856604057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10686916070815316571069371 16030374106222974856604057)
              ·
                refine ⟨12022780579667231142453043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16030374106222974856604057 12022780579667231142453043)
                ·
                  refine ⟨18034170869500846713679565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12022780579667231142453043 18034170869500846713679565)
                  ·
                    refine ⟨6762814076062817517629837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18034170869500846713679565 6762814076062817517629837)
                    ·
                      refine ⟨2536055278523556569111189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6762814076062817517629837 2536055278523556569111189)
                      ·
                        rfl

theorem cell23_4938950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4938950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938950 prefixEnd_4938950 := by exact prefixLift 4938950
  have htrace : WordTrace (prefixWord ++ tailWord_4938950) baseStart_4938950 baseEnd_4938950 := by
    simpa [prefixWord, tailWord_4938950, baseEnd_4938950] using wordTrace_append hprefix tailTrace_4938950
  have hstable : (prefixWord ++ tailWord_4938950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938950).length < 2 ^ (prefixWord ++ tailWord_4938950).sum := by decide
  have hdescent : baseEnd_4938950 < baseStart_4938950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938955 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 7]
def baseStart_4938955 : Nat := 118140960795 + 4938955 * 2 ^ 59
def prefixEnd_4938955 : Nat := 4983230072969 + 3 ^ 40 * 4938955 * 2
def baseEnd_4938955 : Nat := 2536057845926829049548665

theorem tailTrace_4938955 : CollatzResearch.WordTrace tailWord_4938955 prefixEnd_4938955 2536057845926829049548665 := by
  unfold tailWord_4938955
  simp only [CollatzResearch.WordTrace]
  refine ⟨180138487822017016204138319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120092325214678010802758879 180138487822017016204138319)
  ·
    refine ⟨270207731733025524306207479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180138487822017016204138319 270207731733025524306207479)
    ·
      refine ⟨405311597599538286459311219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270207731733025524306207479 405311597599538286459311219)
      ·
        refine ⟨607967396399307429688966829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405311597599538286459311219 607967396399307429688966829)
        ·
          refine ⟨227987773649740286133362561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 607967396399307429688966829 227987773649740286133362561)
          ·
            refine ⟨170990830237305214600021921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227987773649740286133362561 170990830237305214600021921)
            ·
              refine ⟨128243122677978910950016441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170990830237305214600021921 128243122677978910950016441)
              ·
                refine ⟨96182342008484183212512331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128243122677978910950016441 96182342008484183212512331)
                ·
                  refine ⟨144273513012726274818768497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96182342008484183212512331 144273513012726274818768497)
                  ·
                    refine ⟨108205134759544706114076373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144273513012726274818768497 108205134759544706114076373)
                    ·
                      refine ⟨2536057845926829049548665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108205134759544706114076373 2536057845926829049548665)
                      ·
                        rfl

theorem cell23_4938955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_4938955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938955 prefixEnd_4938955 := by exact prefixLift 4938955
  have htrace : WordTrace (prefixWord ++ tailWord_4938955) baseStart_4938955 baseEnd_4938955 := by
    simpa [prefixWord, tailWord_4938955, baseEnd_4938955] using wordTrace_append hprefix tailTrace_4938955
  have hstable : (prefixWord ++ tailWord_4938955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938955).length < 2 ^ (prefixWord ++ tailWord_4938955).sum := by decide
  have hdescent : baseEnd_4938955 < baseStart_4938955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4938989 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_4938989 : Nat := 118140960795 + 4938989 * 2 ^ 59
def prefixEnd_4938989 : Nat := 4983230072969 + 3 ^ 40 * 4938989 * 2
def baseEnd_4938989 : Nat := 2536075304269081916523509

theorem tailTrace_4938989 : CollatzResearch.WordTrace tailWord_4938989 prefixEnd_4938989 2536075304269081916523509 := by
  unfold tailWord_4938989
  simp only [CollatzResearch.WordTrace]
  refine ⟨180139727903893840010876021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120093151935929226673917347 180139727903893840010876021)
  ·
    refine ⟨16888099490990047501019627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180139727903893840010876021 16888099490990047501019627)
    ·
      refine ⟨25332149236485071251529441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16888099490990047501019627 25332149236485071251529441)
      ·
        refine ⟨18999111927363803438647081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25332149236485071251529441 18999111927363803438647081)
        ·
          refine ⟨14249333945522852578985311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18999111927363803438647081 14249333945522852578985311)
          ·
            refine ⟨21374000918284278868477967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14249333945522852578985311 21374000918284278868477967)
            ·
              refine ⟨32061001377426418302716951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21374000918284278868477967 32061001377426418302716951)
              ·
                refine ⟨48091502066139627454075427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32061001377426418302716951 48091502066139627454075427)
                ·
                  refine ⟨72137253099209441181113141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48091502066139627454075427 72137253099209441181113141)
                  ·
                    refine ⟨6762867478050885110729357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72137253099209441181113141 6762867478050885110729357)
                    ·
                      refine ⟨2536075304269081916523509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6762867478050885110729357 2536075304269081916523509)
                      ·
                        rfl

theorem cell23_4938989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_4938989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4938989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4938989 prefixEnd_4938989 := by exact prefixLift 4938989
  have htrace : WordTrace (prefixWord ++ tailWord_4938989) baseStart_4938989 baseEnd_4938989 := by
    simpa [prefixWord, tailWord_4938989, baseEnd_4938989] using wordTrace_append hprefix tailTrace_4938989
  have hstable : (prefixWord ++ tailWord_4938989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4938989).length < 2 ^ (prefixWord ++ tailWord_4938989).sum := by decide
  have hdescent : baseEnd_4938989 < baseStart_4938989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4938989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939009 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 2, 5]
def baseStart_4939009 : Nat := 118140960795 + 4939009 * 2 ^ 59
def prefixEnd_4939009 : Nat := 4983230072969 + 3 ^ 40 * 4939009 * 2
def baseEnd_4939009 : Nat := 845361857960723946091139

theorem tailTrace_4939009 : CollatzResearch.WordTrace tailWord_4939009 prefixEnd_4939009 845361857960723946091139 := by
  unfold tailWord_4939009
  simp only [CollatzResearch.WordTrace]
  refine ⟨180140457363821383426604081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120093638242547588951069387 180140457363821383426604081)
  ·
    refine ⟨135105343022866037569953061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180140457363821383426604081 135105343022866037569953061)
    ·
      refine ⟨25332251816787382044366199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135105343022866037569953061 25332251816787382044366199)
      ·
        refine ⟨37998377725181073066549299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25332251816787382044366199 37998377725181073066549299)
        ·
          refine ⟨56997566587771609599823949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37998377725181073066549299 56997566587771609599823949)
          ·
            refine ⟨21374087470414353599933981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56997566587771609599823949 21374087470414353599933981)
            ·
              refine ⟨8015282801405382599975243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21374087470414353599933981 8015282801405382599975243)
              ·
                refine ⟨12022924202108073899962865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8015282801405382599975243 12022924202108073899962865)
                ·
                  refine ⟨9017193151581055424972149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12022924202108073899962865 9017193151581055424972149)
                  ·
                    refine ⟨845361857960723946091139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9017193151581055424972149 845361857960723946091139)
                    ·
                      rfl

theorem cell23_4939009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_4939009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939009 prefixEnd_4939009 := by exact prefixLift 4939009
  have htrace : WordTrace (prefixWord ++ tailWord_4939009) baseStart_4939009 baseEnd_4939009 := by
    simpa [prefixWord, tailWord_4939009, baseEnd_4939009] using wordTrace_append hprefix tailTrace_4939009
  have hstable : (prefixWord ++ tailWord_4939009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939009).length < 2 ^ (prefixWord ++ tailWord_4939009).sum := by decide
  have hdescent : baseEnd_4939009 < baseStart_4939009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939116 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_4939116 : Nat := 118140960795 + 4939116 * 2 ^ 59
def prefixEnd_4939116 : Nat := 4983230072969 + 3 ^ 40 * 4939116 * 2
def baseEnd_4939116 : Nat := 845380172104067639878475

theorem tailTrace_4939116 : CollatzResearch.WordTrace tailWord_4939116 prefixEnd_4939116 845380172104067639878475 := by
  unfold tailWord_4939116
  simp only [CollatzResearch.WordTrace]
  refine ⟨90072179987216870350374601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120096239982955827133832801 90072179987216870350374601)
  ·
    refine ⟨67554134990412652762780951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90072179987216870350374601 67554134990412652762780951)
    ·
      refine ⟨101331202485618979144171427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67554134990412652762780951 101331202485618979144171427)
      ·
        refine ⟨151996803728428468716257141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101331202485618979144171427 151996803728428468716257141)
        ·
          refine ⟨14249700349540168942149107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151996803728428468716257141 14249700349540168942149107)
          ·
            refine ⟨21374550524310253413223661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14249700349540168942149107 21374550524310253413223661)
            ·
              refine ⟨8015456446616345029958873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21374550524310253413223661 8015456446616345029958873)
              ·
                refine ⟨6011592334962258772469155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8015456446616345029958873 6011592334962258772469155)
                ·
                  refine ⟨9017388502443388158703733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6011592334962258772469155 9017388502443388158703733)
                  ·
                    refine ⟨845380172104067639878475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9017388502443388158703733 845380172104067639878475)
                    ·
                      rfl

theorem cell23_4939116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_4939116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939116 prefixEnd_4939116 := by exact prefixLift 4939116
  have htrace : WordTrace (prefixWord ++ tailWord_4939116) baseStart_4939116 baseEnd_4939116 := by
    simpa [prefixWord, tailWord_4939116, baseEnd_4939116] using wordTrace_append hprefix tailTrace_4939116
  have hstable : (prefixWord ++ tailWord_4939116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939116).length < 2 ^ (prefixWord ++ tailWord_4939116).sum := by decide
  have hdescent : baseEnd_4939116 < baseStart_4939116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939119 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_4939119 : Nat := 118140960795 + 4939119 * 2 ^ 59
def prefixEnd_4939119 : Nat := 4983230072969 + 3 ^ 40 * 4939119 * 2
def baseEnd_4939119 : Nat := 2536142056754166407897911

theorem tailTrace_4939119 : CollatzResearch.WordTrace tailWord_4939119 prefixEnd_4939119 2536142056754166407897911 := by
  unfold tailWord_4939119
  simp only [CollatzResearch.WordTrace]
  refine ⟨180144469393422872213108411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120096312928948581475405607 180144469393422872213108411)
  ·
    refine ⟨270216704090134308319662617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180144469393422872213108411 270216704090134308319662617)
    ·
      refine ⟨202662528067600731239746963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270216704090134308319662617 202662528067600731239746963)
      ·
        refine ⟨303993792101401096859620445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202662528067600731239746963 303993792101401096859620445)
        ·
          refine ⟨113997672038025411322357667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303993792101401096859620445 113997672038025411322357667)
          ·
            refine ⟨170996508057038116983536501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113997672038025411322357667 170996508057038116983536501)
            ·
              refine ⟨16030922630347323467206547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170996508057038116983536501 16030922630347323467206547)
              ·
                refine ⟨24046383945520985200809821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16030922630347323467206547 24046383945520985200809821)
                ·
                  refine ⟨9017393979570369450303683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24046383945520985200809821 9017393979570369450303683)
                  ·
                    refine ⟨13526090969355554175455525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9017393979570369450303683 13526090969355554175455525)
                    ·
                      refine ⟨2536142056754166407897911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13526090969355554175455525 2536142056754166407897911)
                      ·
                        rfl

theorem cell23_4939119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_4939119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939119 prefixEnd_4939119 := by exact prefixLift 4939119
  have htrace : WordTrace (prefixWord ++ tailWord_4939119) baseStart_4939119 baseEnd_4939119 := by
    simpa [prefixWord, tailWord_4939119, baseEnd_4939119] using wordTrace_append hprefix tailTrace_4939119
  have hstable : (prefixWord ++ tailWord_4939119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939119).length < 2 ^ (prefixWord ++ tailWord_4939119).sum := by decide
  have hdescent : baseEnd_4939119 < baseStart_4939119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939129 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 6, 4]
def baseStart_4939129 : Nat := 118140960795 + 4939129 * 2 ^ 59
def prefixEnd_4939129 : Nat := 4983230072969 + 3 ^ 40 * 4939129 * 2
def baseEnd_4939129 : Nat := 845382397186903789590955

theorem tailTrace_4939129 : CollatzResearch.WordTrace tailWord_4939129 prefixEnd_4939129 845382397186903789590955 := by
  unfold tailWord_4939129
  simp only [CollatzResearch.WordTrace]
  refine ⟨180144834123386643920972441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120096556082257762613981627 180144834123386643920972441)
  ·
    refine ⟨135108625592539982940729331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180144834123386643920972441 135108625592539982940729331)
    ·
      refine ⟨202662938388809974411093997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135108625592539982940729331 202662938388809974411093997)
      ·
        refine ⟨75998601895803740404160249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202662938388809974411093997 75998601895803740404160249)
        ·
          refine ⟨56998951421852805303120187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75998601895803740404160249 56998951421852805303120187)
          ·
            refine ⟨85498427132779207954680281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56998951421852805303120187 85498427132779207954680281)
            ·
              refine ⟨64123820349584405966010211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85498427132779207954680281 64123820349584405966010211)
              ·
                refine ⟨96185730524376608949015317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64123820349584405966010211 96185730524376608949015317)
                ·
                  refine ⟨4508706118330153544485093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96185730524376608949015317 4508706118330153544485093)
                  ·
                    refine ⟨845382397186903789590955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4508706118330153544485093 845382397186903789590955)
                    ·
                      rfl

theorem cell23_4939129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 4].length) (baseStart_4939129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939129 prefixEnd_4939129 := by exact prefixLift 4939129
  have htrace : WordTrace (prefixWord ++ tailWord_4939129) baseStart_4939129 baseEnd_4939129 := by
    simpa [prefixWord, tailWord_4939129, baseEnd_4939129] using wordTrace_append hprefix tailTrace_4939129
  have hstable : (prefixWord ++ tailWord_4939129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939129).length < 2 ^ (prefixWord ++ tailWord_4939129).sum := by decide
  have hdescent : baseEnd_4939129 < baseStart_4939129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939170 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_4939170 : Nat := 118140960795 + 4939170 * 2 ^ 59
def prefixEnd_4939170 : Nat := 4983230072969 + 3 ^ 40 * 4939170 * 2
def baseEnd_4939170 : Nat := 2536168244267545708360177

theorem tailTrace_4939170 : CollatzResearch.WordTrace tailWord_4939170 prefixEnd_4939170 2536168244267545708360177 := by
  unfold tailWord_4939170
  simp only [CollatzResearch.WordTrace]
  refine ⟨45036582379059526980803741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120097553010825405282143309 45036582379059526980803741)
  ·
    refine ⟨16888718392147322617801403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45036582379059526980803741 16888718392147322617801403)
    ·
      refine ⟨25333077588220983926702105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16888718392147322617801403 25333077588220983926702105)
      ·
        refine ⟨18999808191165737945026579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25333077588220983926702105 18999808191165737945026579)
        ·
          refine ⟨28499712286748606917539869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18999808191165737945026579 28499712286748606917539869)
          ·
            refine ⟨10687392107530727594077451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28499712286748606917539869 10687392107530727594077451)
            ·
              refine ⟨16031088161296091391116177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10687392107530727594077451 16031088161296091391116177)
              ·
                refine ⟨12023316120972068543337133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16031088161296091391116177 12023316120972068543337133)
                ·
                  refine ⟨4508743545364525703751425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12023316120972068543337133 4508743545364525703751425)
                  ·
                    refine ⟨3381557659023394277813569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4508743545364525703751425 3381557659023394277813569)
                    ·
                      refine ⟨2536168244267545708360177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381557659023394277813569 2536168244267545708360177)
                      ·
                        rfl

theorem cell23_4939170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_4939170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939170 prefixEnd_4939170 := by exact prefixLift 4939170
  have htrace : WordTrace (prefixWord ++ tailWord_4939170) baseStart_4939170 baseEnd_4939170 := by
    simpa [prefixWord, tailWord_4939170, baseEnd_4939170] using wordTrace_append hprefix tailTrace_4939170
  have hstable : (prefixWord ++ tailWord_4939170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939170).length < 2 ^ (prefixWord ++ tailWord_4939170).sum := by decide
  have hdescent : baseEnd_4939170 < baseStart_4939170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939203 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 3]
def baseStart_4939203 : Nat := 118140960795 + 4939203 * 2 ^ 59
def prefixEnd_4939203 : Nat := 4983230072969 + 3 ^ 40 * 4939203 * 2
def baseEnd_4939203 : Nat := 2536185189129144079247525

theorem tailTrace_4939203 : CollatzResearch.WordTrace tailWord_4939203 prefixEnd_4939203 2536185189129144079247525 := by
  unfold tailWord_4939203
  simp only [CollatzResearch.WordTrace]
  refine ⟨180147533125118554559166263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120098355416745703039444175 180147533125118554559166263)
  ·
    refine ⟨270221299687677831838749395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180147533125118554559166263 270221299687677831838749395)
    ·
      refine ⟨405331949531516747758124093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270221299687677831838749395 405331949531516747758124093)
      ·
        refine ⟨151999481074318780409296535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 405331949531516747758124093 151999481074318780409296535)
        ·
          refine ⟨227999221611478170613944803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151999481074318780409296535 227999221611478170613944803)
          ·
            refine ⟨341998832417217255920917205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227999221611478170613944803 341998832417217255920917205)
            ·
              refine ⟨8015597634778529435646497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 341998832417217255920917205 8015597634778529435646497)
              ·
                refine ⟨6011698226083897076734873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8015597634778529435646497 6011698226083897076734873)
                ·
                  refine ⟨4508773669562922807551155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6011698226083897076734873 4508773669562922807551155)
                  ·
                    refine ⟨6763160504344384211326733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4508773669562922807551155 6763160504344384211326733)
                    ·
                      refine ⟨2536185189129144079247525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6763160504344384211326733 2536185189129144079247525)
                      ·
                        rfl

theorem cell23_4939203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_4939203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939203 prefixEnd_4939203 := by exact prefixLift 4939203
  have htrace : WordTrace (prefixWord ++ tailWord_4939203) baseStart_4939203 baseEnd_4939203 := by
    simpa [prefixWord, tailWord_4939203, baseEnd_4939203] using wordTrace_append hprefix tailTrace_4939203
  have hstable : (prefixWord ++ tailWord_4939203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939203).length < 2 ^ (prefixWord ++ tailWord_4939203).sum := by decide
  have hdescent : baseEnd_4939203 < baseStart_4939203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939220 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_4939220 : Nat := 118140960795 + 4939220 * 2 ^ 59
def prefixEnd_4939220 : Nat := 4983230072969 + 3 ^ 40 * 4939220 * 2
def baseEnd_4939220 : Nat := 2536193918300270512734947

theorem tailTrace_4939220 : CollatzResearch.WordTrace tailWord_4939220 prefixEnd_4939220 2536193918300270512734947 := by
  unfold tailWord_4939220
  simp only [CollatzResearch.WordTrace]
  refine ⟨90074076583028483231267557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120098768777371310975023409 90074076583028483231267557)
  ·
    refine ⟨16888889359317840605862667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90074076583028483231267557 16888889359317840605862667)
    ·
      refine ⟨25333334038976760908794001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16888889359317840605862667 25333334038976760908794001)
      ·
        refine ⟨19000000529232570681595501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25333334038976760908794001 19000000529232570681595501)
        ·
          refine ⟨7125000198462214005598313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19000000529232570681595501 7125000198462214005598313)
          ·
            refine ⟨5343750148846660504198735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7125000198462214005598313 5343750148846660504198735)
            ·
              refine ⟨8015625223269990756298103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5343750148846660504198735 8015625223269990756298103)
              ·
                refine ⟨12023437834904986134447155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8015625223269990756298103 12023437834904986134447155)
                ·
                  refine ⟨18035156752357479201670733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12023437834904986134447155 18035156752357479201670733)
                  ·
                    refine ⟨6763183782134054700626525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18035156752357479201670733 6763183782134054700626525)
                    ·
                      refine ⟨2536193918300270512734947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6763183782134054700626525 2536193918300270512734947)
                      ·
                        rfl

theorem cell23_4939220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_4939220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939220 prefixEnd_4939220 := by exact prefixLift 4939220
  have htrace : WordTrace (prefixWord ++ tailWord_4939220) baseStart_4939220 baseEnd_4939220 := by
    simpa [prefixWord, tailWord_4939220, baseEnd_4939220] using wordTrace_append hprefix tailTrace_4939220
  have hstable : (prefixWord ++ tailWord_4939220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939220).length < 2 ^ (prefixWord ++ tailWord_4939220).sum := by decide
  have hdescent : baseEnd_4939220 < baseStart_4939220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939246 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_4939246 : Nat := 118140960795 + 4939246 * 2 ^ 59
def prefixEnd_4939246 : Nat := 4983230072969 + 3 ^ 40 * 4939246 * 2
def baseEnd_4939246 : Nat := 2536207268797287411009827

theorem tailTrace_4939246 : CollatzResearch.WordTrace tailWord_4939246 prefixEnd_4939246 2536207268797287411009827 := by
  unfold tailWord_4939246
  simp only [CollatzResearch.WordTrace]
  refine ⟨22518637682995346612872699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120099400975975181935321061 22518637682995346612872699)
  ·
    refine ⟨33777956524493019919309049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22518637682995346612872699 33777956524493019919309049)
    ·
      refine ⟨25333467393369764939481787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33777956524493019919309049 25333467393369764939481787)
      ·
        refine ⟨38000201090054647409222681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25333467393369764939481787 38000201090054647409222681)
        ·
          refine ⟨28500150817540985556917011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38000201090054647409222681 28500150817540985556917011)
          ·
            refine ⟨42750226226311478335375517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28500150817540985556917011 42750226226311478335375517)
            ·
              refine ⟨16031334834866804375765819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42750226226311478335375517 16031334834866804375765819)
              ·
                refine ⟨24047002252300206563648729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16031334834866804375765819 24047002252300206563648729)
                ·
                  refine ⟨18035251689225154922736547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24047002252300206563648729 18035251689225154922736547)
                  ·
                    refine ⟨27052877533837732384104821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18035251689225154922736547 27052877533837732384104821)
                    ·
                      refine ⟨2536207268797287411009827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27052877533837732384104821 2536207268797287411009827)
                      ·
                        rfl

theorem cell23_4939246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_4939246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939246 prefixEnd_4939246 := by exact prefixLift 4939246
  have htrace : WordTrace (prefixWord ++ tailWord_4939246) baseStart_4939246 baseEnd_4939246 := by
    simpa [prefixWord, tailWord_4939246, baseEnd_4939246] using wordTrace_append hprefix tailTrace_4939246
  have hstable : (prefixWord ++ tailWord_4939246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939246).length < 2 ^ (prefixWord ++ tailWord_4939246).sum := by decide
  have hdescent : baseEnd_4939246 < baseStart_4939246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939289 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_4939289 : Nat := 118140960795 + 4939289 * 2 ^ 59
def prefixEnd_4939289 : Nat := 4983230072969 + 3 ^ 40 * 4939289 * 2
def baseEnd_4939289 : Nat := 2536229348465430742772129

theorem tailTrace_4939289 : CollatzResearch.WordTrace tailWord_4939289 prefixEnd_4939289 2536229348465430742772129 := by
  unfold tailWord_4939289
  simp only [CollatzResearch.WordTrace]
  refine ⟨180150669802806991246796921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120100446535204660831197947 180150669802806991246796921)
  ·
    refine ⟨135113002352105243435097691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180150669802806991246796921 135113002352105243435097691)
    ·
      refine ⟨202669503528157865152646537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135113002352105243435097691 202669503528157865152646537)
      ·
        refine ⟨152002127646118398864484903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202669503528157865152646537 152002127646118398864484903)
        ·
          refine ⟨228003191469177598296727355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152002127646118398864484903 228003191469177598296727355)
          ·
            refine ⟨342004787203766397445091033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228003191469177598296727355 342004787203766397445091033)
            ·
              refine ⟨256503590402824798083818275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342004787203766397445091033 256503590402824798083818275)
              ·
                refine ⟨384755385604237197125727413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256503590402824798083818275 384755385604237197125727413)
                ·
                  refine ⟨36070817400397237230536945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 384755385604237197125727413 36070817400397237230536945)
                  ·
                    refine ⟨27053113050297927922902709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36070817400397237230536945 27053113050297927922902709)
                    ·
                      refine ⟨2536229348465430742772129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27053113050297927922902709 2536229348465430742772129)
                      ·
                        rfl

theorem cell23_4939289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_4939289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939289 prefixEnd_4939289 := by exact prefixLift 4939289
  have htrace : WordTrace (prefixWord ++ tailWord_4939289) baseStart_4939289 baseEnd_4939289 := by
    simpa [prefixWord, tailWord_4939289, baseEnd_4939289] using wordTrace_append hprefix tailTrace_4939289
  have hstable : (prefixWord ++ tailWord_4939289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939289).length < 2 ^ (prefixWord ++ tailWord_4939289).sum := by decide
  have hdescent : baseEnd_4939289 < baseStart_4939289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939306 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4939306 : Nat := 118140960795 + 4939306 * 2 ^ 59
def prefixEnd_4939306 : Nat := 4983230072969 + 3 ^ 40 * 4939306 * 2
def baseEnd_4939306 : Nat := 2536238077636557176259551

theorem tailTrace_4939306 : CollatzResearch.WordTrace tailWord_4939306 prefixEnd_4939306 2536238077636557176259551 := by
  unfold tailWord_4939306
  simp only [CollatzResearch.WordTrace]
  refine ⟨45037822460936350787541443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120100859895830268766777181 45037822460936350787541443)
  ·
    refine ⟨67556733691404526181312165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45037822460936350787541443 67556733691404526181312165)
    ·
      refine ⟨12666887567138348658996031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67556733691404526181312165 12666887567138348658996031)
      ·
        refine ⟨19000331350707522988494047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12666887567138348658996031 19000331350707522988494047)
        ·
          refine ⟨28500497026061284482741071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19000331350707522988494047 28500497026061284482741071)
          ·
            refine ⟨42750745539091926724111607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28500497026061284482741071 42750745539091926724111607)
            ·
              refine ⟨64126118308637890086167411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42750745539091926724111607 64126118308637890086167411)
              ·
                refine ⟨96189177462956835129251117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64126118308637890086167411 96189177462956835129251117)
                ·
                  refine ⟨36070941548608813173469169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96189177462956835129251117 36070941548608813173469169)
                  ·
                    refine ⟨27053206161456609880101877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36070941548608813173469169 27053206161456609880101877)
                    ·
                      refine ⟨2536238077636557176259551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27053206161456609880101877 2536238077636557176259551)
                      ·
                        rfl

theorem cell23_4939306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4939306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939306 prefixEnd_4939306 := by exact prefixLift 4939306
  have htrace : WordTrace (prefixWord ++ tailWord_4939306) baseStart_4939306 baseEnd_4939306 := by
    simpa [prefixWord, tailWord_4939306, baseEnd_4939306] using wordTrace_append hprefix tailTrace_4939306
  have hstable : (prefixWord ++ tailWord_4939306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939306).length < 2 ^ (prefixWord ++ tailWord_4939306).sum := by decide
  have hdescent : baseEnd_4939306 < baseStart_4939306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939333 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 2, 4, 2]
def baseStart_4939333 : Nat := 118140960795 + 4939333 * 2 ^ 59
def prefixEnd_4939333 : Nat := 4983230072969 + 3 ^ 40 * 4939333 * 2
def baseEnd_4939333 : Nat := 2536251941614228570621927

theorem tailTrace_4939333 : CollatzResearch.WordTrace tailWord_4939333 prefixEnd_4939333 2536251941614228570621927 := by
  unfold tailWord_4939333
  simp only [CollatzResearch.WordTrace]
  refine ⟨180152274614647586761398653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120101516409765057840932435 180152274614647586761398653)
  ·
    refine ⟨67557102980492845035524495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180152274614647586761398653 67557102980492845035524495)
    ·
      refine ⟨101335654470739267553286743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67557102980492845035524495 101335654470739267553286743)
      ·
        refine ⟨152003481706108901329930115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101335654470739267553286743 152003481706108901329930115)
        ·
          refine ⟨228005222559163351994895173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152003481706108901329930115 228005222559163351994895173)
          ·
            refine ⟨42750979229843128499042845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228005222559163351994895173 42750979229843128499042845)
            ·
              refine ⟨16031617211191173187141067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42750979229843128499042845 16031617211191173187141067)
              ·
                refine ⟨24047425816786759780711601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16031617211191173187141067 24047425816786759780711601)
                ·
                  refine ⟨18035569362590069835533701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24047425816786759780711601 18035569362590069835533701)
                  ·
                    refine ⟨3381669255485638094162569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18035569362590069835533701 3381669255485638094162569)
                    ·
                      refine ⟨2536251941614228570621927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381669255485638094162569 2536251941614228570621927)
                      ·
                        rfl

theorem cell23_4939333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_4939333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939333 prefixEnd_4939333 := by exact prefixLift 4939333
  have htrace : WordTrace (prefixWord ++ tailWord_4939333) baseStart_4939333 baseEnd_4939333 := by
    simpa [prefixWord, tailWord_4939333, baseEnd_4939333] using wordTrace_append hprefix tailTrace_4939333
  have hstable : (prefixWord ++ tailWord_4939333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939333).length < 2 ^ (prefixWord ++ tailWord_4939333).sum := by decide
  have hdescent : baseEnd_4939333 < baseStart_4939333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939339 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 10]
def baseStart_4939339 : Nat := 118140960795 + 4939339 * 2 ^ 59
def prefixEnd_4939339 : Nat := 4983230072969 + 3 ^ 40 * 4939339 * 2
def baseEnd_4939339 : Nat := 281806113610906171905211

theorem tailTrace_4939339 : CollatzResearch.WordTrace tailWord_4939339 prefixEnd_4939339 281806113610906171905211 := by
  unfold tailWord_4939339
  simp only [CollatzResearch.WordTrace]
  refine ⟨180152493452625849786117071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120101662301750566524078047 180152493452625849786117071)
  ·
    refine ⟨270228740178938774679175607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180152493452625849786117071 270228740178938774679175607)
    ·
      refine ⟨405343110268408162018763411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270228740178938774679175607 405343110268408162018763411)
      ·
        refine ⟨608014665402612243028145117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405343110268408162018763411 608014665402612243028145117)
        ·
          refine ⟨228005499525979591135554419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 608014665402612243028145117 228005499525979591135554419)
          ·
            refine ⟨342008249288969386703331629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228005499525979591135554419 342008249288969386703331629)
            ·
              refine ⟨128253093483363520013749361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342008249288969386703331629 128253093483363520013749361)
              ·
                refine ⟨96189820112522640010312021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128253093483363520013749361 96189820112522640010312021)
                ·
                  refine ⟨281806113610906171905211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 96189820112522640010312021 281806113610906171905211)
                  ·
                    rfl

theorem cell23_4939339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 10].length) (baseStart_4939339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939339 prefixEnd_4939339 := by exact prefixLift 4939339
  have htrace : WordTrace (prefixWord ++ tailWord_4939339) baseStart_4939339 baseEnd_4939339 := by
    simpa [prefixWord, tailWord_4939339, baseEnd_4939339] using wordTrace_append hprefix tailTrace_4939339
  have hstable : (prefixWord ++ tailWord_4939339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939339).length < 2 ^ (prefixWord ++ tailWord_4939339).sum := by decide
  have hdescent : baseEnd_4939339 < baseStart_4939339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939373 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 8]
def baseStart_4939373 : Nat := 118140960795 + 4939373 * 2 ^ 59
def prefixEnd_4939373 : Nat := 4983230072969 + 3 ^ 40 * 4939373 * 2
def baseEnd_4939373 : Nat := 281808053426712046013527

theorem tailTrace_4939373 : CollatzResearch.WordTrace tailWord_4939373 prefixEnd_4939373 281808053426712046013527 := by
  unfold tailWord_4939373
  simp only [CollatzResearch.WordTrace]
  refine ⟨180153733534502673592854773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120102489023001782395236515 180153733534502673592854773)
  ·
    refine ⟨16889412518859625649330135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180153733534502673592854773 16889412518859625649330135)
    ·
      refine ⟨25334118778289438473995203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16889412518859625649330135 25334118778289438473995203)
      ·
        refine ⟨38001178167434157710992805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25334118778289438473995203 38001178167434157710992805)
        ·
          refine ⟨7125220906393904570811151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38001178167434157710992805 7125220906393904570811151)
          ·
            refine ⟨10687831359590856856216727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7125220906393904570811151 10687831359590856856216727)
            ·
              refine ⟨16031747039386285284325091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10687831359590856856216727 16031747039386285284325091)
              ·
                refine ⟨24047620559079427926487637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16031747039386285284325091 24047620559079427926487637)
                ·
                  refine ⟨281808053426712046013527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24047620559079427926487637 281808053426712046013527)
                  ·
                    rfl

theorem cell23_4939373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_4939373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939373 prefixEnd_4939373 := by exact prefixLift 4939373
  have htrace : WordTrace (prefixWord ++ tailWord_4939373) baseStart_4939373 baseEnd_4939373 := by
    simpa [prefixWord, tailWord_4939373, baseEnd_4939373] using wordTrace_append hprefix tailTrace_4939373
  have hstable : (prefixWord ++ tailWord_4939373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939373).length < 2 ^ (prefixWord ++ tailWord_4939373).sum := by decide
  have hdescent : baseEnd_4939373 < baseStart_4939373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939376 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_4939376 : Nat := 118140960795 + 4939376 * 2 ^ 59
def prefixEnd_4939376 : Nat := 4983230072969 + 3 ^ 40 * 4939376 * 2
def baseEnd_4939376 : Nat := 2536274021282371902384229

theorem tailTrace_4939376 : CollatzResearch.WordTrace tailWord_4939376 prefixEnd_4939376 2536274021282371902384229 := by
  unfold tailWord_4939376
  simp only [CollatzResearch.WordTrace]
  refine ⟨90076921476745902552606991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120102561968994536736809321 90076921476745902552606991)
  ·
    refine ⟨135115382215118853828910487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90076921476745902552606991 135115382215118853828910487)
    ·
      refine ⟨202673073322678280743365731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135115382215118853828910487 202673073322678280743365731)
      ·
        refine ⟨304009609984017421115048597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202673073322678280743365731 304009609984017421115048597)
        ·
          refine ⟨14250450468000816614767903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 304009609984017421115048597 14250450468000816614767903)
          ·
            refine ⟨21375675702001224922151855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14250450468000816614767903 21375675702001224922151855)
            ·
              refine ⟨32063513553001837383227783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21375675702001224922151855 32063513553001837383227783)
              ·
                refine ⟨48095270329502756074841675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32063513553001837383227783 48095270329502756074841675)
                ·
                  refine ⟨72142905494254134112262513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48095270329502756074841675 72142905494254134112262513)
                  ·
                    refine ⟨54107179120690600584196885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72142905494254134112262513 54107179120690600584196885)
                    ·
                      refine ⟨2536274021282371902384229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54107179120690600584196885 2536274021282371902384229)
                      ·
                        rfl

theorem cell23_4939376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_4939376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939376 prefixEnd_4939376 := by exact prefixLift 4939376
  have htrace : WordTrace (prefixWord ++ tailWord_4939376) baseStart_4939376 baseEnd_4939376 := by
    simpa [prefixWord, tailWord_4939376, baseEnd_4939376] using wordTrace_append hprefix tailTrace_4939376
  have hstable : (prefixWord ++ tailWord_4939376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939376).length < 2 ^ (prefixWord ++ tailWord_4939376).sum := by decide
  have hdescent : baseEnd_4939376 < baseStart_4939376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939386 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_4939386 : Nat := 118140960795 + 4939386 * 2 ^ 59
def prefixEnd_4939386 : Nat := 4983230072969 + 3 ^ 40 * 4939386 * 2
def baseEnd_4939386 : Nat := 845426385362972287753061

theorem tailTrace_4939386 : CollatzResearch.WordTrace tailWord_4939386 prefixEnd_4939386 845426385362972287753061 := by
  unfold tailWord_4939386
  simp only [CollatzResearch.WordTrace]
  refine ⟨45038551920863894203269503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120102805122303717875385341 45038551920863894203269503)
  ·
    refine ⟨67557827881295841304904255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45038551920863894203269503 67557827881295841304904255)
    ·
      refine ⟨101336741821943761957356383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67557827881295841304904255 101336741821943761957356383)
      ·
        refine ⟨152005112732915642936034575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101336741821943761957356383 152005112732915642936034575)
        ·
          refine ⟨228007669099373464404051863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152005112732915642936034575 228007669099373464404051863)
          ·
            refine ⟨342011503649060196606077795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228007669099373464404051863 342011503649060196606077795)
            ·
              refine ⟨513017255473590294909116693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342011503649060196606077795 513017255473590294909116693)
              ·
                refine ⟨24047683850324545073864845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 513017255473590294909116693 24047683850324545073864845)
                ·
                  refine ⟨9017881443871704402699317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24047683850324545073864845 9017881443871704402699317)
                  ·
                    refine ⟨845426385362972287753061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9017881443871704402699317 845426385362972287753061)
                    ·
                      rfl

theorem cell23_4939386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_4939386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939386 prefixEnd_4939386 := by exact prefixLift 4939386
  have htrace : WordTrace (prefixWord ++ tailWord_4939386) baseStart_4939386 baseEnd_4939386 := by
    simpa [prefixWord, tailWord_4939386, baseEnd_4939386] using wordTrace_append hprefix tailTrace_4939386
  have hstable : (prefixWord ++ tailWord_4939386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939386).length < 2 ^ (prefixWord ++ tailWord_4939386).sum := by decide
  have hdescent : baseEnd_4939386 < baseStart_4939386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939403 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 1, 5]
def baseStart_4939403 : Nat := 118140960795 + 4939403 * 2 ^ 59
def prefixEnd_4939403 : Nat := 4983230072969 + 3 ^ 40 * 4939403 * 2
def baseEnd_4939403 : Nat := 845429295086681098915535

theorem tailTrace_4939403 : CollatzResearch.WordTrace tailWord_4939403 prefixEnd_4939403 845429295086681098915535 := by
  unfold tailWord_4939403
  simp only [CollatzResearch.WordTrace]
  refine ⟨180154827724393988716446863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120103218482929325810964575 180154827724393988716446863)
  ·
    refine ⟨270232241586590983074670295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180154827724393988716446863 270232241586590983074670295)
    ·
      refine ⟨405348362379886474612005443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270232241586590983074670295 405348362379886474612005443)
      ·
        refine ⟨608022543569829711918008165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405348362379886474612005443 608022543569829711918008165)
        ·
          refine ⟨114004226919343070984626531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 608022543569829711918008165 114004226919343070984626531)
          ·
            refine ⟨171006340379014606476939797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114004226919343070984626531 171006340379014606476939797)
            ·
              refine ⟨8015922205266309678606553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 171006340379014606476939797 8015922205266309678606553)
              ·
                refine ⟨6011941653949732258954915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8015922205266309678606553 6011941653949732258954915)
                ·
                  refine ⟨9017912480924598388432373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6011941653949732258954915 9017912480924598388432373)
                  ·
                    refine ⟨845429295086681098915535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9017912480924598388432373 845429295086681098915535)
                    ·
                      rfl

theorem cell23_4939403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 5].length) (baseStart_4939403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939403 prefixEnd_4939403 := by exact prefixLift 4939403
  have htrace : WordTrace (prefixWord ++ tailWord_4939403) baseStart_4939403 baseEnd_4939403 := by
    simpa [prefixWord, tailWord_4939403, baseEnd_4939403] using wordTrace_append hprefix tailTrace_4939403
  have hstable : (prefixWord ++ tailWord_4939403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939403).length < 2 ^ (prefixWord ++ tailWord_4939403).sum := by decide
  have hdescent : baseEnd_4939403 < baseStart_4939403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939443 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 3]
def baseStart_4939443 : Nat := 118140960795 + 4939443 * 2 ^ 59
def prefixEnd_4939443 : Nat := 4983230072969 + 3 ^ 40 * 4939443 * 2
def baseEnd_4939443 : Nat := 2536308424486223140246421

theorem tailTrace_4939443 : CollatzResearch.WordTrace tailWord_4939443 prefixEnd_4939443 2536308424486223140246421 := by
  unfold tailWord_4939443
  simp only [CollatzResearch.WordTrace]
  refine ⟨180156286644249075547902983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120104191096166050365268655 180156286644249075547902983)
  ·
    refine ⟨270234429966373613321854475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180156286644249075547902983 270234429966373613321854475)
    ·
      refine ⟨405351644949560419982781713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270234429966373613321854475 405351644949560419982781713)
      ·
        refine ⟨304013733712170314987086285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405351644949560419982781713 304013733712170314987086285)
        ·
          refine ⟨114005150142063868120157357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304013733712170314987086285 114005150142063868120157357)
          ·
            refine ⟨42751931303273950545059009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114005150142063868120157357 42751931303273950545059009)
            ·
              refine ⟨32063948477455462908794257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42751931303273950545059009 32063948477455462908794257)
              ·
                refine ⟨24047961358091597181595693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32063948477455462908794257 24047961358091597181595693)
                ·
                  refine ⟨9017985509284348943098385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24047961358091597181595693 9017985509284348943098385)
                  ·
                    refine ⟨6763489131963261707323789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9017985509284348943098385 6763489131963261707323789)
                    ·
                      refine ⟨2536308424486223140246421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6763489131963261707323789 2536308424486223140246421)
                      ·
                        rfl

theorem cell23_4939443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_4939443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939443 prefixEnd_4939443 := by exact prefixLift 4939443
  have htrace : WordTrace (prefixWord ++ tailWord_4939443) baseStart_4939443 baseEnd_4939443 := by
    simpa [prefixWord, tailWord_4939443, baseEnd_4939443] using wordTrace_append hprefix tailTrace_4939443
  have hstable : (prefixWord ++ tailWord_4939443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939443).length < 2 ^ (prefixWord ++ tailWord_4939443).sum := by decide
  have hdescent : baseEnd_4939443 < baseStart_4939443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939450 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_4939450 : Nat := 118140960795 + 4939450 * 2 ^ 59
def prefixEnd_4939450 : Nat := 4983230072969 + 3 ^ 40 * 4939450 * 2
def baseEnd_4939450 : Nat := 845437339616934870952963

theorem tailTrace_4939450 : CollatzResearch.WordTrace tailWord_4939450 prefixEnd_4939450 845437339616934870952963 := by
  unfold tailWord_4939450
  simp only [CollatzResearch.WordTrace]
  refine ⟨45039135488805928935851951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120104361303482477162271869 45039135488805928935851951)
  ·
    refine ⟨67558703233208893403777927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45039135488805928935851951 67558703233208893403777927)
    ·
      refine ⟨101338054849813340105666891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67558703233208893403777927 101338054849813340105666891)
      ·
        refine ⟨152007082274720010158500337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101338054849813340105666891 152007082274720010158500337)
        ·
          refine ⟨114005311706040007618875253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152007082274720010158500337 114005311706040007618875253)
          ·
            refine ⟨10687997972441250714269555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114005311706040007618875253 10687997972441250714269555)
            ·
              refine ⟨16031996958661876071404333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10687997972441250714269555 16031996958661876071404333)
              ·
                refine ⟨6011998859498203526776625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16031996958661876071404333 6011998859498203526776625)
                ·
                  refine ⟨4508999144623652645082469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6011998859498203526776625 4508999144623652645082469)
                  ·
                    refine ⟨845437339616934870952963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4508999144623652645082469 845437339616934870952963)
                    ·
                      rfl

theorem cell23_4939450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_4939450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939450 prefixEnd_4939450 := by exact prefixLift 4939450
  have htrace : WordTrace (prefixWord ++ tailWord_4939450) baseStart_4939450 baseEnd_4939450 := by
    simpa [prefixWord, tailWord_4939450, baseEnd_4939450] using wordTrace_append hprefix tailTrace_4939450
  have hstable : (prefixWord ++ tailWord_4939450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939450).length < 2 ^ (prefixWord ++ tailWord_4939450).sum := by decide
  have hdescent : baseEnd_4939450 < baseStart_4939450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939453 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4939453 : Nat := 118140960795 + 4939453 * 2 ^ 59
def prefixEnd_4939453 : Nat := 4983230072969 + 3 ^ 40 * 4939453 * 2
def baseEnd_4939453 : Nat := 2536313559292768101121375

theorem tailTrace_4939453 : CollatzResearch.WordTrace tailWord_4939453 prefixEnd_4939453 2536313559292768101121375 := by
  unfold tailWord_4939453
  simp only [CollatzResearch.WordTrace]
  refine ⟨180156651374212847255767013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120104434249475231503844675 180156651374212847255767013)
  ·
    refine ⟨33779372132664908860456315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180156651374212847255767013 33779372132664908860456315)
    ·
      refine ⟨50669058198997363290684473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33779372132664908860456315 50669058198997363290684473)
      ·
        refine ⟨38001793649248022468013355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50669058198997363290684473 38001793649248022468013355)
        ·
          refine ⟨57002690473872033702020033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38001793649248022468013355 57002690473872033702020033)
          ·
            refine ⟨42752017855404025276515025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57002690473872033702020033 42752017855404025276515025)
            ·
              refine ⟨32064013391553018957386269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42752017855404025276515025 32064013391553018957386269)
              ·
                refine ⟨12024005021832382109019851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32064013391553018957386269 12024005021832382109019851)
                ·
                  refine ⟨18036007532748573163529777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12024005021832382109019851 18036007532748573163529777)
                  ·
                    refine ⟨13527005649561429872647333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18036007532748573163529777 13527005649561429872647333)
                    ·
                      refine ⟨2536313559292768101121375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13527005649561429872647333 2536313559292768101121375)
                      ·
                        rfl

theorem cell23_4939453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4939453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939453 prefixEnd_4939453 := by exact prefixLift 4939453
  have htrace : WordTrace (prefixWord ++ tailWord_4939453) baseStart_4939453 baseEnd_4939453 := by
    simpa [prefixWord, tailWord_4939453, baseEnd_4939453] using wordTrace_append hprefix tailTrace_4939453
  have hstable : (prefixWord ++ tailWord_4939453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939453).length < 2 ^ (prefixWord ++ tailWord_4939453).sum := by decide
  have hdescent : baseEnd_4939453 < baseStart_4939453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939460 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_4939460 : Nat := 118140960795 + 4939460 * 2 ^ 59
def prefixEnd_4939460 : Nat := 4983230072969 + 3 ^ 40 * 4939460 * 2
def baseEnd_4939460 : Nat := 2536317153657349573733843

theorem tailTrace_4939460 : CollatzResearch.WordTrace tailWord_4939460 prefixEnd_4939460 2536317153657349573733843 := by
  unfold tailWord_4939460
  simp only [CollatzResearch.WordTrace]
  refine ⟨90078453342593743725635917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120104604456791658300847889 90078453342593743725635917)
  ·
    refine ⟨33779420003472653897113469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90078453342593743725635917 33779420003472653897113469)
    ·
      refine ⟨12667282501302245211417551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33779420003472653897113469 12667282501302245211417551)
      ·
        refine ⟨19000923751953367817126327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12667282501302245211417551 19000923751953367817126327)
        ·
          refine ⟨28501385627930051725689491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19000923751953367817126327 28501385627930051725689491)
          ·
            refine ⟨42752078441895077588534237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28501385627930051725689491 42752078441895077588534237)
            ·
              refine ⟨16032029415710654095700339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42752078441895077588534237 16032029415710654095700339)
              ·
                refine ⟨24048044123565981143550509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16032029415710654095700339 24048044123565981143550509)
                ·
                  refine ⟨9018016546337242928831441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24048044123565981143550509 9018016546337242928831441)
                  ·
                    refine ⟨6763512409752932196623581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9018016546337242928831441 6763512409752932196623581)
                    ·
                      refine ⟨2536317153657349573733843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6763512409752932196623581 2536317153657349573733843)
                      ·
                        rfl

theorem cell23_4939460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_4939460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939460 prefixEnd_4939460 := by exact prefixLift 4939460
  have htrace : WordTrace (prefixWord ++ tailWord_4939460) baseStart_4939460 baseEnd_4939460 := by
    simpa [prefixWord, tailWord_4939460, baseEnd_4939460] using wordTrace_append hprefix tailTrace_4939460
  have hstable : (prefixWord ++ tailWord_4939460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939460).length < 2 ^ (prefixWord ++ tailWord_4939460).sum := by decide
  have hdescent : baseEnd_4939460 < baseStart_4939460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939473 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_4939473 : Nat := 118140960795 + 4939473 * 2 ^ 59
def prefixEnd_4939473 : Nat := 4983230072969 + 3 ^ 40 * 4939473 * 2
def baseEnd_4939473 : Nat := 2536323828905858022871283

theorem tailTrace_4939473 : CollatzResearch.WordTrace tailWord_4939473 prefixEnd_4939473 2536323828905858022871283 := by
  unfold tailWord_4939473
  simp only [CollatzResearch.WordTrace]
  refine ⟨180157380834140390671495073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120104920556093593780996715 180157380834140390671495073)
  ·
    refine ⟨135118035625605293003621305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180157380834140390671495073 135118035625605293003621305)
    ·
      refine ⟨101338526719203969752715979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135118035625605293003621305 101338526719203969752715979)
      ·
        refine ⟨152007790078805954629073969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101338526719203969752715979 152007790078805954629073969)
        ·
          refine ⟨114005842559104465971805477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152007790078805954629073969 114005842559104465971805477)
          ·
            refine ⟨21376095479832087369713527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114005842559104465971805477 21376095479832087369713527)
            ·
              refine ⟨32064143219748131054570291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21376095479832087369713527 32064143219748131054570291)
              ·
                refine ⟨48096214829622196581855437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32064143219748131054570291 48096214829622196581855437)
                ·
                  refine ⟨18036080561108323718195789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48096214829622196581855437 18036080561108323718195789)
                  ·
                    refine ⟨6763530210415621394323421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18036080561108323718195789 6763530210415621394323421)
                    ·
                      refine ⟨2536323828905858022871283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6763530210415621394323421 2536323828905858022871283)
                      ·
                        rfl

theorem cell23_4939473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_4939473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939473 prefixEnd_4939473 := by exact prefixLift 4939473
  have htrace : WordTrace (prefixWord ++ tailWord_4939473) baseStart_4939473 baseEnd_4939473 := by
    simpa [prefixWord, tailWord_4939473, baseEnd_4939473] using wordTrace_append hprefix tailTrace_4939473
  have hstable : (prefixWord ++ tailWord_4939473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939473).length < 2 ^ (prefixWord ++ tailWord_4939473).sum := by decide
  have hdescent : baseEnd_4939473 < baseStart_4939473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939484 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4939484 : Nat := 118140960795 + 4939484 * 2 ^ 59
def prefixEnd_4939484 : Nat := 4983230072969 + 3 ^ 40 * 4939484 * 2
def baseEnd_4939484 : Nat := 845443159064352493277911

theorem tailTrace_4939484 : CollatzResearch.WordTrace tailWord_4939484 prefixEnd_4939484 845443159064352493277911 := by
  unfold tailWord_4939484
  simp only [CollatzResearch.WordTrace]
  refine ⟨90078891018550269775072753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120105188024733693033430337 90078891018550269775072753)
  ·
    refine ⟨67559168263912702331304565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90078891018550269775072753 67559168263912702331304565)
    ·
      refine ⟨6333672024741815843559803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67559168263912702331304565 6333672024741815843559803)
      ·
        refine ⟨9500508037112723765339705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6333672024741815843559803 9500508037112723765339705)
        ·
          refine ⟨7125381027834542824004779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9500508037112723765339705 7125381027834542824004779)
          ·
            refine ⟨10688071541751814236007169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7125381027834542824004779 10688071541751814236007169)
            ·
              refine ⟨8016053656313860677005377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10688071541751814236007169 8016053656313860677005377)
              ·
                refine ⟨6012040242235395507754033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8016053656313860677005377 6012040242235395507754033)
                ·
                  refine ⟨4509030181676546630815525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6012040242235395507754033 4509030181676546630815525)
                  ·
                    refine ⟨845443159064352493277911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4509030181676546630815525 845443159064352493277911)
                    ·
                      rfl

theorem cell23_4939484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4939484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939484 prefixEnd_4939484 := by exact prefixLift 4939484
  have htrace : WordTrace (prefixWord ++ tailWord_4939484) baseStart_4939484 baseEnd_4939484 := by
    simpa [prefixWord, tailWord_4939484, baseEnd_4939484] using wordTrace_append hprefix tailTrace_4939484
  have hstable : (prefixWord ++ tailWord_4939484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939484).length < 2 ^ (prefixWord ++ tailWord_4939484).sum := by decide
  have hdescent : baseEnd_4939484 < baseStart_4939484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939485 : List Nat := [1, 4, 3, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4939485 : Nat := 118140960795 + 4939485 * 2 ^ 59
def prefixEnd_4939485 : Nat := 4983230072969 + 3 ^ 40 * 4939485 * 2
def baseEnd_4939485 : Nat := 2536329990673711975921229

theorem tailTrace_4939485 : CollatzResearch.WordTrace tailWord_4939485 prefixEnd_4939485 2536329990673711975921229 := by
  unfold tailWord_4939485
  simp only [CollatzResearch.WordTrace]
  refine ⟨180157818510096916720931909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120105212340064611147287939 180157818510096916720931909)
  ·
    refine ⟨33779590970643171885174733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180157818510096916720931909 33779590970643171885174733)
    ·
      refine ⟨12667346613991189456940525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33779590970643171885174733 12667346613991189456940525)
      ·
        refine ⟨4750254980246696046352697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12667346613991189456940525 4750254980246696046352697)
        ·
          refine ⟨3562691235185022034764523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4750254980246696046352697 3562691235185022034764523)
          ·
            refine ⟨5344036852777533052146785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562691235185022034764523 5344036852777533052146785)
            ·
              refine ⟨4008027639583149789110089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5344036852777533052146785 4008027639583149789110089)
              ·
                refine ⟨3006020729687362341832567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4008027639583149789110089 3006020729687362341832567)
                ·
                  refine ⟨4509031094531043512748851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006020729687362341832567 4509031094531043512748851)
                  ·
                    refine ⟨6763546641796565269123277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4509031094531043512748851 6763546641796565269123277)
                    ·
                      refine ⟨2536329990673711975921229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6763546641796565269123277 2536329990673711975921229)
                      ·
                        rfl

theorem cell23_4939485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4939485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939485 prefixEnd_4939485 := by exact prefixLift 4939485
  have htrace : WordTrace (prefixWord ++ tailWord_4939485) baseStart_4939485 baseEnd_4939485 := by
    simpa [prefixWord, tailWord_4939485, baseEnd_4939485] using wordTrace_append hprefix tailTrace_4939485
  have hstable : (prefixWord ++ tailWord_4939485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939485).length < 2 ^ (prefixWord ++ tailWord_4939485).sum := by decide
  have hdescent : baseEnd_4939485 < baseStart_4939485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939491 : List Nat := [1, 1, 1, 7, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4939491 : Nat := 118140960795 + 4939491 * 2 ^ 59
def prefixEnd_4939491 : Nat := 4983230072969 + 3 ^ 40 * 4939491 * 2
def baseEnd_4939491 : Nat := 2536333071557638952446201

theorem tailTrace_4939491 : CollatzResearch.WordTrace tailWord_4939491 prefixEnd_4939491 2536333071557638952446201 := by
  unfold tailWord_4939491
  simp only [CollatzResearch.WordTrace]
  refine ⟨180158037348075179745650327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120105358232050119830433551 180158037348075179745650327)
  ·
    refine ⟨270237056022112769618475491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180158037348075179745650327 270237056022112769618475491)
    ·
      refine ⟨405355584033169154427713237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270237056022112769618475491 405355584033169154427713237)
      ·
        refine ⟨9500521500777402056899529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 405355584033169154427713237 9500521500777402056899529)
        ·
          refine ⟨7125391125583051542674647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9500521500777402056899529 7125391125583051542674647)
          ·
            refine ⟨10688086688374577314011971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7125391125583051542674647 10688086688374577314011971)
            ·
              refine ⟨16032130032561865971017957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10688086688374577314011971 16032130032561865971017957)
              ·
                refine ⟨3006024381105349869565867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16032130032561865971017957 3006024381105349869565867)
                ·
                  refine ⟨4509036571658024804348801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006024381105349869565867 4509036571658024804348801)
                  ·
                    refine ⟨3381777428743518603261601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4509036571658024804348801 3381777428743518603261601)
                    ·
                      refine ⟨2536333071557638952446201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381777428743518603261601 2536333071557638952446201)
                      ·
                        rfl

theorem cell23_4939491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4939491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939491 prefixEnd_4939491 := by exact prefixLift 4939491
  have htrace : WordTrace (prefixWord ++ tailWord_4939491) baseStart_4939491 baseEnd_4939491 := by
    simpa [prefixWord, tailWord_4939491, baseEnd_4939491] using wordTrace_append hprefix tailTrace_4939491
  have hstable : (prefixWord ++ tailWord_4939491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939491).length < 2 ^ (prefixWord ++ tailWord_4939491).sum := by decide
  have hdescent : baseEnd_4939491 < baseStart_4939491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939500 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 3, 3, 2]
def baseStart_4939500 : Nat := 118140960795 + 4939500 * 2 ^ 59
def prefixEnd_4939500 : Nat := 4983230072969 + 3 ^ 40 * 4939500 * 2
def baseEnd_4939500 : Nat := 2536337692883529417233659

theorem tailTrace_4939500 : CollatzResearch.WordTrace tailWord_4939500 prefixEnd_4939500 2536337692883529417233659 := by
  unfold tailWord_4939500
  simp only [CollatzResearch.WordTrace]
  refine ⟨90079182802521287141363977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120105577070028382855151969 90079182802521287141363977)
  ·
    refine ⟨67559387101890965356022983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90079182802521287141363977 67559387101890965356022983)
    ·
      refine ⟨101339080652836448034034475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67559387101890965356022983 101339080652836448034034475)
      ·
        refine ⟨152008620979254672051051713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101339080652836448034034475 152008620979254672051051713)
        ·
          refine ⟨114006465734441004038288785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152008620979254672051051713 114006465734441004038288785)
          ·
            refine ⟨85504849300830753028716589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114006465734441004038288785 85504849300830753028716589)
            ·
              refine ⟨32064318487811532385768721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85504849300830753028716589 32064318487811532385768721)
              ·
                refine ⟨24048238865858649289326541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32064318487811532385768721 24048238865858649289326541)
                ·
                  refine ⟨9018089574696993483497453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24048238865858649289326541 9018089574696993483497453)
                  ·
                    refine ⟨3381783590511372556311545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9018089574696993483497453 3381783590511372556311545)
                    ·
                      refine ⟨2536337692883529417233659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381783590511372556311545 2536337692883529417233659)
                      ·
                        rfl

theorem cell23_4939500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_4939500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939500 prefixEnd_4939500 := by exact prefixLift 4939500
  have htrace : WordTrace (prefixWord ++ tailWord_4939500) baseStart_4939500 baseEnd_4939500 := by
    simpa [prefixWord, tailWord_4939500, baseEnd_4939500] using wordTrace_append hprefix tailTrace_4939500
  have hstable : (prefixWord ++ tailWord_4939500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939500).length < 2 ^ (prefixWord ++ tailWord_4939500).sum := by decide
  have hdescent : baseEnd_4939500 < baseStart_4939500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939534 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_4939534 : Nat := 118140960795 + 4939534 * 2 ^ 59
def prefixEnd_4939534 : Nat := 4983230072969 + 3 ^ 40 * 4939534 * 2
def baseEnd_4939534 : Nat := 2536355151225782284208503

theorem tailTrace_4939534 : CollatzResearch.WordTrace tailWord_4939534 prefixEnd_4939534 2536355151225782284208503 := by
  unfold tailWord_4939534
  simp only [CollatzResearch.WordTrace]
  refine ⟨22519950710864924761183207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120106403791279598726310437 22519950710864924761183207)
  ·
    refine ⟨33779926066297387141774811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22519950710864924761183207 33779926066297387141774811)
    ·
      refine ⟨50669889099446080712662217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33779926066297387141774811 50669889099446080712662217)
      ·
        refine ⟨38002416824584560534496663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50669889099446080712662217 38002416824584560534496663)
        ·
          refine ⟨57003625236876840801744995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38002416824584560534496663 57003625236876840801744995)
          ·
            refine ⟨85505437855315261202617493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57003625236876840801744995 85505437855315261202617493)
            ·
              refine ⟨4008067399467902868872695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85505437855315261202617493 4008067399467902868872695)
              ·
                refine ⟨6012101099201854303309043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4008067399467902868872695 6012101099201854303309043)
                ·
                  refine ⟨9018151648802781454963565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6012101099201854303309043 9018151648802781454963565)
                  ·
                    refine ⟨3381806868301043045611337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9018151648802781454963565 3381806868301043045611337)
                    ·
                      refine ⟨2536355151225782284208503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3381806868301043045611337 2536355151225782284208503)
                      ·
                        rfl

theorem cell23_4939534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_4939534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939534 prefixEnd_4939534 := by exact prefixLift 4939534
  have htrace : WordTrace (prefixWord ++ tailWord_4939534) baseStart_4939534 baseEnd_4939534 := by
    simpa [prefixWord, tailWord_4939534, baseEnd_4939534] using wordTrace_append hprefix tailTrace_4939534
  have hstable : (prefixWord ++ tailWord_4939534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939534).length < 2 ^ (prefixWord ++ tailWord_4939534).sum := by decide
  have hdescent : baseEnd_4939534 < baseStart_4939534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939553 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 7]
def baseStart_4939553 : Nat := 118140960795 + 4939553 * 2 ^ 59
def prefixEnd_4939553 : Nat := 4983230072969 + 3 ^ 40 * 4939553 * 2
def baseEnd_4939553 : Nat := 281818323039801967763435

theorem tailTrace_4939553 : CollatzResearch.WordTrace tailWord_4939553 prefixEnd_4939553 281818323039801967763435 := by
  unfold tailWord_4939553
  simp only [CollatzResearch.WordTrace]
  refine ⟨180160298673850564334407313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120106865782567042889604875 180160298673850564334407313)
  ·
    refine ⟨135120224005387923250805485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180160298673850564334407313 135120224005387923250805485)
    ·
      refine ⟨50670084002020471219052057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135120224005387923250805485 50670084002020471219052057)
      ·
        refine ⟨38002563001515353414289043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50670084002020471219052057 38002563001515353414289043)
        ·
          refine ⟨57003844502273030121433565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38002563001515353414289043 57003844502273030121433565)
          ·
            refine ⟨21376441688352386295537587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57003844502273030121433565 21376441688352386295537587)
            ·
              refine ⟨32064662532528579443306381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21376441688352386295537587 32064662532528579443306381)
              ·
                refine ⟨12024248449698217291239893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32064662532528579443306381 12024248449698217291239893)
                ·
                  refine ⟨281818323039801967763435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12024248449698217291239893 281818323039801967763435)
                  ·
                    rfl

theorem cell23_4939553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 7].length) (baseStart_4939553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939553 prefixEnd_4939553 := by exact prefixLift 4939553
  have htrace : WordTrace (prefixWord ++ tailWord_4939553) baseStart_4939553 baseEnd_4939553 := by
    simpa [prefixWord, tailWord_4939553, baseEnd_4939553] using wordTrace_append hprefix tailTrace_4939553
  have hstable : (prefixWord ++ tailWord_4939553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939553).length < 2 ^ (prefixWord ++ tailWord_4939553).sum := by decide
  have hdescent : baseEnd_4939553 < baseStart_4939553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939560 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4939560 : Nat := 118140960795 + 4939560 * 2 ^ 59
def prefixEnd_4939560 : Nat := 4983230072969 + 3 ^ 40 * 4939560 * 2
def baseEnd_4939560 : Nat := 2536368501722799182483383

theorem tailTrace_4939560 : CollatzResearch.WordTrace tailWord_4939560 prefixEnd_4939560 2536368501722799182483383 := by
  unfold tailWord_4939560
  simp only [CollatzResearch.WordTrace]
  refine ⟨90080276992412602264956067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120107035989883469686608089 90080276992412602264956067)
  ·
    refine ⟨135120415488618903397434101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90080276992412602264956067 135120415488618903397434101)
    ·
      refine ⟨12667538952058022193509447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135120415488618903397434101 12667538952058022193509447)
      ·
        refine ⟨19001308428087033290264171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12667538952058022193509447 19001308428087033290264171)
        ·
          refine ⟨28501962642130549935396257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19001308428087033290264171 28501962642130549935396257)
          ·
            refine ⟨21376471981597912451547193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28501962642130549935396257 21376471981597912451547193)
            ·
              refine ⟨16032353986198434338660395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21376471981597912451547193 16032353986198434338660395)
              ·
                refine ⟨24048530979297651507990593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16032353986198434338660395 24048530979297651507990593)
                ·
                  refine ⟨18036398234473238630992945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24048530979297651507990593 18036398234473238630992945)
                  ·
                    refine ⟨13527298675854928973244709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18036398234473238630992945 13527298675854928973244709)
                    ·
                      refine ⟨2536368501722799182483383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13527298675854928973244709 2536368501722799182483383)
                      ·
                        rfl

theorem cell23_4939560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4939560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939560 prefixEnd_4939560 := by exact prefixLift 4939560
  have htrace : WordTrace (prefixWord ++ tailWord_4939560) baseStart_4939560 baseEnd_4939560 := by
    simpa [prefixWord, tailWord_4939560, baseEnd_4939560] using wordTrace_append hprefix tailTrace_4939560
  have hstable : (prefixWord ++ tailWord_4939560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939560).length < 2 ^ (prefixWord ++ tailWord_4939560).sum := by decide
  have hdescent : baseEnd_4939560 < baseStart_4939560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939563 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 3]
def baseStart_4939563 : Nat := 118140960795 + 4939563 * 2 ^ 59
def prefixEnd_4939563 : Nat := 4983230072969 + 3 ^ 40 * 4939563 * 2
def baseEnd_4939563 : Nat := 2536370042164762670745869

theorem tailTrace_4939563 : CollatzResearch.WordTrace tailWord_4939563 prefixEnd_4939563 2536370042164762670745869 := by
  unfold tailWord_4939563
  simp only [CollatzResearch.WordTrace]
  refine ⟨180160663403814336042271343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120107108935876224028180895 180160663403814336042271343)
  ·
    refine ⟨270240995105721504063407015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180160663403814336042271343 270240995105721504063407015)
    ·
      refine ⟨405361492658582256095110523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270240995105721504063407015 405361492658582256095110523)
      ·
        refine ⟨608042238987873384142665785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405361492658582256095110523 608042238987873384142665785)
        ·
          refine ⟨456031679240905038106999339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608042238987873384142665785 456031679240905038106999339)
          ·
            refine ⟨684047518861357557160499009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456031679240905038106999339 684047518861357557160499009)
            ·
              refine ⟨513035639146018167870374257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684047518861357557160499009 513035639146018167870374257)
              ·
                refine ⟨384776729359513625902780693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513035639146018167870374257 384776729359513625902780693)
                ·
                  refine ⟨18036409188727201214192845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 384776729359513625902780693 18036409188727201214192845)
                  ·
                    refine ⟨6763653445772700455322317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18036409188727201214192845 6763653445772700455322317)
                    ·
                      refine ⟨2536370042164762670745869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6763653445772700455322317 2536370042164762670745869)
                      ·
                        rfl

theorem cell23_4939563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 3].length) (baseStart_4939563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939563 prefixEnd_4939563 := by exact prefixLift 4939563
  have htrace : WordTrace (prefixWord ++ tailWord_4939563) baseStart_4939563 baseEnd_4939563 := by
    simpa [prefixWord, tailWord_4939563, baseEnd_4939563] using wordTrace_append hprefix tailTrace_4939563
  have hstable : (prefixWord ++ tailWord_4939563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939563).length < 2 ^ (prefixWord ++ tailWord_4939563).sum := by decide
  have hdescent : baseEnd_4939563 < baseStart_4939563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939587 : List Nat := [1, 1, 1, 3, 1, 7, 1, 3, 5]
def baseStart_4939587 : Nat := 118140960795 + 4939587 * 2 ^ 59
def prefixEnd_4939587 : Nat := 4983230072969 + 3 ^ 40 * 4939587 * 2
def baseEnd_4939587 : Nat := 281820262855607841871751

theorem tailTrace_4939587 : CollatzResearch.WordTrace tailWord_4939587 prefixEnd_4939587 281820262855607841871751 := by
  unfold tailWord_4939587
  simp only [CollatzResearch.WordTrace]
  refine ⟨180161538755727388141145015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120107692503818258760763343 180161538755727388141145015)
  ·
    refine ⟨270242308133591082211717523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180161538755727388141145015 270242308133591082211717523)
    ·
      refine ⟨405363462200386623317576285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270242308133591082211717523 405363462200386623317576285)
      ·
        refine ⟨152011298325144983744091107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 405363462200386623317576285 152011298325144983744091107)
        ·
          refine ⟨228016947487717475616136661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152011298325144983744091107 228016947487717475616136661)
          ·
            refine ⟨5344147206743378334753203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 228016947487717475616136661 5344147206743378334753203)
            ·
              refine ⟨8016220810115067502129805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5344147206743378334753203 8016220810115067502129805)
              ·
                refine ⟨3006082803793150313298677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8016220810115067502129805 3006082803793150313298677)
                ·
                  refine ⟨281820262855607841871751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006082803793150313298677 281820262855607841871751)
                  ·
                    rfl

theorem cell23_4939587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 5].length) (baseStart_4939587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939587 prefixEnd_4939587 := by exact prefixLift 4939587
  have htrace : WordTrace (prefixWord ++ tailWord_4939587) baseStart_4939587 baseEnd_4939587 := by
    simpa [prefixWord, tailWord_4939587, baseEnd_4939587] using wordTrace_append hprefix tailTrace_4939587
  have hstable : (prefixWord ++ tailWord_4939587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939587).length < 2 ^ (prefixWord ++ tailWord_4939587).sum := by decide
  have hdescent : baseEnd_4939587 < baseStart_4939587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939593 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_4939593 : Nat := 118140960795 + 4939593 * 2 ^ 59
def prefixEnd_4939593 : Nat := 4983230072969 + 3 ^ 40 * 4939593 * 2
def baseEnd_4939593 : Nat := 2536385446584397553370731

theorem tailTrace_4939593 : CollatzResearch.WordTrace tailWord_4939593 prefixEnd_4939593 2536385446584397553370731 := by
  unfold tailWord_4939593
  simp only [CollatzResearch.WordTrace]
  refine ⟨180161757593705651165863433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120107838395803767443908955 180161757593705651165863433)
  ·
    refine ⟨135121318195279238374397575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180161757593705651165863433 135121318195279238374397575)
    ·
      refine ⟨202681977292918857561596363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135121318195279238374397575 202681977292918857561596363)
      ·
        refine ⟨304022965939378286342394545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202681977292918857561596363 304022965939378286342394545)
        ·
          refine ⟨228017224454533714756795909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304022965939378286342394545 228017224454533714756795909)
          ·
            refine ⟨42753229585225071516899233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228017224454533714756795909 42753229585225071516899233)
            ·
              refine ⟨32064922188918803637674425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42753229585225071516899233 32064922188918803637674425)
              ·
                refine ⟨24048691641689102728255819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32064922188918803637674425 24048691641689102728255819)
                ·
                  refine ⟨36073037462533654092383729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24048691641689102728255819 36073037462533654092383729)
                  ·
                    refine ⟨27054778096900240569287797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36073037462533654092383729 27054778096900240569287797)
                    ·
                      refine ⟨2536385446584397553370731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27054778096900240569287797 2536385446584397553370731)
                      ·
                        rfl

theorem cell23_4939593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_4939593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939593 prefixEnd_4939593 := by exact prefixLift 4939593
  have htrace : WordTrace (prefixWord ++ tailWord_4939593) baseStart_4939593 baseEnd_4939593 := by
    simpa [prefixWord, tailWord_4939593, baseEnd_4939593] using wordTrace_append hprefix tailTrace_4939593
  have hstable : (prefixWord ++ tailWord_4939593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939593).length < 2 ^ (prefixWord ++ tailWord_4939593).sum := by decide
  have hdescent : baseEnd_4939593 < baseStart_4939593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939604 : List Nat := [2, 4, 1, 1, 3, 2, 3, 2, 5]
def baseStart_4939604 : Nat := 118140960795 + 4939604 * 2 ^ 59
def prefixEnd_4939604 : Nat := 4983230072969 + 3 ^ 40 * 4939604 * 2
def baseEnd_4939604 : Nat := 281821232763510778925909

theorem tailTrace_4939604 : CollatzResearch.WordTrace tailWord_4939604 prefixEnd_4939604 281821232763510778925909 := by
  unfold tailWord_4939604
  simp only [CollatzResearch.WordTrace]
  refine ⟨90081079398332900022256933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120108105864443866696342577 90081079398332900022256933)
  ·
    refine ⟨16890202387187418754173175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90081079398332900022256933 16890202387187418754173175)
    ·
      refine ⟨25335303580781128131259763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16890202387187418754173175 25335303580781128131259763)
      ·
        refine ⟨38002955371171692196889645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25335303580781128131259763 38002955371171692196889645)
        ·
          refine ⟨14251108264189384573833617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38002955371171692196889645 14251108264189384573833617)
          ·
            refine ⟨10688331198142038430375213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14251108264189384573833617 10688331198142038430375213)
            ·
              refine ⟨4008124199303264411390705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10688331198142038430375213 4008124199303264411390705)
              ·
                refine ⟨3006093149477448308543029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4008124199303264411390705 3006093149477448308543029)
                ·
                  refine ⟨281821232763510778925909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006093149477448308543029 281821232763510778925909)
                  ·
                    rfl

theorem cell23_4939604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_4939604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939604 prefixEnd_4939604 := by exact prefixLift 4939604
  have htrace : WordTrace (prefixWord ++ tailWord_4939604) baseStart_4939604 baseEnd_4939604 := by
    simpa [prefixWord, tailWord_4939604, baseEnd_4939604] using wordTrace_append hprefix tailTrace_4939604
  have hstable : (prefixWord ++ tailWord_4939604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939604).length < 2 ^ (prefixWord ++ tailWord_4939604).sum := by decide
  have hdescent : baseEnd_4939604 < baseStart_4939604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939637 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_4939637 : Nat := 118140960795 + 4939637 * 2 ^ 59
def prefixEnd_4939637 : Nat := 4983230072969 + 3 ^ 40 * 4939637 * 2
def baseEnd_4939637 : Nat := 2536408039733195381220529

theorem tailTrace_4939637 : CollatzResearch.WordTrace tailWord_4939637 prefixEnd_4939637 2536408039733195381220529 := by
  unfold tailWord_4939637
  simp only [CollatzResearch.WordTrace]
  refine ⟨180163362405546246680465165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120108908270364164453643443 180163362405546246680465165)
  ·
    refine ⟨67561260902079842505174437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180163362405546246680465165 67561260902079842505174437)
    ·
      refine ⟨12667736419139970469720207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67561260902079842505174437 12667736419139970469720207)
      ·
        refine ⟨19001604628709955704580311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12667736419139970469720207 19001604628709955704580311)
        ·
          refine ⟨28502406943064933556870467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19001604628709955704580311 28502406943064933556870467)
          ·
            refine ⟨42753610414597400335305701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28502406943064933556870467 42753610414597400335305701)
            ·
              refine ⟨8016301952737012562869819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42753610414597400335305701 8016301952737012562869819)
              ·
                refine ⟨12024452929105518844304729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8016301952737012562869819 12024452929105518844304729)
                ·
                  refine ⟨9018339696829139133228547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12024452929105518844304729 9018339696829139133228547)
                  ·
                    refine ⟨13527509545243708699842821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9018339696829139133228547 13527509545243708699842821)
                    ·
                      refine ⟨2536408039733195381220529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13527509545243708699842821 2536408039733195381220529)
                      ·
                        rfl

theorem cell23_4939637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_4939637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939637 prefixEnd_4939637 := by exact prefixLift 4939637
  have htrace : WordTrace (prefixWord ++ tailWord_4939637) baseStart_4939637 baseEnd_4939637 := by
    simpa [prefixWord, tailWord_4939637, baseEnd_4939637] using wordTrace_append hprefix tailTrace_4939637
  have hstable : (prefixWord ++ tailWord_4939637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939637).length < 2 ^ (prefixWord ++ tailWord_4939637).sum := by decide
  have hdescent : baseEnd_4939637 < baseStart_4939637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939647 : List Nat := [1, 1, 2, 2, 1, 1, 3, 7, 1, 4]
def baseStart_4939647 : Nat := 118140960795 + 4939647 * 2 ^ 59
def prefixEnd_4939647 : Nat := 4983230072969 + 3 ^ 40 * 4939647 * 2
def baseEnd_4939647 : Nat := 845471058179913447365161

theorem tailTrace_4939647 : CollatzResearch.WordTrace tailWord_4939647 prefixEnd_4939647 845471058179913447365161 := by
  unfold tailWord_4939647
  simp only [CollatzResearch.WordTrace]
  refine ⟨180163727135510018388329195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120109151423673345592219463 180163727135510018388329195)
  ·
    refine ⟨270245590703265027582493793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180163727135510018388329195 270245590703265027582493793)
    ·
      refine ⟨202684193027448770686870345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270245590703265027582493793 202684193027448770686870345)
      ·
        refine ⟨152013144770586578015152759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202684193027448770686870345 152013144770586578015152759)
        ·
          refine ⟨228019717155879867022729139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152013144770586578015152759 228019717155879867022729139)
          ·
            refine ⟨342029575733819800534093709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228019717155879867022729139 342029575733819800534093709)
            ·
              refine ⟨128261090900182425200285141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342029575733819800534093709 128261090900182425200285141)
              ·
                refine ⟨3006119317973025590631683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 128261090900182425200285141 3006119317973025590631683)
                ·
                  refine ⟨4509178976959538385947525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006119317973025590631683 4509178976959538385947525)
                  ·
                    refine ⟨845471058179913447365161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4509178976959538385947525 845471058179913447365161)
                    ·
                      rfl

theorem cell23_4939647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 4].length) (baseStart_4939647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939647 prefixEnd_4939647 := by exact prefixLift 4939647
  have htrace : WordTrace (prefixWord ++ tailWord_4939647) baseStart_4939647 baseEnd_4939647 := by
    simpa [prefixWord, tailWord_4939647, baseEnd_4939647] using wordTrace_append hprefix tailTrace_4939647
  have hstable : (prefixWord ++ tailWord_4939647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939647).length < 2 ^ (prefixWord ++ tailWord_4939647).sum := by decide
  have hdescent : baseEnd_4939647 < baseStart_4939647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939683 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 7]
def baseStart_4939683 : Nat := 118140960795 + 4939683 * 2 ^ 59
def prefixEnd_4939683 : Nat := 4983230072969 + 3 ^ 40 * 4939683 * 2
def baseEnd_4939683 : Nat := 2536431659843302201245317

theorem tailTrace_4939683 : CollatzResearch.WordTrace tailWord_4939683 prefixEnd_4939683 2536431659843302201245317 := by
  unfold tailWord_4939683
  simp only [CollatzResearch.WordTrace]
  refine ⟨180165040163379596536639703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120110026775586397691093135 180165040163379596536639703)
  ·
    refine ⟨270247560245069394804959555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180165040163379596536639703 270247560245069394804959555)
    ·
      refine ⟨405371340367604092207439333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270247560245069394804959555 405371340367604092207439333)
      ·
        refine ⟨76007126318925767288894875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 405371340367604092207439333 76007126318925767288894875)
        ·
          refine ⟨114010689478388650933342313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76007126318925767288894875 114010689478388650933342313)
          ·
            refine ⟨85508017108791488200006735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114010689478388650933342313 85508017108791488200006735)
            ·
              refine ⟨128262025663187232300010103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85508017108791488200006735 128262025663187232300010103)
              ·
                refine ⟨192393038494780848450015155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128262025663187232300010103 192393038494780848450015155)
                ·
                  refine ⟨288589557742171272675022733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192393038494780848450015155 288589557742171272675022733)
                  ·
                    refine ⟨108221084153314227253133525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 288589557742171272675022733 108221084153314227253133525)
                    ·
                      refine ⟨2536431659843302201245317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108221084153314227253133525 2536431659843302201245317)
                      ·
                        rfl

theorem cell23_4939683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_4939683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939683 prefixEnd_4939683 := by exact prefixLift 4939683
  have htrace : WordTrace (prefixWord ++ tailWord_4939683) baseStart_4939683 baseEnd_4939683 := by
    simpa [prefixWord, tailWord_4939683, baseEnd_4939683] using wordTrace_append hprefix tailTrace_4939683
  have hstable : (prefixWord ++ tailWord_4939683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939683).length < 2 ^ (prefixWord ++ tailWord_4939683).sum := by decide
  have hdescent : baseEnd_4939683 < baseStart_4939683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939688 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4939688 : Nat := 118140960795 + 4939688 * 2 ^ 59
def prefixEnd_4939688 : Nat := 4983230072969 + 3 ^ 40 * 4939688 * 2
def baseEnd_4939688 : Nat := 2536434227246574681682795

theorem tailTrace_4939688 : CollatzResearch.WordTrace tailWord_4939688 prefixEnd_4939688 2536434227246574681682795 := by
  unfold tailWord_4939688
  simp only [CollatzResearch.WordTrace]
  refine ⟨90082611264180741195285859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120110148352240988260381145 90082611264180741195285859)
  ·
    refine ⟨135123916896271111792928789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90082611264180741195285859 135123916896271111792928789)
    ·
      refine ⟨6333933604512708365293537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 135123916896271111792928789 6333933604512708365293537)
      ·
        refine ⟨4750450203384531273970153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6333933604512708365293537 4750450203384531273970153)
        ·
          refine ⟨3562837652538398455477615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4750450203384531273970153 3562837652538398455477615)
          ·
            refine ⟨5344256478807597683216423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562837652538398455477615 5344256478807597683216423)
            ·
              refine ⟨8016384718211396524824635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5344256478807597683216423 8016384718211396524824635)
              ·
                refine ⟨12024577077317094787236953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8016384718211396524824635 12024577077317094787236953)
                ·
                  refine ⟨9018432807987821090427715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12024577077317094787236953 9018432807987821090427715)
                  ·
                    refine ⟨13527649211981731635641573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9018432807987821090427715 13527649211981731635641573)
                    ·
                      refine ⟨2536434227246574681682795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13527649211981731635641573 2536434227246574681682795)
                      ·
                        rfl

theorem cell23_4939688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4939688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939688 prefixEnd_4939688 := by exact prefixLift 4939688
  have htrace : WordTrace (prefixWord ++ tailWord_4939688) baseStart_4939688 baseEnd_4939688 := by
    simpa [prefixWord, tailWord_4939688, baseEnd_4939688] using wordTrace_append hprefix tailTrace_4939688
  have hstable : (prefixWord ++ tailWord_4939688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939688).length < 2 ^ (prefixWord ++ tailWord_4939688).sum := by decide
  have hdescent : baseEnd_4939688 < baseStart_4939688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939820 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_4939820 : Nat := 118140960795 + 4939820 * 2 ^ 59
def prefixEnd_4939820 : Nat := 4983230072969 + 3 ^ 40 * 4939820 * 2
def baseEnd_4939820 : Nat := 2536502006692968165232187

theorem tailTrace_4939820 : CollatzResearch.WordTrace tailWord_4939820 prefixEnd_4939820 2536502006692968165232187 := by
  unfold tailWord_4939820
  simp only [CollatzResearch.WordTrace]
  refine ⟨90085018481941634467188457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120113357975922179289584609 90085018481941634467188457)
  ·
    refine ⟨67563763861456225850391343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90085018481941634467188457 67563763861456225850391343)
    ·
      refine ⟨101345645792184338775587015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67563763861456225850391343 101345645792184338775587015)
      ·
        refine ⟨152018468688276508163380523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101345645792184338775587015 152018468688276508163380523)
        ·
          refine ⟨228027703032414762245070785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152018468688276508163380523 228027703032414762245070785)
          ·
            refine ⟨171020777274311071683803089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228027703032414762245070785 171020777274311071683803089)
            ·
              refine ⟨128265582955733303762852317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171020777274311071683803089 128265582955733303762852317)
              ·
                refine ⟨48099593608399988911069619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128265582955733303762852317 48099593608399988911069619)
                ·
                  refine ⟨72149390412599983366604429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48099593608399988911069619 72149390412599983366604429)
                  ·
                    refine ⟨27056021404724993762476661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72149390412599983366604429 27056021404724993762476661)
                    ·
                      refine ⟨2536502006692968165232187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27056021404724993762476661 2536502006692968165232187)
                      ·
                        rfl

theorem cell23_4939820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_4939820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939820 prefixEnd_4939820 := by exact prefixLift 4939820
  have htrace : WordTrace (prefixWord ++ tailWord_4939820) baseStart_4939820 baseEnd_4939820 := by
    simpa [prefixWord, tailWord_4939820, baseEnd_4939820] using wordTrace_append hprefix tailTrace_4939820
  have hstable : (prefixWord ++ tailWord_4939820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939820).length < 2 ^ (prefixWord ++ tailWord_4939820).sum := by decide
  have hdescent : baseEnd_4939820 < baseStart_4939820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939837 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4939837 : Nat := 118140960795 + 4939837 * 2 ^ 59
def prefixEnd_4939837 : Nat := 4983230072969 + 3 ^ 40 * 4939837 * 2
def baseEnd_4939837 : Nat := 2536510735864094598719609

theorem tailTrace_4939837 : CollatzResearch.WordTrace tailWord_4939837 prefixEnd_4939837 2536510735864094598719609 := by
  unfold tailWord_4939837
  simp only [CollatzResearch.WordTrace]
  refine ⟨180170657004821680837745765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120113771336547787225163843 180170657004821680837745765)
  ·
    refine ⟨33781998188404065157077331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180170657004821680837745765 33781998188404065157077331)
    ·
      refine ⟨50672997282606097735615997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33781998188404065157077331 50672997282606097735615997)
      ·
        refine ⟨19002373980977286650855999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50672997282606097735615997 19002373980977286650855999)
        ·
          refine ⟨28503560971465929976283999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19002373980977286650855999 28503560971465929976283999)
          ·
            refine ⟨42755341457198894964425999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28503560971465929976283999 42755341457198894964425999)
            ·
              refine ⟨64133012185798342446638999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42755341457198894964425999 64133012185798342446638999)
              ·
                refine ⟨96199518278697513669958499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64133012185798342446638999 96199518278697513669958499)
                ·
                  refine ⟨144299277418046270504937749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96199518278697513669958499 144299277418046270504937749)
                  ·
                    refine ⟨6764028628970918929918957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 144299277418046270504937749 6764028628970918929918957)
                    ·
                      refine ⟨2536510735864094598719609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6764028628970918929918957 2536510735864094598719609)
                      ·
                        rfl

theorem cell23_4939837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4939837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939837 prefixEnd_4939837 := by exact prefixLift 4939837
  have htrace : WordTrace (prefixWord ++ tailWord_4939837) baseStart_4939837 baseEnd_4939837 := by
    simpa [prefixWord, tailWord_4939837, baseEnd_4939837] using wordTrace_append hprefix tailTrace_4939837
  have hstable : (prefixWord ++ tailWord_4939837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939837).length < 2 ^ (prefixWord ++ tailWord_4939837).sum := by decide
  have hdescent : baseEnd_4939837 < baseStart_4939837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939847 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_4939847 : Nat := 118140960795 + 4939847 * 2 ^ 59
def prefixEnd_4939847 : Nat := 4983230072969 + 3 ^ 40 * 4939847 * 2
def baseEnd_4939847 : Nat := 2536515870670639559594563

theorem tailTrace_4939847 : CollatzResearch.WordTrace tailWord_4939847 prefixEnd_4939847 2536515870670639559594563 := by
  unfold tailWord_4939847
  simp only [CollatzResearch.WordTrace]
  refine ⟨180171021734785452545609795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120114014489856968363739863 180171021734785452545609795)
  ·
    refine ⟨270256532602178178818414693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180171021734785452545609795 270256532602178178818414693)
    ·
      refine ⟨50673099862908408528452755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270256532602178178818414693 50673099862908408528452755)
      ·
        refine ⟨76009649794362612792679133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50673099862908408528452755 76009649794362612792679133)
        ·
          refine ⟨28503618672885979797254675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76009649794362612792679133 28503618672885979797254675)
          ·
            refine ⟨42755428009328969695882013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28503618672885979797254675 42755428009328969695882013)
            ·
              refine ⟨16033285503498363635955755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42755428009328969695882013 16033285503498363635955755)
              ·
                refine ⟨24049928255247545453933633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16033285503498363635955755 24049928255247545453933633)
                ·
                  refine ⟨18037446191435659090450225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24049928255247545453933633 18037446191435659090450225)
                  ·
                    refine ⟨13528084643576744317837669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18037446191435659090450225 13528084643576744317837669)
                    ·
                      refine ⟨2536515870670639559594563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13528084643576744317837669 2536515870670639559594563)
                      ·
                        rfl

theorem cell23_4939847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_4939847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939847 prefixEnd_4939847 := by exact prefixLift 4939847
  have htrace : WordTrace (prefixWord ++ tailWord_4939847) baseStart_4939847 baseEnd_4939847 := by
    simpa [prefixWord, tailWord_4939847, baseEnd_4939847] using wordTrace_append hprefix tailTrace_4939847
  have hstable : (prefixWord ++ tailWord_4939847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939847).length < 2 ^ (prefixWord ++ tailWord_4939847).sum := by decide
  have hdescent : baseEnd_4939847 < baseStart_4939847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939907 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 4]
def baseStart_4939907 : Nat := 118140960795 + 4939907 * 2 ^ 59
def prefixEnd_4939907 : Nat := 4983230072969 + 3 ^ 40 * 4939907 * 2
def baseEnd_4939907 : Nat := 2536546679509909324844287

theorem tailTrace_4939907 : CollatzResearch.WordTrace tailWord_4939907 prefixEnd_4939907 2536546679509909324844287 := by
  unfold tailWord_4939907
  simp only [CollatzResearch.WordTrace]
  refine ⟨180173210114568082792793975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120115473409712055195195983 180173210114568082792793975)
  ·
    refine ⟨270259815171852124189190963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180173210114568082792793975 270259815171852124189190963)
    ·
      refine ⟨405389722757778186283786445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270259815171852124189190963 405389722757778186283786445)
      ·
        refine ⟨152021146034166819856419917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 405389722757778186283786445 152021146034166819856419917)
        ·
          refine ⟨57007929762812557446157469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152021146034166819856419917 57007929762812557446157469)
          ·
            refine ⟨21377973661054709042309051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57007929762812557446157469 21377973661054709042309051)
            ·
              refine ⟨32066960491582063563463577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21377973661054709042309051 32066960491582063563463577)
              ·
                refine ⟨24050220368686547672597683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32066960491582063563463577 24050220368686547672597683)
                ·
                  refine ⟨36075330553029821508896525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24050220368686547672597683 36075330553029821508896525)
                  ·
                    refine ⟨13528248957386183065836197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36075330553029821508896525 13528248957386183065836197)
                    ·
                      refine ⟨2536546679509909324844287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13528248957386183065836197 2536546679509909324844287)
                      ·
                        rfl

theorem cell23_4939907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_4939907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939907 prefixEnd_4939907 := by exact prefixLift 4939907
  have htrace : WordTrace (prefixWord ++ tailWord_4939907) baseStart_4939907 baseEnd_4939907 := by
    simpa [prefixWord, tailWord_4939907, baseEnd_4939907] using wordTrace_append hprefix tailTrace_4939907
  have hstable : (prefixWord ++ tailWord_4939907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939907).length < 2 ^ (prefixWord ++ tailWord_4939907).sum := by decide
  have hdescent : baseEnd_4939907 < baseStart_4939907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4939994 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_4939994 : Nat := 118140960795 + 4939994 * 2 ^ 59
def prefixEnd_4939994 : Nat := 4983230072969 + 3 ^ 40 * 4939994 * 2
def baseEnd_4939994 : Nat := 845530450775616828152129

theorem tailTrace_4939994 : CollatzResearch.WordTrace tailWord_4939994 prefixEnd_4939994 845530450775616828152129 := by
  unfold tailWord_4939994
  simp only [CollatzResearch.WordTrace]
  refine ⟨45044095816313224162802759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120117588843501931100807357 45044095816313224162802759)
  ·
    refine ⟨67566143724469836244204139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45044095816313224162802759 67566143724469836244204139)
    ·
      refine ⟨101349215586704754366306209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67566143724469836244204139 101349215586704754366306209)
      ·
        refine ⟨76011911690028565774729657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101349215586704754366306209 76011911690028565774729657)
        ·
          refine ⟨57008933767521424331047243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76011911690028565774729657 57008933767521424331047243)
          ·
            refine ⟨85513400651282136496570865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57008933767521424331047243 85513400651282136496570865)
            ·
              refine ⟨64135050488461602372428149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85513400651282136496570865 64135050488461602372428149)
              ·
                refine ⟨6012660983293275222415139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64135050488461602372428149 6012660983293275222415139)
                ·
                  refine ⟨9018991474939912833622709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6012660983293275222415139 9018991474939912833622709)
                  ·
                    refine ⟨845530450775616828152129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9018991474939912833622709 845530450775616828152129)
                    ·
                      rfl

theorem cell23_4939994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_4939994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4939994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4939994 prefixEnd_4939994 := by exact prefixLift 4939994
  have htrace : WordTrace (prefixWord ++ tailWord_4939994) baseStart_4939994 baseEnd_4939994 := by
    simpa [prefixWord, tailWord_4939994, baseEnd_4939994] using wordTrace_append hprefix tailTrace_4939994
  have hstable : (prefixWord ++ tailWord_4939994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4939994).length < 2 ^ (prefixWord ++ tailWord_4939994).sum := by decide
  have hdescent : baseEnd_4939994 < baseStart_4939994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4939994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940001 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_4940001 : Nat := 118140960795 + 4940001 * 2 ^ 59
def prefixEnd_4940001 : Nat := 4983230072969 + 3 ^ 40 * 4940001 * 2
def baseEnd_4940001 : Nat := 2536594946691431957068855

theorem tailTrace_4940001 : CollatzResearch.WordTrace tailWord_4940001 prefixEnd_4940001 2536594946691431957068855 := by
  unfold tailWord_4940001
  simp only [CollatzResearch.WordTrace]
  refine ⟨180176638576227536846715857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120117759050818357897810571 180176638576227536846715857)
  ·
    refine ⟨135132478932170652635036893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180176638576227536846715857 135132478932170652635036893)
    ·
      refine ⟨50674679599563994738138835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135132478932170652635036893 50674679599563994738138835)
      ·
        refine ⟨76012019399345992107208253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50674679599563994738138835 76012019399345992107208253)
        ·
          refine ⟨28504507274754747040203095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76012019399345992107208253 28504507274754747040203095)
          ·
            refine ⟨42756760912132120560304643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28504507274754747040203095 42756760912132120560304643)
            ·
              refine ⟨64135141368198180840456965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42756760912132120560304643 64135141368198180840456965)
              ·
                refine ⟨12025339006537158907585681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64135141368198180840456965 12025339006537158907585681)
                ·
                  refine ⟨9019004254902869180689261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12025339006537158907585681 9019004254902869180689261)
                  ·
                    refine ⟨3382126595588575942758473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9019004254902869180689261 3382126595588575942758473)
                    ·
                      refine ⟨2536594946691431957068855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3382126595588575942758473 2536594946691431957068855)
                      ·
                        rfl

theorem cell23_4940001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_4940001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940001 prefixEnd_4940001 := by exact prefixLift 4940001
  have htrace : WordTrace (prefixWord ++ tailWord_4940001) baseStart_4940001 baseEnd_4940001 := by
    simpa [prefixWord, tailWord_4940001, baseEnd_4940001] using wordTrace_append hprefix tailTrace_4940001
  have hstable : (prefixWord ++ tailWord_4940001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940001).length < 2 ^ (prefixWord ++ tailWord_4940001).sum := by decide
  have hdescent : baseEnd_4940001 < baseStart_4940001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940044 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_4940044 : Nat := 118140960795 + 4940044 * 2 ^ 59
def prefixEnd_4940044 : Nat := 4983230072969 + 3 ^ 40 * 4940044 * 2
def baseEnd_4940044 : Nat := 2536617026359575288831157

theorem tailTrace_4940044 : CollatzResearch.WordTrace tailWord_4940044 prefixEnd_4940044 2536617026359575288831157 := by
  unfold tailWord_4940044
  simp only [CollatzResearch.WordTrace]
  refine ⟨90089103457535877595265593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120118804610047836793687457 90089103457535877595265593)
  ·
    refine ⟨67566827593151908196449195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90089103457535877595265593 67566827593151908196449195)
    ·
      refine ⟨101350241389727862294673793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67566827593151908196449195 101350241389727862294673793)
      ·
        refine ⟨76012681042295896721005345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101350241389727862294673793 76012681042295896721005345)
        ·
          refine ⟨57009510781721922540754009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76012681042295896721005345 57009510781721922540754009)
          ·
            refine ⟨42757133086291441905565507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57009510781721922540754009 42757133086291441905565507)
            ·
              refine ⟨64135699629437162858348261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42757133086291441905565507 64135699629437162858348261)
              ·
                refine ⟨12025443680519468035940299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64135699629437162858348261 12025443680519468035940299)
                ·
                  refine ⟨18038165520779202053910449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12025443680519468035940299 18038165520779202053910449)
                  ·
                    refine ⟨13528624140584401540432837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18038165520779202053910449 13528624140584401540432837)
                    ·
                      refine ⟨2536617026359575288831157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13528624140584401540432837 2536617026359575288831157)
                      ·
                        rfl

theorem cell23_4940044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_4940044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940044 prefixEnd_4940044 := by exact prefixLift 4940044
  have htrace : WordTrace (prefixWord ++ tailWord_4940044) baseStart_4940044 baseEnd_4940044 := by
    simpa [prefixWord, tailWord_4940044, baseEnd_4940044] using wordTrace_append hprefix tailTrace_4940044
  have hstable : (prefixWord ++ tailWord_4940044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940044).length < 2 ^ (prefixWord ++ tailWord_4940044).sum := by decide
  have hdescent : baseEnd_4940044 < baseStart_4940044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940065 : List Nat := [1, 2, 3, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_4940065 : Nat := 118140960795 + 4940065 * 2 ^ 59
def prefixEnd_4940065 : Nat := 4983230072969 + 3 ^ 40 * 4940065 * 2
def baseEnd_4940065 : Nat := 2536627809453319706668561

theorem tailTrace_4940065 : CollatzResearch.WordTrace tailWord_4940065 prefixEnd_4940065 2536627809453319706668561 := by
  unfold tailWord_4940065
  simp only [CollatzResearch.WordTrace]
  refine ⟨180178972847995675777045649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120119315231997117184697099 180178972847995675777045649)
  ·
    refine ⟨135134229635996756832784237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180178972847995675777045649 135134229635996756832784237)
    ·
      refine ⟨50675336113498783812294089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135134229635996756832784237 50675336113498783812294089)
      ·
        refine ⟨38006502085124087859220567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50675336113498783812294089 38006502085124087859220567)
        ·
          refine ⟨57009753127686131788830851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38006502085124087859220567 57009753127686131788830851)
          ·
            refine ⟨85514629691529197683246277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57009753127686131788830851 85514629691529197683246277)
            ·
              refine ⟨16033993067161724565608677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85514629691529197683246277 16033993067161724565608677)
              ·
                refine ⟨3006373700092823356051627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16033993067161724565608677 3006373700092823356051627)
                ·
                  refine ⟨4509560550139235034077441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006373700092823356051627 4509560550139235034077441)
                  ·
                    refine ⟨3382170412604426275558081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4509560550139235034077441 3382170412604426275558081)
                    ·
                      refine ⟨2536627809453319706668561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3382170412604426275558081 2536627809453319706668561)
                      ·
                        rfl

theorem cell23_4940065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_4940065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940065 prefixEnd_4940065 := by exact prefixLift 4940065
  have htrace : WordTrace (prefixWord ++ tailWord_4940065) baseStart_4940065 baseEnd_4940065 := by
    simpa [prefixWord, tailWord_4940065, baseEnd_4940065] using wordTrace_append hprefix tailTrace_4940065
  have hstable : (prefixWord ++ tailWord_4940065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940065).length < 2 ^ (prefixWord ++ tailWord_4940065).sum := by decide
  have hdescent : baseEnd_4940065 < baseStart_4940065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940078 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4940078 : Nat := 118140960795 + 4940078 * 2 ^ 59
def prefixEnd_4940078 : Nat := 4983230072969 + 3 ^ 40 * 4940078 * 2
def baseEnd_4940078 : Nat := 2536634484701828155806001

theorem tailTrace_4940078 : CollatzResearch.WordTrace tailWord_4940078 prefixEnd_4940078 2536634484701828155806001 := by
  unfold tailWord_4940078
  simp only [CollatzResearch.WordTrace]
  refine ⟨22522430874618572374658611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120119631331299052664845925 22522430874618572374658611)
  ·
    refine ⟨33783646311927858561987917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22522430874618572374658611 33783646311927858561987917)
    ·
      refine ⟨12668867366972946960745469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33783646311927858561987917 12668867366972946960745469)
      ·
        refine ⟨4750825262614855110279551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12668867366972946960745469 4750825262614855110279551)
        ·
          refine ⟨7126237893922282665419327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750825262614855110279551 7126237893922282665419327)
          ·
            refine ⟨10689356840883423998128991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7126237893922282665419327 10689356840883423998128991)
            ·
              refine ⟨16034035261325135997193487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10689356840883423998128991 16034035261325135997193487)
              ·
                refine ⟨24051052891987703995790231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16034035261325135997193487 24051052891987703995790231)
                ·
                  refine ⟨36076579337981555993685347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24051052891987703995790231 36076579337981555993685347)
                  ·
                    refine ⟨54114869006972333990528021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36076579337981555993685347 54114869006972333990528021)
                    ·
                      refine ⟨2536634484701828155806001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54114869006972333990528021 2536634484701828155806001)
                      ·
                        rfl

theorem cell23_4940078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4940078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940078 prefixEnd_4940078 := by exact prefixLift 4940078
  have htrace : WordTrace (prefixWord ++ tailWord_4940078) baseStart_4940078 baseEnd_4940078 := by
    simpa [prefixWord, tailWord_4940078, baseEnd_4940078] using wordTrace_append hprefix tailTrace_4940078
  have hstable : (prefixWord ++ tailWord_4940078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940078).length < 2 ^ (prefixWord ++ tailWord_4940078).sum := by decide
  have hdescent : baseEnd_4940078 < baseStart_4940078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940108 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 1, 3, 2]
def baseStart_4940108 : Nat := 118140960795 + 4940108 * 2 ^ 59
def prefixEnd_4940108 : Nat := 4983230072969 + 3 ^ 40 * 4940108 * 2
def baseEnd_4940108 : Nat := 2536649889121463038430863

theorem tailTrace_4940108 : CollatzResearch.WordTrace tailWord_4940108 prefixEnd_4940108 2536649889121463038430863 := by
  unfold tailWord_4940108
  simp only [CollatzResearch.WordTrace]
  refine ⟨90090270593419947060430489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120120360791226596080573985 90090270593419947060430489)
  ·
    refine ⟨67567702945064960295322867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90090270593419947060430489 67567702945064960295322867)
    ·
      refine ⟨101351554417597440442984301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67567702945064960295322867 101351554417597440442984301)
      ·
        refine ⟨38006832906599040166119113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101351554417597440442984301 38006832906599040166119113)
        ·
          refine ⟨28505124679949280124589335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38006832906599040166119113 28505124679949280124589335)
          ·
            refine ⟨42757687019923920186884003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28505124679949280124589335 42757687019923920186884003)
            ·
              refine ⟨64136530529885880280326005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42757687019923920186884003 64136530529885880280326005)
              ·
                refine ⟨6012799737176801276280563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64136530529885880280326005 6012799737176801276280563)
                ·
                  refine ⟨9019199605765201914420845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6012799737176801276280563 9019199605765201914420845)
                  ·
                    refine ⟨3382199852161950717907817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9019199605765201914420845 3382199852161950717907817)
                    ·
                      refine ⟨2536649889121463038430863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3382199852161950717907817 2536649889121463038430863)
                      ·
                        rfl

theorem cell23_4940108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_4940108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940108 prefixEnd_4940108 := by exact prefixLift 4940108
  have htrace : WordTrace (prefixWord ++ tailWord_4940108) baseStart_4940108 baseEnd_4940108 := by
    simpa [prefixWord, tailWord_4940108, baseEnd_4940108] using wordTrace_append hprefix tailTrace_4940108
  have hstable : (prefixWord ++ tailWord_4940108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940108).length < 2 ^ (prefixWord ++ tailWord_4940108).sum := by decide
  have hdescent : baseEnd_4940108 < baseStart_4940108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940114 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_4940114 : Nat := 118140960795 + 4940114 * 2 ^ 59
def prefixEnd_4940114 : Nat := 4983230072969 + 3 ^ 40 * 4940114 * 2
def baseEnd_4940114 : Nat := 845550990001796671651945

theorem tailTrace_4940114 : CollatzResearch.WordTrace tailWord_4940114 prefixEnd_4940114 845550990001796671651945 := by
  unfold tailWord_4940114
  simp only [CollatzResearch.WordTrace]
  refine ⟨45045190006204539286394849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120120506683212104763719597 45045190006204539286394849)
  ·
    refine ⟨33783892504653404464796137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45045190006204539286394849 33783892504653404464796137)
    ·
      refine ⟨25337919378490053348597103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33783892504653404464796137 25337919378490053348597103)
      ·
        refine ⟨38006879067735080022895655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25337919378490053348597103 38006879067735080022895655)
        ·
          refine ⟨57010318601602620034343483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38006879067735080022895655 57010318601602620034343483)
          ·
            refine ⟨85515477902403930051515225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57010318601602620034343483 85515477902403930051515225)
            ·
              refine ⟨64136608426802947538636419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85515477902403930051515225 64136608426802947538636419)
              ·
                refine ⟨96204912640204421307954629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64136608426802947538636419 96204912640204421307954629)
                ·
                  refine ⟨18038421120038328995241493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96204912640204421307954629 18038421120038328995241493)
                  ·
                    refine ⟨845550990001796671651945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18038421120038328995241493 845550990001796671651945)
                    ·
                      rfl

theorem cell23_4940114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_4940114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940114 prefixEnd_4940114 := by exact prefixLift 4940114
  have htrace : WordTrace (prefixWord ++ tailWord_4940114) baseStart_4940114 baseEnd_4940114 := by
    simpa [prefixWord, tailWord_4940114, baseEnd_4940114] using wordTrace_append hprefix tailTrace_4940114
  have hstable : (prefixWord ++ tailWord_4940114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940114).length < 2 ^ (prefixWord ++ tailWord_4940114).sum := by decide
  have hdescent : baseEnd_4940114 < baseStart_4940114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940182 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4940182 : Nat := 118140960795 + 4940182 * 2 ^ 59
def prefixEnd_4940182 : Nat := 4983230072969 + 3 ^ 40 * 4940182 * 2
def baseEnd_4940182 : Nat := 845562628896631916301841

theorem tailTrace_4940182 : CollatzResearch.WordTrace tailWord_4940182 prefixEnd_4940182 845562628896631916301841 := by
  unfold tailWord_4940182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11261452511785737797440925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120122160125714536506036533 11261452511785737797440925)
  ·
    refine ⟨4223044691919651674040347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11261452511785737797440925 4223044691919651674040347)
    ·
      refine ⟨6334567037879477511060521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4223044691919651674040347 6334567037879477511060521)
      ·
        refine ⟨4750925278409608133295391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6334567037879477511060521 4750925278409608133295391)
        ·
          refine ⟨7126387917614412199943087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750925278409608133295391 7126387917614412199943087)
          ·
            refine ⟨10689581876421618299914631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7126387917614412199943087 10689581876421618299914631)
            ·
              refine ⟨16034372814632427449871947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10689581876421618299914631 16034372814632427449871947)
              ·
                refine ⟨24051559221948641174807921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16034372814632427449871947 24051559221948641174807921)
                ·
                  refine ⟨18038669416461480881105941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24051559221948641174807921 18038669416461480881105941)
                  ·
                    refine ⟨845562628896631916301841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18038669416461480881105941 845562628896631916301841)
                    ·
                      rfl

theorem cell23_4940182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4940182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940182 prefixEnd_4940182 := by exact prefixLift 4940182
  have htrace : WordTrace (prefixWord ++ tailWord_4940182) baseStart_4940182 baseEnd_4940182 := by
    simpa [prefixWord, tailWord_4940182, baseEnd_4940182] using wordTrace_append hprefix tailTrace_4940182
  have hstable : (prefixWord ++ tailWord_4940182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940182).length < 2 ^ (prefixWord ++ tailWord_4940182).sum := by decide
  have hdescent : baseEnd_4940182 < baseStart_4940182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940328 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 3, 6]
def baseStart_4940328 : Nat := 118140960795 + 4940328 * 2 ^ 59
def prefixEnd_4940328 : Nat := 4983230072969 + 3 ^ 40 * 4940328 * 2
def baseEnd_4940328 : Nat := 845587618288484059226617

theorem tailTrace_4940328 : CollatzResearch.WordTrace tailWord_4940328 prefixEnd_4940328 845587618288484059226617 := by
  unfold tailWord_4940328
  simp only [CollatzResearch.WordTrace]
  refine ⟨90094282623021435846934819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120125710164028581129246425 90094282623021435846934819)
  ·
    refine ⟨135141423934532153770402229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90094282623021435846934819 135141423934532153770402229)
    ·
      refine ⟨12669508493862389415975209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135141423934532153770402229 12669508493862389415975209)
      ·
        refine ⟨9502131370396792061981407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12669508493862389415975209 9502131370396792061981407)
        ·
          refine ⟨14253197055595188092972111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9502131370396792061981407 14253197055595188092972111)
          ·
            refine ⟨21379795583392782139458167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14253197055595188092972111 21379795583392782139458167)
            ·
              refine ⟨32069693375089173209187251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21379795583392782139458167 32069693375089173209187251)
              ·
                refine ⟨48104540062633759813780877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32069693375089173209187251 48104540062633759813780877)
                ·
                  refine ⟨18039202523487659930167829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48104540062633759813780877 18039202523487659930167829)
                  ·
                    refine ⟨845587618288484059226617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18039202523487659930167829 845587618288484059226617)
                    ·
                      rfl

theorem cell23_4940328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_4940328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940328 prefixEnd_4940328 := by exact prefixLift 4940328
  have htrace : WordTrace (prefixWord ++ tailWord_4940328) baseStart_4940328 baseEnd_4940328 := by
    simpa [prefixWord, tailWord_4940328, baseEnd_4940328] using wordTrace_append hprefix tailTrace_4940328
  have hstable : (prefixWord ++ tailWord_4940328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940328).length < 2 ^ (prefixWord ++ tailWord_4940328).sum := by decide
  have hdescent : baseEnd_4940328 < baseStart_4940328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940338 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_4940338 : Nat := 118140960795 + 4940338 * 2 ^ 59
def prefixEnd_4940338 : Nat := 4983230072969 + 3 ^ 40 * 4940338 * 2
def baseEnd_4940338 : Nat := 2536767989671997138554805

theorem tailTrace_4940338 : CollatzResearch.WordTrace tailWord_4940338 prefixEnd_4940338 2536767989671997138554805 := by
  unfold tailWord_4940338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45047232494001660850433417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120125953317337762267822445 45047232494001660850433417)
  ·
    refine ⟨33785424370501245637825063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45047232494001660850433417 33785424370501245637825063)
    ·
      refine ⟨50678136555751868456737595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33785424370501245637825063 50678136555751868456737595)
      ·
        refine ⟨76017204833627802685106393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50678136555751868456737595 76017204833627802685106393)
        ·
          refine ⟨57012903625220852013829795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76017204833627802685106393 57012903625220852013829795)
          ·
            refine ⟨85519355437831278020744693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57012903625220852013829795 85519355437831278020744693)
            ·
              refine ⟨8017439572296682314444815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85519355437831278020744693 8017439572296682314444815)
              ·
                refine ⟨12026159358445023471667223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8017439572296682314444815 12026159358445023471667223)
                ·
                  refine ⟨18039239037667535207500835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12026159358445023471667223 18039239037667535207500835)
                  ·
                    refine ⟨27058858556501302811251253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18039239037667535207500835 27058858556501302811251253)
                    ·
                      refine ⟨2536767989671997138554805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27058858556501302811251253 2536767989671997138554805)
                      ·
                        rfl

theorem cell23_4940338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_4940338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940338 prefixEnd_4940338 := by exact prefixLift 4940338
  have htrace : WordTrace (prefixWord ++ tailWord_4940338) baseStart_4940338 baseEnd_4940338 := by
    simpa [prefixWord, tailWord_4940338, baseEnd_4940338] using wordTrace_append hprefix tailTrace_4940338
  have hstable : (prefixWord ++ tailWord_4940338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940338).length < 2 ^ (prefixWord ++ tailWord_4940338).sum := by decide
  have hdescent : baseEnd_4940338 < baseStart_4940338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940345 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 2, 4]
def baseStart_4940345 : Nat := 118140960795 + 4940345 * 2 ^ 59
def prefixEnd_4940345 : Nat := 4983230072969 + 3 ^ 40 * 4940345 * 2
def baseEnd_4940345 : Nat := 845590528012192870389091

theorem tailTrace_4940345 : CollatzResearch.WordTrace tailWord_4940345 prefixEnd_4940345 845590528012192870389091 := by
  unfold tailWord_4940345
  simp only [CollatzResearch.WordTrace]
  refine ⟨180189185286981283597238489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120126123524654189064825659 180189185286981283597238489)
  ·
    refine ⟨135141888965235962697928867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180189185286981283597238489 135141888965235962697928867)
    ·
      refine ⟨202712833447853944046893301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135141888965235962697928867 202712833447853944046893301)
      ·
        refine ⟨19004328135736307254396247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202712833447853944046893301 19004328135736307254396247)
        ·
          refine ⟨28506492203604460881594371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19004328135736307254396247 28506492203604460881594371)
          ·
            refine ⟨42759738305406691322391557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28506492203604460881594371 42759738305406691322391557)
            ·
              refine ⟨8017450932263754622948417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42759738305406691322391557 8017450932263754622948417)
              ·
                refine ⟨6013088199197815967211313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8017450932263754622948417 6013088199197815967211313)
                ·
                  refine ⟨4509816149398361975408485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6013088199197815967211313 4509816149398361975408485)
                  ·
                    refine ⟨845590528012192870389091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4509816149398361975408485 845590528012192870389091)
                    ·
                      rfl

theorem cell23_4940345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 4].length) (baseStart_4940345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940345 prefixEnd_4940345 := by exact prefixLift 4940345
  have htrace : WordTrace (prefixWord ++ tailWord_4940345) baseStart_4940345 baseEnd_4940345 := by
    simpa [prefixWord, tailWord_4940345, baseEnd_4940345] using wordTrace_append hprefix tailTrace_4940345
  have hstable : (prefixWord ++ tailWord_4940345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940345).length < 2 ^ (prefixWord ++ tailWord_4940345).sum := by decide
  have hdescent : baseEnd_4940345 < baseStart_4940345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940365 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4940365 : Nat := 118140960795 + 4940365 * 2 ^ 59
def prefixEnd_4940365 : Nat := 4983230072969 + 3 ^ 40 * 4940365 * 2
def baseEnd_4940365 : Nat := 2536781853649668532917181

theorem tailTrace_4940365 : CollatzResearch.WordTrace tailWord_4940365 prefixEnd_4940365 2536781853649668532917181 := by
  unfold tailWord_4940365
  simp only [CollatzResearch.WordTrace]
  refine ⟨180189914746908827012966549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120126609831272551341977699 180189914746908827012966549)
  ·
    refine ⟨8446402253761351266232807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 180189914746908827012966549 8446402253761351266232807)
    ·
      refine ⟨12669603380642026899349211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8446402253761351266232807 12669603380642026899349211)
      ·
        refine ⟨19004405070963040349023817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12669603380642026899349211 19004405070963040349023817)
        ·
          refine ⟨14253303803222280261767863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19004405070963040349023817 14253303803222280261767863)
          ·
            refine ⟨21379955704833420392651795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14253303803222280261767863 21379955704833420392651795)
            ·
              refine ⟨32069933557250130588977693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21379955704833420392651795 32069933557250130588977693)
              ·
                refine ⟨12026225083968798970866635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32069933557250130588977693 12026225083968798970866635)
                ·
                  refine ⟨18039337625953198456299953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12026225083968798970866635 18039337625953198456299953)
                  ·
                    refine ⟨13529503219464898842224965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18039337625953198456299953 13529503219464898842224965)
                    ·
                      refine ⟨2536781853649668532917181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13529503219464898842224965 2536781853649668532917181)
                      ·
                        rfl

theorem cell23_4940365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4940365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940365 prefixEnd_4940365 := by exact prefixLift 4940365
  have htrace : WordTrace (prefixWord ++ tailWord_4940365) baseStart_4940365 baseEnd_4940365 := by
    simpa [prefixWord, tailWord_4940365, baseEnd_4940365] using wordTrace_append hprefix tailTrace_4940365
  have hstable : (prefixWord ++ tailWord_4940365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940365).length < 2 ^ (prefixWord ++ tailWord_4940365).sum := by decide
  have hdescent : baseEnd_4940365 < baseStart_4940365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940386 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4940386 : Nat := 118140960795 + 4940386 * 2 ^ 59
def prefixEnd_4940386 : Nat := 4983230072969 + 3 ^ 40 * 4940386 * 2
def baseEnd_4940386 : Nat := 2536792636743412950754585

theorem tailTrace_4940386 : CollatzResearch.WordTrace tailWord_4940386 prefixEnd_4940386 2536792636743412950754585 := by
  unfold tailWord_4940386
  simp only [CollatzResearch.WordTrace]
  refine ⟨45047670169958186899870253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120127120453221831732987341 45047670169958186899870253)
  ·
    refine ⟨16892876313734320087451345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45047670169958186899870253 16892876313734320087451345)
    ·
      refine ⟨12669657235300740065588509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16892876313734320087451345 12669657235300740065588509)
      ·
        refine ⟨4751121463237777524595691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12669657235300740065588509 4751121463237777524595691)
        ·
          refine ⟨7126682194856666286893537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4751121463237777524595691 7126682194856666286893537)
          ·
            refine ⟨5345011646142499715170153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7126682194856666286893537 5345011646142499715170153)
            ·
              refine ⟨4008758734606874786377615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5345011646142499715170153 4008758734606874786377615)
              ·
                refine ⟨6013138101910312179566423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4008758734606874786377615 6013138101910312179566423)
                ·
                  refine ⟨9019707152865468269349635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6013138101910312179566423 9019707152865468269349635)
                  ·
                    refine ⟨13529560729298202404024453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9019707152865468269349635 13529560729298202404024453)
                    ·
                      refine ⟨2536792636743412950754585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13529560729298202404024453 2536792636743412950754585)
                      ·
                        rfl

theorem cell23_4940386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4940386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940386 prefixEnd_4940386 := by exact prefixLift 4940386
  have htrace : WordTrace (prefixWord ++ tailWord_4940386) baseStart_4940386 baseEnd_4940386 := by
    simpa [prefixWord, tailWord_4940386, baseEnd_4940386] using wordTrace_append hprefix tailTrace_4940386
  have hstable : (prefixWord ++ tailWord_4940386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940386).length < 2 ^ (prefixWord ++ tailWord_4940386).sum := by decide
  have hdescent : baseEnd_4940386 < baseStart_4940386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940389 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 1, 2, 3]
def baseStart_4940389 : Nat := 118140960795 + 4940389 * 2 ^ 59
def prefixEnd_4940389 : Nat := 4983230072969 + 3 ^ 40 * 4940389 * 2
def baseEnd_4940389 : Nat := 2536794177185376439017071

theorem tailTrace_4940389 : CollatzResearch.WordTrace tailWord_4940389 prefixEnd_4940389 2536794177185376439017071 := by
  unfold tailWord_4940389
  simp only [CollatzResearch.WordTrace]
  refine ⟨180190790098821879111840221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120127193399214586074560147 180190790098821879111840221)
  ·
    refine ⟨67571546287058204666940083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180190790098821879111840221 67571546287058204666940083)
    ·
      refine ⟨101357319430587307000410125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67571546287058204666940083 101357319430587307000410125)
      ·
        refine ⟨38008994786470240125153797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101357319430587307000410125 38008994786470240125153797)
        ·
          refine ⟨7126686522463170023466337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38008994786470240125153797 7126686522463170023466337)
          ·
            refine ⟨5345014891847377517599753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7126686522463170023466337 5345014891847377517599753)
            ·
              refine ⟨4008761168885533138199815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5345014891847377517599753 4008761168885533138199815)
              ·
                refine ⟨6013141753328299707299723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4008761168885533138199815 6013141753328299707299723)
                ·
                  refine ⟨9019712629992449560949585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6013141753328299707299723 9019712629992449560949585)
                  ·
                    refine ⟨6764784472494337170712189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9019712629992449560949585 6764784472494337170712189)
                    ·
                      refine ⟨2536794177185376439017071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6764784472494337170712189 2536794177185376439017071)
                      ·
                        rfl

theorem cell23_4940389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_4940389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940389 prefixEnd_4940389 := by exact prefixLift 4940389
  have htrace : WordTrace (prefixWord ++ tailWord_4940389) baseStart_4940389 baseEnd_4940389 := by
    simpa [prefixWord, tailWord_4940389, baseEnd_4940389] using wordTrace_append hprefix tailTrace_4940389
  have hstable : (prefixWord ++ tailWord_4940389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940389).length < 2 ^ (prefixWord ++ tailWord_4940389).sum := by decide
  have hdescent : baseEnd_4940389 < baseStart_4940389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940402 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_4940402 : Nat := 118140960795 + 4940402 * 2 ^ 59
def prefixEnd_4940402 : Nat := 4983230072969 + 3 ^ 40 * 4940402 * 2
def baseEnd_4940402 : Nat := 2536800852433884888154511

theorem tailTrace_4940402 : CollatzResearch.WordTrace tailWord_4940402 prefixEnd_4940402 2536800852433884888154511 := by
  unfold tailWord_4940402
  simp only [CollatzResearch.WordTrace]
  refine ⟨45047816061943695583015865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120127509498516521554708973 45047816061943695583015865)
  ·
    refine ⟨33785862046457771687261899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45047816061943695583015865 33785862046457771687261899)
    ·
      refine ⟨50678793069686657530892849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33785862046457771687261899 50678793069686657530892849)
      ·
        refine ⟨38009094802264993148169637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50678793069686657530892849 38009094802264993148169637)
        ·
          refine ⟨7126705275424686215281807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38009094802264993148169637 7126705275424686215281807)
          ·
            refine ⟨10690057913137029322922711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7126705275424686215281807 10690057913137029322922711)
            ·
              refine ⟨16035086869705543984384067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10690057913137029322922711 16035086869705543984384067)
              ·
                refine ⟨24052630304558315976576101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16035086869705543984384067 24052630304558315976576101)
                ·
                  refine ⟨4509868182104684245608019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24052630304558315976576101 4509868182104684245608019)
                  ·
                    refine ⟨6764802273157026368412029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4509868182104684245608019 6764802273157026368412029)
                    ·
                      refine ⟨2536800852433884888154511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6764802273157026368412029 2536800852433884888154511)
                      ·
                        rfl

theorem cell23_4940402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_4940402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940402 prefixEnd_4940402 := by exact prefixLift 4940402
  have htrace : WordTrace (prefixWord ++ tailWord_4940402) baseStart_4940402 baseEnd_4940402 := by
    simpa [prefixWord, tailWord_4940402, baseEnd_4940402] using wordTrace_append hprefix tailTrace_4940402
  have hstable : (prefixWord ++ tailWord_4940402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940402).length < 2 ^ (prefixWord ++ tailWord_4940402).sum := by decide
  have hdescent : baseEnd_4940402 < baseStart_4940402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940411 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 5]
def baseStart_4940411 : Nat := 118140960795 + 4940411 * 2 ^ 59
def prefixEnd_4940411 : Nat := 4983230072969 + 3 ^ 40 * 4940411 * 2
def baseEnd_4940411 : Nat := 2536805473759775352941969

theorem tailTrace_4940411 : CollatzResearch.WordTrace tailWord_4940411 prefixEnd_4940411 2536805473759775352941969 := by
  unfold tailWord_4940411
  simp only [CollatzResearch.WordTrace]
  refine ⟨180191592504742176869141087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120127728336494784579427391 180191592504742176869141087)
  ·
    refine ⟨270287388757113265303711631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180191592504742176869141087 270287388757113265303711631)
    ·
      refine ⟨405431083135669897955567447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270287388757113265303711631 405431083135669897955567447)
      ·
        refine ⟨608146624703504846933351171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405431083135669897955567447 608146624703504846933351171)
        ·
          refine ⟨912219937055257270400026757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608146624703504846933351171 912219937055257270400026757)
          ·
            refine ⟨171041238197860738200005017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 912219937055257270400026757 171041238197860738200005017)
            ·
              refine ⟨128280928648395553650003763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171041238197860738200005017 128280928648395553650003763)
              ·
                refine ⟨192421392972593330475005645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128280928648395553650003763 192421392972593330475005645)
                ·
                  refine ⟨72158022364722498928127117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192421392972593330475005645 72158022364722498928127117)
                  ·
                    refine ⟨27059258386770937098047669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72158022364722498928127117 27059258386770937098047669)
                    ·
                      refine ⟨2536805473759775352941969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27059258386770937098047669 2536805473759775352941969)
                      ·
                        rfl

theorem cell23_4940411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_4940411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940411 prefixEnd_4940411 := by exact prefixLift 4940411
  have htrace : WordTrace (prefixWord ++ tailWord_4940411) baseStart_4940411 baseEnd_4940411 := by
    simpa [prefixWord, tailWord_4940411, baseEnd_4940411] using wordTrace_append hprefix tailTrace_4940411
  have hstable : (prefixWord ++ tailWord_4940411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940411).length < 2 ^ (prefixWord ++ tailWord_4940411).sum := by decide
  have hdescent : baseEnd_4940411 < baseStart_4940411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940470 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_4940470 : Nat := 118140960795 + 4940470 * 2 ^ 59
def prefixEnd_4940470 : Nat := 4983230072969 + 3 ^ 40 * 4940470 * 2
def baseEnd_4940470 : Nat := 2536835769118390622104199

theorem tailTrace_4940470 : CollatzResearch.WordTrace tailWord_4940470 prefixEnd_4940470 2536835769118390622104199 := by
  unfold tailWord_4940470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262109025720526871596179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120129162941018953297025909 11262109025720526871596179)
  ·
    refine ⟨16893163538580790307394269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11262109025720526871596179 16893163538580790307394269)
    ·
      refine ⟨6334936326967796365272851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16893163538580790307394269 6334936326967796365272851)
      ·
        refine ⟨9502404490451694547909277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6334936326967796365272851 9502404490451694547909277)
        ·
          refine ⟨3563401683919385455465979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9502404490451694547909277 3563401683919385455465979)
          ·
            refine ⟨5345102525879078183198969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563401683919385455465979 5345102525879078183198969)
            ·
              refine ⟨4008826894409308637399227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5345102525879078183198969 4008826894409308637399227)
              ·
                refine ⟨6013240341613962956098841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4008826894409308637399227 6013240341613962956098841)
                ·
                  refine ⟨4509930256210472217074131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6013240341613962956098841 4509930256210472217074131)
                  ·
                    refine ⟨6764895384315708325611197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4509930256210472217074131 6764895384315708325611197)
                    ·
                      refine ⟨2536835769118390622104199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6764895384315708325611197 2536835769118390622104199)
                      ·
                        rfl

theorem cell23_4940470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_4940470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940470 prefixEnd_4940470 := by exact prefixLift 4940470
  have htrace : WordTrace (prefixWord ++ tailWord_4940470) baseStart_4940470 baseEnd_4940470 := by
    simpa [prefixWord, tailWord_4940470, baseEnd_4940470] using wordTrace_append hprefix tailTrace_4940470
  have hstable : (prefixWord ++ tailWord_4940470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940470).length < 2 ^ (prefixWord ++ tailWord_4940470).sum := by decide
  have hdescent : baseEnd_4940470 < baseStart_4940470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940542 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4940542 : Nat := 118140960795 + 4940542 * 2 ^ 59
def prefixEnd_4940542 : Nat := 4983230072969 + 3 ^ 40 * 4940542 * 2
def baseEnd_4940542 : Nat := 845624246575171446801289

theorem tailTrace_4940542 : CollatzResearch.WordTrace tailWord_4940542 prefixEnd_4940542 845624246575171446801289 := by
  unfold tailWord_4940542
  simp only [CollatzResearch.WordTrace]
  refine ⟨22524546308408448280269985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120130913644845057494773253 22524546308408448280269985)
  ·
    refine ⟨16893409731306336210202489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22524546308408448280269985 16893409731306336210202489)
    ·
      refine ⟨12670057298479752157651867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16893409731306336210202489 12670057298479752157651867)
      ·
        refine ⟨19005085947719628236477801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12670057298479752157651867 19005085947719628236477801)
        ·
          refine ⟨14253814460789721177358351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19005085947719628236477801 14253814460789721177358351)
          ·
            refine ⟨21380721691184581766037527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14253814460789721177358351 21380721691184581766037527)
            ·
              refine ⟨32071082536776872649056291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21380721691184581766037527 32071082536776872649056291)
              ·
                refine ⟨48106623805165308973584437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32071082536776872649056291 48106623805165308973584437)
                ·
                  refine ⟨4509995981734247716273541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48106623805165308973584437 4509995981734247716273541)
                  ·
                    refine ⟨845624246575171446801289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4509995981734247716273541 845624246575171446801289)
                    ·
                      rfl

theorem cell23_4940542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4940542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940542 prefixEnd_4940542 := by exact prefixLift 4940542
  have htrace : WordTrace (prefixWord ++ tailWord_4940542) baseStart_4940542 baseEnd_4940542 := by
    simpa [prefixWord, tailWord_4940542, baseEnd_4940542] using wordTrace_append hprefix tailTrace_4940542
  have hstable : (prefixWord ++ tailWord_4940542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940542).length < 2 ^ (prefixWord ++ tailWord_4940542).sum := by decide
  have hdescent : baseEnd_4940542 < baseStart_4940542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940552 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_4940552 : Nat := 118140960795 + 4940552 * 2 ^ 59
def prefixEnd_4940552 : Nat := 4983230072969 + 3 ^ 40 * 4940552 * 2
def baseEnd_4940552 : Nat := 2536877874532059301278821

theorem tailTrace_4940552 : CollatzResearch.WordTrace tailWord_4940552 prefixEnd_4940552 2536877874532059301278821 := by
  unfold tailWord_4940552
  simp only [CollatzResearch.WordTrace]
  refine ⟨90098367598615678975011955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120131156798154238633349273 90098367598615678975011955)
  ·
    refine ⟨135147551397923518462517933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90098367598615678975011955 135147551397923518462517933)
    ·
      refine ⟨50680331774221319423444225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135147551397923518462517933 50680331774221319423444225)
      ·
        refine ⟨38010248830665989567583169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50680331774221319423444225 38010248830665989567583169)
        ·
          refine ⟨28507686622999492175687377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38010248830665989567583169 28507686622999492175687377)
          ·
            refine ⟨21380764967249619131765533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28507686622999492175687377 21380764967249619131765533)
            ·
              refine ⟨8017786862718607174412075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21380764967249619131765533 8017786862718607174412075)
              ·
                refine ⟨12026680294077910761618113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8017786862718607174412075 12026680294077910761618113)
                ·
                  refine ⟨9020010220558433071213585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12026680294077910761618113 9020010220558433071213585)
                  ·
                    refine ⟨6765007665418824803410189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9020010220558433071213585 6765007665418824803410189)
                    ·
                      refine ⟨2536877874532059301278821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6765007665418824803410189 2536877874532059301278821)
                      ·
                        rfl

theorem cell23_4940552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_4940552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940552 prefixEnd_4940552 := by exact prefixLift 4940552
  have htrace : WordTrace (prefixWord ++ tailWord_4940552) baseStart_4940552 baseEnd_4940552 := by
    simpa [prefixWord, tailWord_4940552, baseEnd_4940552] using wordTrace_append hprefix tailTrace_4940552
  have hstable : (prefixWord ++ tailWord_4940552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940552).length < 2 ^ (prefixWord ++ tailWord_4940552).sum := by decide
  have hdescent : baseEnd_4940552 < baseStart_4940552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940572 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 6]
def baseStart_4940572 : Nat := 118140960795 + 4940572 * 2 ^ 59
def prefixEnd_4940572 : Nat := 4983230072969 + 3 ^ 40 * 4940572 * 2
def baseEnd_4940572 : Nat := 281876460460572135892081

theorem tailTrace_4940572 : CollatzResearch.WordTrace tailWord_4940572 prefixEnd_4940572 281876460460572135892081 := by
  unfold tailWord_4940572
  simp only [CollatzResearch.WordTrace]
  refine ⟨90098732328579450682875985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120131643104772600910501313 90098732328579450682875985)
  ·
    refine ⟨67574049246434588012156989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90098732328579450682875985 67574049246434588012156989)
    ·
      refine ⟨25340268467412970504558871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67574049246434588012156989 25340268467412970504558871)
      ·
        refine ⟨38010402701119455756838307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25340268467412970504558871 38010402701119455756838307)
        ·
          refine ⟨57015604051679183635257461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38010402701119455756838307 57015604051679183635257461)
          ·
            refine ⟨5345212879844923465805387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57015604051679183635257461 5345212879844923465805387)
            ·
              refine ⟨8017819319767385198708081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345212879844923465805387 8017819319767385198708081)
              ·
                refine ⟨6013364489825538899031061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8017819319767385198708081 6013364489825538899031061)
                ·
                  refine ⟨281876460460572135892081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6013364489825538899031061 281876460460572135892081)
                  ·
                    rfl

theorem cell23_4940572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_4940572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940572 prefixEnd_4940572 := by exact prefixLift 4940572
  have htrace : WordTrace (prefixWord ++ tailWord_4940572) baseStart_4940572 baseEnd_4940572 := by
    simpa [prefixWord, tailWord_4940572, baseEnd_4940572] using wordTrace_append hprefix tailTrace_4940572
  have hstable : (prefixWord ++ tailWord_4940572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940572).length < 2 ^ (prefixWord ++ tailWord_4940572).sum := by decide
  have hdescent : baseEnd_4940572 < baseStart_4940572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940655 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 3]
def baseStart_4940655 : Nat := 118140960795 + 4940655 * 2 ^ 59
def prefixEnd_4940655 : Nat := 4983230072969 + 3 ^ 40 * 4940655 * 2
def baseEnd_4940655 : Nat := 2536930763039472398290847

theorem tailTrace_4940655 : CollatzResearch.WordTrace tailWord_4940655 prefixEnd_4940655 2536930763039472398290847 := by
  unfold tailWord_4940655
  simp only [CollatzResearch.WordTrace]
  refine ⟨180200491915858206541023419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120133661277238804360682279 180200491915858206541023419)
  ·
    refine ⟨270300737873787309811535129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180200491915858206541023419 270300737873787309811535129)
    ·
      refine ⟨202725553405340482358651347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270300737873787309811535129 202725553405340482358651347)
      ·
        refine ⟨304088330108010723537977021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202725553405340482358651347 304088330108010723537977021)
        ·
          refine ⟨114033123790504021326741383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304088330108010723537977021 114033123790504021326741383)
          ·
            refine ⟨171049685685756031990112075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114033123790504021326741383 171049685685756031990112075)
            ·
              refine ⟨256574528528634047985168113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171049685685756031990112075 256574528528634047985168113)
              ·
                refine ⟨192430896396475535988876085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256574528528634047985168113 192430896396475535988876085)
                ·
                  refine ⟨18040396537169581498957133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192430896396475535988876085 18040396537169581498957133)
                  ·
                    refine ⟨6765148701438593062108925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18040396537169581498957133 6765148701438593062108925)
                    ·
                      refine ⟨2536930763039472398290847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6765148701438593062108925 2536930763039472398290847)
                      ·
                        rfl

theorem cell23_4940655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_4940655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940655 prefixEnd_4940655 := by exact prefixLift 4940655
  have htrace : WordTrace (prefixWord ++ tailWord_4940655) baseStart_4940655 baseEnd_4940655 := by
    simpa [prefixWord, tailWord_4940655, baseEnd_4940655] using wordTrace_append hprefix tailTrace_4940655
  have hstable : (prefixWord ++ tailWord_4940655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940655).length < 2 ^ (prefixWord ++ tailWord_4940655).sum := by decide
  have hdescent : baseEnd_4940655 < baseStart_4940655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940662 : List Nat := [5, 1, 1, 3, 1, 1, 2, 9]
def baseStart_4940662 : Nat := 118140960795 + 4940662 * 2 ^ 59
def prefixEnd_4940662 : Nat := 4983230072969 + 3 ^ 40 * 4940662 * 2
def baseEnd_4940662 : Nat := 93960531755705698922345

theorem tailTrace_4940662 : CollatzResearch.WordTrace tailWord_4940662 prefixEnd_4940662 93960531755705698922345 := by
  unfold tailWord_4940662
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262546701677052921033015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120133831484555231157685493 11262546701677052921033015)
  ·
    refine ⟨16893820052515579381549523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11262546701677052921033015 16893820052515579381549523)
    ·
      refine ⟨25340730078773369072324285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16893820052515579381549523 25340730078773369072324285)
      ·
        refine ⟨9502773779540013402121607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25340730078773369072324285 9502773779540013402121607)
        ·
          refine ⟨14254160669310020103182411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9502773779540013402121607 14254160669310020103182411)
          ·
            refine ⟨21381241003965030154773617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14254160669310020103182411 21381241003965030154773617)
            ·
              refine ⟨16035930752973772616080213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21381241003965030154773617 16035930752973772616080213)
              ·
                refine ⟨93960531755705698922345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16035930752973772616080213 93960531755705698922345)
                ·
                  rfl

theorem cell23_4940662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_4940662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940662 prefixEnd_4940662 := by exact prefixLift 4940662
  have htrace : WordTrace (prefixWord ++ tailWord_4940662) baseStart_4940662 baseEnd_4940662 := by
    simpa [prefixWord, tailWord_4940662, baseEnd_4940662] using wordTrace_append hprefix tailTrace_4940662
  have hstable : (prefixWord ++ tailWord_4940662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940662).length < 2 ^ (prefixWord ++ tailWord_4940662).sum := by decide
  have hdescent : baseEnd_4940662 < baseStart_4940662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940672 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 4, 1, 3]
def baseStart_4940672 : Nat := 118140960795 + 4940672 * 2 ^ 59
def prefixEnd_4940672 : Nat := 4983230072969 + 3 ^ 40 * 4940672 * 2
def baseEnd_4940672 : Nat := 2536939492210598831778269

theorem tailTrace_4940672 : CollatzResearch.WordTrace tailWord_4940672 prefixEnd_4940672 2536939492210598831778269 := by
  unfold tailWord_4940672
  simp only [CollatzResearch.WordTrace]
  refine ⟨90100555978398309222196135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120134074637864412296261513 90100555978398309222196135)
  ·
    refine ⟨135150833967597463833294203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90100555978398309222196135 135150833967597463833294203)
    ·
      refine ⟨202726250951396195749941305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135150833967597463833294203 202726250951396195749941305)
      ·
        refine ⟨152044688213547146812455979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202726250951396195749941305 152044688213547146812455979)
        ·
          refine ⟨228067032320320720218683969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152044688213547146812455979 228067032320320720218683969)
          ·
            refine ⟨171050274240240540164012977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228067032320320720218683969 171050274240240540164012977)
            ·
              refine ⟨128287705680180405123009733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171050274240240540164012977 128287705680180405123009733)
              ·
                refine ⟨24053944815033825960564325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128287705680180405123009733 24053944815033825960564325)
                ·
                  refine ⟨4510114652818842367605811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24053944815033825960564325 4510114652818842367605811)
                  ·
                    refine ⟨6765171979228263551408717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4510114652818842367605811 6765171979228263551408717)
                    ·
                      refine ⟨2536939492210598831778269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6765171979228263551408717 2536939492210598831778269)
                      ·
                        rfl

theorem cell23_4940672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_4940672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940672 prefixEnd_4940672 := by exact prefixLift 4940672
  have htrace : WordTrace (prefixWord ++ tailWord_4940672) baseStart_4940672 baseEnd_4940672 := by
    simpa [prefixWord, tailWord_4940672, baseEnd_4940672] using wordTrace_append hprefix tailTrace_4940672
  have hstable : (prefixWord ++ tailWord_4940672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940672).length < 2 ^ (prefixWord ++ tailWord_4940672).sum := by decide
  have hdescent : baseEnd_4940672 < baseStart_4940672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940690 : List Nat := [3, 2, 3, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4940690 : Nat := 118140960795 + 4940690 * 2 ^ 59
def prefixEnd_4940690 : Nat := 4983230072969 + 3 ^ 40 * 4940690 * 2
def baseEnd_4940690 : Nat := 2536948734862379761353187

theorem tailTrace_4940690 : CollatzResearch.WordTrace tailWord_4940690 prefixEnd_4940690 2536948734862379761353187 := by
  unfold tailWord_4940690
  simp only [CollatzResearch.WordTrace]
  refine ⟨45050442117682851879636881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120134512313820938345698349 45050442117682851879636881)
  ·
    refine ⟨33787831588262138909727661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45050442117682851879636881 33787831588262138909727661)
    ·
      refine ⟨12670436845598302091147873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33787831588262138909727661 12670436845598302091147873)
      ·
        refine ⟨9502827634198726568360905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12670436845598302091147873 9502827634198726568360905)
        ·
          refine ⟨7127120725649044926270679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9502827634198726568360905 7127120725649044926270679)
          ·
            refine ⟨10690681088473567389406019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7127120725649044926270679 10690681088473567389406019)
            ·
              refine ⟨16036021632710351084109029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10690681088473567389406019 16036021632710351084109029)
              ·
                refine ⟨3006754056133190828270443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16036021632710351084109029 3006754056133190828270443)
                ·
                  refine ⟨4510131084199786242405665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006754056133190828270443 4510131084199786242405665)
                  ·
                    refine ⟨3382598313149839681804249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4510131084199786242405665 3382598313149839681804249)
                    ·
                      refine ⟨2536948734862379761353187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3382598313149839681804249 2536948734862379761353187)
                      ·
                        rfl

theorem cell23_4940690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4940690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940690 prefixEnd_4940690 := by exact prefixLift 4940690
  have htrace : WordTrace (prefixWord ++ tailWord_4940690) baseStart_4940690 baseEnd_4940690 := by
    simpa [prefixWord, tailWord_4940690, baseEnd_4940690] using wordTrace_append hprefix tailTrace_4940690
  have hstable : (prefixWord ++ tailWord_4940690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940690).length < 2 ^ (prefixWord ++ tailWord_4940690).sum := by decide
  have hdescent : baseEnd_4940690 < baseStart_4940690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940695 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4940695 : Nat := 118140960795 + 4940695 * 2 ^ 59
def prefixEnd_4940695 : Nat := 4983230072969 + 3 ^ 40 * 4940695 * 2
def baseEnd_4940695 : Nat := 2536951302265652241790663

theorem tailTrace_4940695 : CollatzResearch.WordTrace tailWord_4940695 prefixEnd_4940695 2536951302265652241790663 := by
  unfold tailWord_4940695
  simp only [CollatzResearch.WordTrace]
  refine ⟨180201950835713293372479539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120134633890475528914986359 180201950835713293372479539)
  ·
    refine ⟨270302926253569940058719309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180201950835713293372479539 270302926253569940058719309)
    ·
      refine ⟨101363597345088727522019741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270302926253569940058719309 101363597345088727522019741)
      ·
        refine ⟨38011349004408272820757403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101363597345088727522019741 38011349004408272820757403)
        ·
          refine ⟨57017023506612409231136105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38011349004408272820757403 57017023506612409231136105)
          ·
            refine ⟨42762767629959306923352079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57017023506612409231136105 42762767629959306923352079)
            ·
              refine ⟨64144151444938960385028119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42762767629959306923352079 64144151444938960385028119)
              ·
                refine ⟨96216227167408440577542179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64144151444938960385028119 96216227167408440577542179)
                ·
                  refine ⟨144324340751112660866313269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96216227167408440577542179 144324340751112660866313269)
                  ·
                    refine ⟨13530406945416811956216869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 144324340751112660866313269 13530406945416811956216869)
                    ·
                      refine ⟨2536951302265652241790663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13530406945416811956216869 2536951302265652241790663)
                      ·
                        rfl

theorem cell23_4940695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4940695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940695 prefixEnd_4940695 := by exact prefixLift 4940695
  have htrace : WordTrace (prefixWord ++ tailWord_4940695) baseStart_4940695 baseEnd_4940695 := by
    simpa [prefixWord, tailWord_4940695, baseEnd_4940695] using wordTrace_append hprefix tailTrace_4940695
  have hstable : (prefixWord ++ tailWord_4940695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940695).length < 2 ^ (prefixWord ++ tailWord_4940695).sum := by decide
  have hdescent : baseEnd_4940695 < baseStart_4940695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940706 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_4940706 : Nat := 118140960795 + 4940706 * 2 ^ 59
def prefixEnd_4940706 : Nat := 4983230072969 + 3 ^ 40 * 4940706 * 2
def baseEnd_4940706 : Nat := 2536956950552851698753113

theorem tailTrace_4940706 : CollatzResearch.WordTrace tailWord_4940706 prefixEnd_4940706 2536956950552851698753113 := by
  unfold tailWord_4940706
  simp only [CollatzResearch.WordTrace]
  refine ⟨45050588009668360562782493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120134901359115628167419981 45050588009668360562782493)
  ·
    refine ⟨16893970503625635211043435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45050588009668360562782493 16893970503625635211043435)
    ·
      refine ⟨25340955755438452816565153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16893970503625635211043435 25340955755438452816565153)
      ·
        refine ⟨19005716816578839612423865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25340955755438452816565153 19005716816578839612423865)
        ·
          refine ⟨14254287612434129709317899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19005716816578839612423865 14254287612434129709317899)
          ·
            refine ⟨21381431418651194563976849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14254287612434129709317899 21381431418651194563976849)
            ·
              refine ⟨16036073563988395922982637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21381431418651194563976849 16036073563988395922982637)
              ·
                refine ⟨6013527586495648471118489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16036073563988395922982637 6013527586495648471118489)
                ·
                  refine ⟨4510145689871736353338867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6013527586495648471118489 4510145689871736353338867)
                  ·
                    refine ⟨6765218534807604530008301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4510145689871736353338867 6765218534807604530008301)
                    ·
                      refine ⟨2536956950552851698753113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6765218534807604530008301 2536956950552851698753113)
                      ·
                        rfl

theorem cell23_4940706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_4940706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940706 prefixEnd_4940706 := by exact prefixLift 4940706
  have htrace : WordTrace (prefixWord ++ tailWord_4940706) baseStart_4940706 baseEnd_4940706 := by
    simpa [prefixWord, tailWord_4940706, baseEnd_4940706] using wordTrace_append hprefix tailTrace_4940706
  have hstable : (prefixWord ++ tailWord_4940706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940706).length < 2 ^ (prefixWord ++ tailWord_4940706).sum := by decide
  have hdescent : baseEnd_4940706 < baseStart_4940706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940729 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 1, 4, 2]
def baseStart_4940729 : Nat := 118140960795 + 4940729 * 2 ^ 59
def prefixEnd_4940729 : Nat := 4983230072969 + 3 ^ 40 * 4940729 * 2
def baseEnd_4940729 : Nat := 2536968760607905108765507

theorem tailTrace_4940729 : CollatzResearch.WordTrace tailWord_4940729 prefixEnd_4940729 2536968760607905108765507 := by
  unfold tailWord_4940729
  simp only [CollatzResearch.WordTrace]
  refine ⟨180203190917590117179217241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120135460611726744786144827 180203190917590117179217241)
  ·
    refine ⟨135152393188192587884412931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180203190917590117179217241 135152393188192587884412931)
    ·
      refine ⟨202728589782288881826619397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135152393188192587884412931 202728589782288881826619397)
      ·
        refine ⟨38011610584179165342491137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202728589782288881826619397 38011610584179165342491137)
        ·
          refine ⟨28508707938134374006868353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38011610584179165342491137 28508707938134374006868353)
          ·
            refine ⟨21381530953600780505151265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28508707938134374006868353 21381530953600780505151265)
            ·
              refine ⟨16036148215200585378863449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21381530953600780505151265 16036148215200585378863449)
              ·
                refine ⟨12027111161400439034147587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16036148215200585378863449 12027111161400439034147587)
                ·
                  refine ⟨18040666742100658551221381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12027111161400439034147587 18040666742100658551221381)
                  ·
                    refine ⟨3382625014143873478354009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18040666742100658551221381 3382625014143873478354009)
                    ·
                      refine ⟨2536968760607905108765507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3382625014143873478354009 2536968760607905108765507)
                      ·
                        rfl

theorem cell23_4940729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_4940729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940729 prefixEnd_4940729 := by exact prefixLift 4940729
  have htrace : WordTrace (prefixWord ++ tailWord_4940729) baseStart_4940729 baseEnd_4940729 := by
    simpa [prefixWord, tailWord_4940729, baseEnd_4940729] using wordTrace_append hprefix tailTrace_4940729
  have hstable : (prefixWord ++ tailWord_4940729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940729).length < 2 ^ (prefixWord ++ tailWord_4940729).sum := by decide
  have hdescent : baseEnd_4940729 < baseStart_4940729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940740 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4940740 : Nat := 118140960795 + 4940740 * 2 ^ 59
def prefixEnd_4940740 : Nat := 4983230072969 + 3 ^ 40 * 4940740 * 2
def baseEnd_4940740 : Nat := 2536974408895104565727957

theorem tailTrace_4940740 : CollatzResearch.WordTrace tailWord_4940740 prefixEnd_4940740 2536974408895104565727957 := by
  unfold tailWord_4940740
  simp only [CollatzResearch.WordTrace]
  refine ⟨90101796060275133028933837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120135728080366844038578449 90101796060275133028933837)
  ·
    refine ⟨33788173522603174885850189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90101796060275133028933837 33788173522603174885850189)
    ·
      refine ⟨12670565070976190582193821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33788173522603174885850189 12670565070976190582193821)
      ·
        refine ⟨4751461901616071468322683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12670565070976190582193821 4751461901616071468322683)
        ·
          refine ⟨7127192852424107202484025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4751461901616071468322683 7127192852424107202484025)
          ·
            refine ⟨5345394639318080401863019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7127192852424107202484025 5345394639318080401863019)
            ·
              refine ⟨8018091958977120602794529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345394639318080401863019 8018091958977120602794529)
              ·
                refine ⟨6013568969232840452095897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8018091958977120602794529 6013568969232840452095897)
                ·
                  refine ⟨4510176726924630339071923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6013568969232840452095897 4510176726924630339071923)
                  ·
                    refine ⟨6765265090386945508607885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4510176726924630339071923 6765265090386945508607885)
                    ·
                      refine ⟨2536974408895104565727957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6765265090386945508607885 2536974408895104565727957)
                      ·
                        rfl

theorem cell23_4940740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4940740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940740 prefixEnd_4940740 := by exact prefixLift 4940740
  have htrace : WordTrace (prefixWord ++ tailWord_4940740) baseStart_4940740 baseEnd_4940740 := by
    simpa [prefixWord, tailWord_4940740, baseEnd_4940740] using wordTrace_append hprefix tailTrace_4940740
  have hstable : (prefixWord ++ tailWord_4940740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940740).length < 2 ^ (prefixWord ++ tailWord_4940740).sum := by decide
  have hdescent : baseEnd_4940740 < baseStart_4940740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940836 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_4940836 : Nat := 118140960795 + 4940836 * 2 ^ 59
def prefixEnd_4940836 : Nat := 4983230072969 + 3 ^ 40 * 4940836 * 2
def baseEnd_4940836 : Nat := 2537023703037936190127515

theorem tailTrace_4940836 : CollatzResearch.WordTrace tailWord_4940836 prefixEnd_4940836 2537023703037936190127515 := by
  unfold tailWord_4940836
  simp only [CollatzResearch.WordTrace]
  refine ⟨90103546764101237226681181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120138062352134982968908241 90103546764101237226681181)
  ·
    refine ⟨33788830036537963960005443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90103546764101237226681181 33788830036537963960005443)
    ·
      refine ⟨50683245054806945940008165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33788830036537963960005443 50683245054806945940008165)
      ·
        refine ⟨9503108447776302363751531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50683245054806945940008165 9503108447776302363751531)
        ·
          refine ⟨14254662671664453545627297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9503108447776302363751531 14254662671664453545627297)
          ·
            refine ⟨10690997003748340159220473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14254662671664453545627297 10690997003748340159220473)
            ·
              refine ⟨8018247752811255119415355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10690997003748340159220473 8018247752811255119415355)
              ·
                refine ⟨12027371629216882679123033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8018247752811255119415355 12027371629216882679123033)
                ·
                  refine ⟨9020528721912662009342275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12027371629216882679123033 9020528721912662009342275)
                  ·
                    refine ⟨13530793082868993014013413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9020528721912662009342275 13530793082868993014013413)
                    ·
                      refine ⟨2537023703037936190127515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13530793082868993014013413 2537023703037936190127515)
                      ·
                        rfl

theorem cell23_4940836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_4940836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940836 prefixEnd_4940836 := by exact prefixLift 4940836
  have htrace : WordTrace (prefixWord ++ tailWord_4940836) baseStart_4940836 baseEnd_4940836 := by
    simpa [prefixWord, tailWord_4940836, baseEnd_4940836] using wordTrace_append hprefix tailTrace_4940836
  have hstable : (prefixWord ++ tailWord_4940836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940836).length < 2 ^ (prefixWord ++ tailWord_4940836).sum := by decide
  have hdescent : baseEnd_4940836 < baseStart_4940836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940872 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 5, 5]
def baseStart_4940872 : Nat := 118140960795 + 4940872 * 2 ^ 59
def prefixEnd_4940872 : Nat := 4983230072969 + 3 ^ 40 * 4940872 * 2
def baseEnd_4940872 : Nat := 845680729447166016425783

theorem tailTrace_4940872 : CollatzResearch.WordTrace tailWord_4940872 prefixEnd_4940872 845680729447166016425783 := by
  unfold tailWord_4940872
  simp only [CollatzResearch.WordTrace]
  refine ⟨90104203278036026300836435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120138937704048035067781913 90104203278036026300836435)
  ·
    refine ⟨135156304917054039451254653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90104203278036026300836435 135156304917054039451254653)
    ·
      refine ⟨50683614343895264794220495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135156304917054039451254653 50683614343895264794220495)
      ·
        refine ⟨76025421515842897191330743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50683614343895264794220495 76025421515842897191330743)
        ·
          refine ⟨114038132273764345786996115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76025421515842897191330743 114038132273764345786996115)
          ·
            refine ⟨171057198410646518680494173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114038132273764345786996115 171057198410646518680494173)
            ·
              refine ⟨64146449403992444505185315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171057198410646518680494173 64146449403992444505185315)
              ·
                refine ⟨96219674105988666757777973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64146449403992444505185315 96219674105988666757777973)
                ·
                  refine ⟨9020594447436437508541685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96219674105988666757777973 9020594447436437508541685)
                  ·
                    refine ⟨845680729447166016425783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9020594447436437508541685 845680729447166016425783)
                    ·
                      rfl

theorem cell23_4940872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_4940872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940872 prefixEnd_4940872 := by exact prefixLift 4940872
  have htrace : WordTrace (prefixWord ++ tailWord_4940872) baseStart_4940872 baseEnd_4940872 := by
    simpa [prefixWord, tailWord_4940872, baseEnd_4940872] using wordTrace_append hprefix tailTrace_4940872
  have hstable : (prefixWord ++ tailWord_4940872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940872).length < 2 ^ (prefixWord ++ tailWord_4940872).sum := by decide
  have hdescent : baseEnd_4940872 < baseStart_4940872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940903 : List Nat := [1, 1, 5, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_4940903 : Nat := 118140960795 + 4940903 * 2 ^ 59
def prefixEnd_4940903 : Nat := 4983230072969 + 3 ^ 40 * 4940903 * 2
def baseEnd_4940903 : Nat := 2537058106241787427989707

theorem tailTrace_4940903 : CollatzResearch.WordTrace tailWord_4940903 prefixEnd_4940903 2537058106241787427989707 := by
  unfold tailWord_4940903
  simp only [CollatzResearch.WordTrace]
  refine ⟨180209537218959744896051363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120139691479306496597367575 180209537218959744896051363)
  ·
    refine ⟨270314305828439617344077045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180209537218959744896051363 270314305828439617344077045)
    ·
      refine ⟨25341966171416214126007223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 270314305828439617344077045 25341966171416214126007223)
      ·
        refine ⟨38012949257124321189010835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25341966171416214126007223 38012949257124321189010835)
        ·
          refine ⟨57019423885686481783516253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38012949257124321189010835 57019423885686481783516253)
          ·
            refine ⟨21382283957132430668818595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57019423885686481783516253 21382283957132430668818595)
            ·
              refine ⟨32073425935698646003227893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21382283957132430668818595 32073425935698646003227893)
              ·
                refine ⟨3006883681471748062802615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32073425935698646003227893 3006883681471748062802615)
                ·
                  refine ⟨4510325522207622094203923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006883681471748062802615 4510325522207622094203923)
                  ·
                    refine ⟨6765488283311433141305885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4510325522207622094203923 6765488283311433141305885)
                    ·
                      refine ⟨2537058106241787427989707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6765488283311433141305885 2537058106241787427989707)
                      ·
                        rfl

theorem cell23_4940903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_4940903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940903 prefixEnd_4940903 := by exact prefixLift 4940903
  have htrace : WordTrace (prefixWord ++ tailWord_4940903) baseStart_4940903 baseEnd_4940903 := by
    simpa [prefixWord, tailWord_4940903, baseEnd_4940903] using wordTrace_append hprefix tailTrace_4940903
  have hstable : (prefixWord ++ tailWord_4940903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940903).length < 2 ^ (prefixWord ++ tailWord_4940903).sum := by decide
  have hdescent : baseEnd_4940903 < baseStart_4940903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940906 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_4940906 : Nat := 118140960795 + 4940906 * 2 ^ 59
def prefixEnd_4940906 : Nat := 4983230072969 + 3 ^ 40 * 4940906 * 2
def baseEnd_4940906 : Nat := 845686548894583638750731

theorem tailTrace_4940906 : CollatzResearch.WordTrace tailWord_4940906 prefixEnd_4940906 845686548894583638750731 := by
  unfold tailWord_4940906
  simp only [CollatzResearch.WordTrace]
  refine ⟨45052411659487219102102643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120139764425299250938940381 45052411659487219102102643)
  ·
    refine ⟨67578617489230828653153965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45052411659487219102102643 67578617489230828653153965)
    ·
      refine ⟨25341981558461560744932737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67578617489230828653153965 25341981558461560744932737)
      ·
        refine ⟨19006486168846170558699553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25341981558461560744932737 19006486168846170558699553)
        ·
          refine ⟨14254864626634627919024665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19006486168846170558699553 14254864626634627919024665)
          ·
            refine ⟨10691148469975970939268499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14254864626634627919024665 10691148469975970939268499)
            ·
              refine ⟨16036722704963956408902749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10691148469975970939268499 16036722704963956408902749)
              ·
                refine ⟨6013771014361483653338531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16036722704963956408902749 6013771014361483653338531)
                ·
                  refine ⟨9020656521542225480007797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6013771014361483653338531 9020656521542225480007797)
                  ·
                    refine ⟨845686548894583638750731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9020656521542225480007797 845686548894583638750731)
                    ·
                      rfl

theorem cell23_4940906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_4940906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940906 prefixEnd_4940906 := by exact prefixLift 4940906
  have htrace : WordTrace (prefixWord ++ tailWord_4940906) baseStart_4940906 baseEnd_4940906 := by
    simpa [prefixWord, tailWord_4940906, baseEnd_4940906] using wordTrace_append hprefix tailTrace_4940906
  have hstable : (prefixWord ++ tailWord_4940906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940906).length < 2 ^ (prefixWord ++ tailWord_4940906).sum := by decide
  have hdescent : baseEnd_4940906 < baseStart_4940906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940919 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 4, 4]
def baseStart_4940919 : Nat := 118140960795 + 4940919 * 2 ^ 59
def prefixEnd_4940919 : Nat := 4983230072969 + 3 ^ 40 * 4940919 * 2
def baseEnd_4940919 : Nat := 845688773977419788463211

theorem tailTrace_4940919 : CollatzResearch.WordTrace tailWord_4940919 prefixEnd_4940919 845688773977419788463211 := by
  unfold tailWord_4940919
  simp only [CollatzResearch.WordTrace]
  refine ⟨180210120786901779628633811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120140080524601186419089207 180210120786901779628633811)
  ·
    refine ⟨270315181180352669442950717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180210120786901779628633811 270315181180352669442950717)
    ·
      refine ⟨101368192942632251041106519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270315181180352669442950717 101368192942632251041106519)
      ·
        refine ⟨152052289413948376561659779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101368192942632251041106519 152052289413948376561659779)
        ·
          refine ⟨228078434120922564842489669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152052289413948376561659779 228078434120922564842489669)
          ·
            refine ⟨42764706397672980907966813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228078434120922564842489669 42764706397672980907966813)
            ·
              refine ⟨16036764899127367840487555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42764706397672980907966813 16036764899127367840487555)
              ·
                refine ⟨24055147348691051760731333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16036764899127367840487555 24055147348691051760731333)
                ·
                  refine ⟨4510340127879572205137125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24055147348691051760731333 4510340127879572205137125)
                  ·
                    refine ⟨845688773977419788463211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4510340127879572205137125 845688773977419788463211)
                    ·
                      rfl

theorem cell23_4940919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_4940919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940919 prefixEnd_4940919 := by exact prefixLift 4940919
  have htrace : WordTrace (prefixWord ++ tailWord_4940919) baseStart_4940919 baseEnd_4940919 := by
    simpa [prefixWord, tailWord_4940919, baseEnd_4940919] using wordTrace_append hprefix tailTrace_4940919
  have hstable : (prefixWord ++ tailWord_4940919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940919).length < 2 ^ (prefixWord ++ tailWord_4940919).sum := by decide
  have hdescent : baseEnd_4940919 < baseStart_4940919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940922 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_4940922 : Nat := 118140960795 + 4940922 * 2 ^ 59
def prefixEnd_4940922 : Nat := 4983230072969 + 3 ^ 40 * 4940922 * 2
def baseEnd_4940922 : Nat := 2537067862374222853652119

theorem tailTrace_4940922 : CollatzResearch.WordTrace tailWord_4940922 prefixEnd_4940922 2537067862374222853652119 := by
  unfold tailWord_4940922
  simp only [CollatzResearch.WordTrace]
  refine ⟨45052557551472727785248255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120140153470593940760662013 45052557551472727785248255)
  ·
    refine ⟨67578836327209091677872383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45052557551472727785248255 67578836327209091677872383)
    ·
      refine ⟨101368254490813637516808575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67578836327209091677872383 101368254490813637516808575)
      ·
        refine ⟨152052381736220456275212863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101368254490813637516808575 152052381736220456275212863)
        ·
          refine ⟨228078572604330684412819295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152052381736220456275212863 228078572604330684412819295)
          ·
            refine ⟨342117858906496026619228943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228078572604330684412819295 342117858906496026619228943)
            ·
              refine ⟨513176788359744039928843415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342117858906496026619228943 513176788359744039928843415)
              ·
                refine ⟨769765182539616059893265123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513176788359744039928843415 769765182539616059893265123)
                ·
                  refine ⟨1154647773809424089839897685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769765182539616059893265123 1154647773809424089839897685)
                  ·
                    refine ⟨13531028599329188552811301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1154647773809424089839897685 13531028599329188552811301)
                    ·
                      refine ⟨2537067862374222853652119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13531028599329188552811301 2537067862374222853652119)
                      ·
                        rfl

theorem cell23_4940922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_4940922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940922 prefixEnd_4940922 := by exact prefixLift 4940922
  have htrace : WordTrace (prefixWord ++ tailWord_4940922) baseStart_4940922 baseEnd_4940922 := by
    simpa [prefixWord, tailWord_4940922, baseEnd_4940922] using wordTrace_append hprefix tailTrace_4940922
  have hstable : (prefixWord ++ tailWord_4940922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940922).length < 2 ^ (prefixWord ++ tailWord_4940922).sum := by decide
  have hdescent : baseEnd_4940922 < baseStart_4940922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940929 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4940929 : Nat := 118140960795 + 4940929 * 2 ^ 59
def prefixEnd_4940929 : Nat := 4983230072969 + 3 ^ 40 * 4940929 * 2
def baseEnd_4940929 : Nat := 2537071456738804326264587

theorem tailTrace_4940929 : CollatzResearch.WordTrace tailWord_4940929 prefixEnd_4940929 2537071456738804326264587 := by
  unfold tailWord_4940929
  simp only [CollatzResearch.WordTrace]
  refine ⟨180210485516865551336497841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120140323677910367557665227 180210485516865551336497841)
  ·
    refine ⟨135157864137649163502373381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180210485516865551336497841 135157864137649163502373381)
    ·
      refine ⟨25342099525809218156695009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135157864137649163502373381 25342099525809218156695009)
      ·
        refine ⟨19006574644356913617521257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25342099525809218156695009 19006574644356913617521257)
        ·
          refine ⟨14254930983267685213140943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19006574644356913617521257 14254930983267685213140943)
          ·
            refine ⟨21382396474901527819711415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14254930983267685213140943 21382396474901527819711415)
            ·
              refine ⟨32073594712352291729567123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21382396474901527819711415 32073594712352291729567123)
              ·
                refine ⟨48110392068528437594350685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32073594712352291729567123 48110392068528437594350685)
                ·
                  refine ⟨18041397025698164097881507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48110392068528437594350685 18041397025698164097881507)
                  ·
                    refine ⟨27062095538547246146822261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18041397025698164097881507 27062095538547246146822261)
                    ·
                      refine ⟨2537071456738804326264587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27062095538547246146822261 2537071456738804326264587)
                      ·
                        rfl

theorem cell23_4940929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4940929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940929 prefixEnd_4940929 := by exact prefixLift 4940929
  have htrace : WordTrace (prefixWord ++ tailWord_4940929) baseStart_4940929 baseEnd_4940929 := by
    simpa [prefixWord, tailWord_4940929, baseEnd_4940929] using wordTrace_append hprefix tailTrace_4940929
  have hstable : (prefixWord ++ tailWord_4940929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940929).length < 2 ^ (prefixWord ++ tailWord_4940929).sum := by decide
  have hdescent : baseEnd_4940929 < baseStart_4940929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940986 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2]
def baseStart_4940986 : Nat := 118140960795 + 4940986 * 2 ^ 59
def prefixEnd_4940986 : Nat := 4983230072969 + 3 ^ 40 * 4940986 * 2
def baseEnd_4940986 : Nat := 2537100725136110603251825

theorem tailTrace_4940986 : CollatzResearch.WordTrace tailWord_4940986 prefixEnd_4940986 2537100725136110603251825 := by
  unfold tailWord_4940986
  simp only [CollatzResearch.WordTrace]
  refine ⟨45053141119414762517830703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120141709651772700047548541 45053141119414762517830703)
  ·
    refine ⟨67579711679122143776746055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45053141119414762517830703 67579711679122143776746055)
    ·
      refine ⟨101369567518683215665119083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67579711679122143776746055 101369567518683215665119083)
      ·
        refine ⟨152054351278024823497678625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101369567518683215665119083 152054351278024823497678625)
        ·
          refine ⟨114040763458518617623258969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152054351278024823497678625 114040763458518617623258969)
          ·
            refine ⟨85530572593888963217444227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114040763458518617623258969 85530572593888963217444227)
            ·
              refine ⟨128295858890833444826166341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85530572593888963217444227 128295858890833444826166341)
              ·
                refine ⟨24055473542031270904906189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128295858890833444826166341 24055473542031270904906189)
                ·
                  refine ⟨9020802578261726589339821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24055473542031270904906189 9020802578261726589339821)
                  ·
                    refine ⟨3382800966848147471002433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9020802578261726589339821 3382800966848147471002433)
                    ·
                      refine ⟨2537100725136110603251825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3382800966848147471002433 2537100725136110603251825)
                      ·
                        rfl

theorem cell23_4940986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_4940986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940986 prefixEnd_4940986 := by exact prefixLift 4940986
  have htrace : WordTrace (prefixWord ++ tailWord_4940986) baseStart_4940986 baseEnd_4940986 := by
    simpa [prefixWord, tailWord_4940986, baseEnd_4940986] using wordTrace_append hprefix tailTrace_4940986
  have hstable : (prefixWord ++ tailWord_4940986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940986).length < 2 ^ (prefixWord ++ tailWord_4940986).sum := by decide
  have hdescent : baseEnd_4940986 < baseStart_4940986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4940994 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_4940994 : Nat := 118140960795 + 4940994 * 2 ^ 59
def prefixEnd_4940994 : Nat := 4983230072969 + 3 ^ 40 * 4940994 * 2
def baseEnd_4940994 : Nat := 2537104832981346571951789

theorem tailTrace_4940994 : CollatzResearch.WordTrace tailWord_4940994 prefixEnd_4940994 2537104832981346571951789 := by
  unfold tailWord_4940994
  simp only [CollatzResearch.WordTrace]
  refine ⟨45053214065407516859403509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120141904174420044958409357 45053214065407516859403509)
  ·
    refine ⟨4223738818631954705569079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45053214065407516859403509 4223738818631954705569079)
    ·
      refine ⟨6335608227947932058353619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4223738818631954705569079 6335608227947932058353619)
      ·
        refine ⟨9503412341921898087530429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6335608227947932058353619 9503412341921898087530429)
        ·
          refine ⟨3563779628220711782823911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9503412341921898087530429 3563779628220711782823911)
          ·
            refine ⟨5345669442331067674235867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563779628220711782823911 5345669442331067674235867)
            ·
              refine ⟨8018504163496601511353801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345669442331067674235867 8018504163496601511353801)
              ·
                refine ⟨6013878122622451133515351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8018504163496601511353801 6013878122622451133515351)
                ·
                  refine ⟨9020817183933676700273027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6013878122622451133515351 9020817183933676700273027)
                  ·
                    refine ⟨13531225775900515050409541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9020817183933676700273027 13531225775900515050409541)
                    ·
                      refine ⟨2537104832981346571951789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13531225775900515050409541 2537104832981346571951789)
                      ·
                        rfl

theorem cell23_4940994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_4940994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4940994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4940994 prefixEnd_4940994 := by exact prefixLift 4940994
  have htrace : WordTrace (prefixWord ++ tailWord_4940994) baseStart_4940994 baseEnd_4940994 := by
    simpa [prefixWord, tailWord_4940994, baseEnd_4940994] using wordTrace_append hprefix tailTrace_4940994
  have hstable : (prefixWord ++ tailWord_4940994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4940994).length < 2 ^ (prefixWord ++ tailWord_4940994).sum := by decide
  have hdescent : baseEnd_4940994 < baseStart_4940994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4940994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941106 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_4941106 : Nat := 118140960795 + 4941106 * 2 ^ 59
def prefixEnd_4941106 : Nat := 4983230072969 + 3 ^ 40 * 4941106 * 2
def baseEnd_4941106 : Nat := 2537162342814650133751273

theorem tailTrace_4941106 : CollatzResearch.WordTrace tailWord_4941106 prefixEnd_4941106 2537162342814650133751273 := by
  unfold tailWord_4941106
  simp only [CollatzResearch.WordTrace]
  refine ⟨45054235309306077641422793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120144627491482873710460781 45054235309306077641422793)
  ·
    refine ⟨33790676481979558231067095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45054235309306077641422793 33790676481979558231067095)
    ·
      refine ⟨50686014722969337346600643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33790676481979558231067095 50686014722969337346600643)
      ·
        refine ⟨76029022084454006019900965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50686014722969337346600643 76029022084454006019900965)
        ·
          refine ⟨14255441640835126128731431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76029022084454006019900965 14255441640835126128731431)
          ·
            refine ⟨21383162461252689193097147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14255441640835126128731431 21383162461252689193097147)
            ·
              refine ⟨32074743691879033789645721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21383162461252689193097147 32074743691879033789645721)
              ·
                refine ⟨24056057768909275342234291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32074743691879033789645721 24056057768909275342234291)
                ·
                  refine ⟨36084086653363913013351437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24056057768909275342234291 36084086653363913013351437)
                  ·
                    refine ⟨13531532495011467380006789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36084086653363913013351437 13531532495011467380006789)
                    ·
                      refine ⟨2537162342814650133751273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13531532495011467380006789 2537162342814650133751273)
                      ·
                        rfl

theorem cell23_4941106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_4941106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941106 prefixEnd_4941106 := by exact prefixLift 4941106
  have htrace : WordTrace (prefixWord ++ tailWord_4941106) baseStart_4941106 baseEnd_4941106 := by
    simpa [prefixWord, tailWord_4941106, baseEnd_4941106] using wordTrace_append hprefix tailTrace_4941106
  have hstable : (prefixWord ++ tailWord_4941106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941106).length < 2 ^ (prefixWord ++ tailWord_4941106).sum := by decide
  have hdescent : baseEnd_4941106 < baseStart_4941106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941129 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 8]
def baseStart_4941129 : Nat := 118140960795 + 4941129 * 2 ^ 59
def prefixEnd_4941129 : Nat := 4983230072969 + 3 ^ 40 * 4941129 * 2
def baseEnd_4941129 : Nat := 281908239207744838195963

theorem tailTrace_4941129 : CollatzResearch.WordTrace tailWord_4941129 prefixEnd_4941129 281908239207744838195963 := by
  unfold tailWord_4941129
  simp only [CollatzResearch.WordTrace]
  refine ⟨180217780116140985493778441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120145186744093990329185627 180217780116140985493778441)
  ·
    refine ⟨135163335087105739120333831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180217780116140985493778441 135163335087105739120333831)
    ·
      refine ⟨202745002630658608680500747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135163335087105739120333831 202745002630658608680500747)
      ·
        refine ⟨304117503945987913020751121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202745002630658608680500747 304117503945987913020751121)
        ·
          refine ⟨228088127959490934765563341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304117503945987913020751121 228088127959490934765563341)
          ·
            refine ⟨85533047984809100537086253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228088127959490934765563341 85533047984809100537086253)
            ·
              refine ⟨32074892994303412701407345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85533047984809100537086253 32074892994303412701407345)
              ·
                refine ⟨24056169745727559526055509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32074892994303412701407345 24056169745727559526055509)
                ·
                  refine ⟨281908239207744838195963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24056169745727559526055509 281908239207744838195963)
                  ·
                    rfl

theorem cell23_4941129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 8].length) (baseStart_4941129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941129 prefixEnd_4941129 := by exact prefixLift 4941129
  have htrace : WordTrace (prefixWord ++ tailWord_4941129) baseStart_4941129 baseEnd_4941129 := by
    simpa [prefixWord, tailWord_4941129, baseEnd_4941129] using wordTrace_append hprefix tailTrace_4941129
  have hstable : (prefixWord ++ tailWord_4941129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941129).length < 2 ^ (prefixWord ++ tailWord_4941129).sum := by decide
  have hdescent : baseEnd_4941129 < baseStart_4941129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941143 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_4941143 : Nat := 118140960795 + 4941143 * 2 ^ 59
def prefixEnd_4941143 : Nat := 4983230072969 + 3 ^ 40 * 4941143 * 2
def baseEnd_4941143 : Nat := 2537181341598866488988603

theorem tailTrace_4941143 : CollatzResearch.WordTrace tailWord_4941143 prefixEnd_4941143 2537181341598866488988603 := by
  unfold tailWord_4941143
  simp only [CollatzResearch.WordTrace]
  refine ⟨180218290738090265884788083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120145527158726843923192055 180218290738090265884788083)
  ·
    refine ⟨270327436107135398827182125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180218290738090265884788083 270327436107135398827182125)
    ·
      refine ⟨101372788540175774560193297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270327436107135398827182125 101372788540175774560193297)
      ·
        refine ⟨76029591405131830920144973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101372788540175774560193297 76029591405131830920144973)
        ·
          refine ⟨28511096776924436595054365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76029591405131830920144973 28511096776924436595054365)
          ·
            refine ⟨10691661291346663723145387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28511096776924436595054365 10691661291346663723145387)
            ·
              refine ⟨16037491937019995584718081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10691661291346663723145387 16037491937019995584718081)
              ·
                refine ⟨12028118952764996688538561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16037491937019995584718081 12028118952764996688538561)
                ·
                  refine ⟨9021089214573747516403921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12028118952764996688538561 9021089214573747516403921)
                  ·
                    refine ⟨6765816910930310637302941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9021089214573747516403921 6765816910930310637302941)
                    ·
                      refine ⟨2537181341598866488988603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6765816910930310637302941 2537181341598866488988603)
                      ·
                        rfl

theorem cell23_4941143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_4941143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941143 prefixEnd_4941143 := by exact prefixLift 4941143
  have htrace : WordTrace (prefixWord ++ tailWord_4941143) baseStart_4941143 baseEnd_4941143 := by
    simpa [prefixWord, tailWord_4941143, baseEnd_4941143] using wordTrace_append hprefix tailTrace_4941143
  have hstable : (prefixWord ++ tailWord_4941143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941143).length < 2 ^ (prefixWord ++ tailWord_4941143).sum := by decide
  have hdescent : baseEnd_4941143 < baseStart_4941143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941213 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_4941213 : Nat := 118140960795 + 4941213 * 2 ^ 59
def prefixEnd_4941213 : Nat := 4983230072969 + 3 ^ 40 * 4941213 * 2
def baseEnd_4941213 : Nat := 2537217285244681215113281

theorem tailTrace_4941213 : CollatzResearch.WordTrace tailWord_4941213 prefixEnd_4941213 2537217285244681215113281 := by
  unfold tailWord_4941213
  simp only [CollatzResearch.WordTrace]
  refine ⟨180220843847836667839836293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120147229231891111893224195 180220843847836667839836293)
  ·
    refine ⟨33791408221469375219969305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180220843847836667839836293 33791408221469375219969305)
    ·
      refine ⟨25343556166102031414976979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33791408221469375219969305 25343556166102031414976979)
      ·
        refine ⟨38015334249153047122465469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25343556166102031414976979 38015334249153047122465469)
        ·
          refine ⟨14255750343432392670924551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38015334249153047122465469 14255750343432392670924551)
          ·
            refine ⟨21383625515148589006386827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14255750343432392670924551 21383625515148589006386827)
            ·
              refine ⟨32075438272722883509580241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21383625515148589006386827 32075438272722883509580241)
              ·
                refine ⟨24056578704542162632185181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32075438272722883509580241 24056578704542162632185181)
                ·
                  refine ⟨9021217014203310987069443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24056578704542162632185181 9021217014203310987069443)
                  ·
                    refine ⟨13531825521304966480604165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9021217014203310987069443 13531825521304966480604165)
                    ·
                      refine ⟨2537217285244681215113281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13531825521304966480604165 2537217285244681215113281)
                      ·
                        rfl

theorem cell23_4941213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_4941213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941213 prefixEnd_4941213 := by exact prefixLift 4941213
  have htrace : WordTrace (prefixWord ++ tailWord_4941213) baseStart_4941213 baseEnd_4941213 := by
    simpa [prefixWord, tailWord_4941213, baseEnd_4941213] using wordTrace_append hprefix tailTrace_4941213
  have hstable : (prefixWord ++ tailWord_4941213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941213).length < 2 ^ (prefixWord ++ tailWord_4941213).sum := by decide
  have hdescent : baseEnd_4941213 < baseStart_4941213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941216 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_4941216 : Nat := 118140960795 + 4941216 * 2 ^ 59
def prefixEnd_4941216 : Nat := 4983230072969 + 3 ^ 40 * 4941216 * 2
def baseEnd_4941216 : Nat := 2537218825686644703375767

theorem tailTrace_4941216 : CollatzResearch.WordTrace tailWord_4941216 prefixEnd_4941216 2537218825686644703375767 := by
  unfold tailWord_4941216
  simp only [CollatzResearch.WordTrace]
  refine ⟨90110476633412899676097751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120147302177883866234797001 90110476633412899676097751)
  ·
    refine ⟨135165714950119349514146627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90110476633412899676097751 135165714950119349514146627)
    ·
      refine ⟨202748572425179024271219941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135165714950119349514146627 202748572425179024271219941)
      ·
        refine ⟨38015357329721067050853739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202748572425179024271219941 38015357329721067050853739)
        ·
          refine ⟨57023035994581600576280609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38015357329721067050853739 57023035994581600576280609)
          ·
            refine ⟨42767276995936200432210457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57023035994581600576280609 42767276995936200432210457)
            ·
              refine ⟨32075457746952150324157843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42767276995936200432210457 32075457746952150324157843)
              ·
                refine ⟨48113186620428225486236765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32075457746952150324157843 48113186620428225486236765)
                ·
                  refine ⟨18042444982660584557338787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48113186620428225486236765 18042444982660584557338787)
                  ·
                    refine ⟨27063667473990876836008181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18042444982660584557338787 27063667473990876836008181)
                    ·
                      refine ⟨2537218825686644703375767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27063667473990876836008181 2537218825686644703375767)
                      ·
                        rfl

theorem cell23_4941216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_4941216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941216 prefixEnd_4941216 := by exact prefixLift 4941216
  have htrace : WordTrace (prefixWord ++ tailWord_4941216) baseStart_4941216 baseEnd_4941216 := by
    simpa [prefixWord, tailWord_4941216, baseEnd_4941216] using wordTrace_append hprefix tailTrace_4941216
  have hstable : (prefixWord ++ tailWord_4941216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941216).length < 2 ^ (prefixWord ++ tailWord_4941216).sum := by decide
  have hdescent : baseEnd_4941216 < baseStart_4941216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941223 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 1, 6]
def baseStart_4941223 : Nat := 118140960795 + 4941223 * 2 ^ 59
def prefixEnd_4941223 : Nat := 4983230072969 + 3 ^ 40 * 4941223 * 2
def baseEnd_4941223 : Nat := 845740806683742058662745

theorem tailTrace_4941223 : CollatzResearch.WordTrace tailWord_4941223 prefixEnd_4941223 845740806683742058662745 := by
  unfold tailWord_4941223
  simp only [CollatzResearch.WordTrace]
  refine ⟨180221208577800439547700323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120147472385200293031800215 180221208577800439547700323)
  ·
    refine ⟨270331812866700659321550485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180221208577800439547700323 270331812866700659321550485)
    ·
      refine ⟨12671803728126593405697679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 270331812866700659321550485 12671803728126593405697679)
      ·
        refine ⟨19007705592189890108546519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12671803728126593405697679 19007705592189890108546519)
        ·
          refine ⟨28511558388284835162819779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19007705592189890108546519 28511558388284835162819779)
          ·
            refine ⟨42767337582427252744229669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28511558388284835162819779 42767337582427252744229669)
            ·
              refine ⟨8018875796705109889543063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42767337582427252744229669 8018875796705109889543063)
              ·
                refine ⟨12028313695057664834314595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8018875796705109889543063 12028313695057664834314595)
                ·
                  refine ⟨18042470542586497251471893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12028313695057664834314595 18042470542586497251471893)
                  ·
                    refine ⟨845740806683742058662745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18042470542586497251471893 845740806683742058662745)
                    ·
                      rfl

theorem cell23_4941223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_4941223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941223 prefixEnd_4941223 := by exact prefixLift 4941223
  have htrace : WordTrace (prefixWord ++ tailWord_4941223) baseStart_4941223 baseEnd_4941223 := by
    simpa [prefixWord, tailWord_4941223, baseEnd_4941223] using wordTrace_append hprefix tailTrace_4941223
  have hstable : (prefixWord ++ tailWord_4941223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941223).length < 2 ^ (prefixWord ++ tailWord_4941223).sum := by decide
  have hdescent : baseEnd_4941223 < baseStart_4941223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941233 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_4941233 : Nat := 118140960795 + 4941233 * 2 ^ 59
def prefixEnd_4941233 : Nat := 4983230072969 + 3 ^ 40 * 4941233 * 2
def baseEnd_4941233 : Nat := 2537227554857771136863189

theorem tailTrace_4941233 : CollatzResearch.WordTrace tailWord_4941233 prefixEnd_4941233 2537227554857771136863189 := by
  unfold tailWord_4941233
  simp only [CollatzResearch.WordTrace]
  refine ⟨180221573307764211255564353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120147715538509474170376235 180221573307764211255564353)
  ·
    refine ⟨135166179980823158441673265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180221573307764211255564353 135166179980823158441673265)
    ·
      refine ⟨101374634985617368831254949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135166179980823158441673265 101374634985617368831254949)
      ·
        refine ⟨19007744059803256655860303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101374634985617368831254949 19007744059803256655860303)
        ·
          refine ⟨28511616089704884983790455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19007744059803256655860303 28511616089704884983790455)
          ·
            refine ⟨42767424134557327475685683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28511616089704884983790455 42767424134557327475685683)
            ·
              refine ⟨64151136201835991213528525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42767424134557327475685683 64151136201835991213528525)
              ·
                refine ⟨24056676075688496705073197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64151136201835991213528525 24056676075688496705073197)
                ·
                  refine ⟨9021253528383186264402449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24056676075688496705073197 9021253528383186264402449)
                  ·
                    refine ⟨6765940146287389698301837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9021253528383186264402449 6765940146287389698301837)
                    ·
                      refine ⟨2537227554857771136863189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6765940146287389698301837 2537227554857771136863189)
                      ·
                        rfl

theorem cell23_4941233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_4941233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941233 prefixEnd_4941233 := by exact prefixLift 4941233
  have htrace : WordTrace (prefixWord ++ tailWord_4941233) baseStart_4941233 baseEnd_4941233 := by
    simpa [prefixWord, tailWord_4941233, baseEnd_4941233] using wordTrace_append hprefix tailTrace_4941233
  have hstable : (prefixWord ++ tailWord_4941233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941233).length < 2 ^ (prefixWord ++ tailWord_4941233).sum := by decide
  have hdescent : baseEnd_4941233 < baseStart_4941233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941244 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_4941244 : Nat := 118140960795 + 4941244 * 2 ^ 59
def prefixEnd_4941244 : Nat := 4983230072969 + 3 ^ 40 * 4941244 * 2
def baseEnd_4941244 : Nat := 845744401048323531275213

theorem tailTrace_4941244 : CollatzResearch.WordTrace tailWord_4941244 prefixEnd_4941244 845744401048323531275213 := by
  unfold tailWord_4941244
  simp only [CollatzResearch.WordTrace]
  refine ⟨90110987255362180067107393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120147983007149573422809857 90110987255362180067107393)
  ·
    refine ⟨67583240441521635050330545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90110987255362180067107393 67583240441521635050330545)
    ·
      refine ⟨50687430331141226287747909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67583240441521635050330545 50687430331141226287747909)
      ·
        refine ⟨9503893187088979928952733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50687430331141226287747909 9503893187088979928952733)
        ·
          refine ⟨3563959945158367473357275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9503893187088979928952733 3563959945158367473357275)
          ·
            refine ⟨5345939917737551210035913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563959945158367473357275 5345939917737551210035913)
            ·
              refine ⟨4009454938303163407526935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5345939917737551210035913 4009454938303163407526935)
              ·
                refine ⟨6014182407454745111290403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4009454938303163407526935 6014182407454745111290403)
                ·
                  refine ⟨9021273611182117666935605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6014182407454745111290403 9021273611182117666935605)
                  ·
                    refine ⟨845744401048323531275213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9021273611182117666935605 845744401048323531275213)
                    ·
                      rfl

theorem cell23_4941244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_4941244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941244 prefixEnd_4941244 := by exact prefixLift 4941244
  have htrace : WordTrace (prefixWord ++ tailWord_4941244) baseStart_4941244 baseEnd_4941244 := by
    simpa [prefixWord, tailWord_4941244, baseEnd_4941244] using wordTrace_append hprefix tailTrace_4941244
  have hstable : (prefixWord ++ tailWord_4941244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941244).length < 2 ^ (prefixWord ++ tailWord_4941244).sum := by decide
  have hdescent : baseEnd_4941244 < baseStart_4941244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941393 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_4941393 : Nat := 118140960795 + 4941393 * 2 ^ 59
def prefixEnd_4941393 : Nat := 4983230072969 + 3 ^ 40 * 4941393 * 2
def baseEnd_4941393 : Nat := 2537309711762490510862453

theorem tailTrace_4941393 : CollatzResearch.WordTrace tailWord_4941393 prefixEnd_4941393 2537309711762490510862453 := by
  unfold tailWord_4941393
  simp only [CollatzResearch.WordTrace]
  refine ⟨180227408987184558581388833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120151605991456372387592555 180227408987184558581388833)
  ·
    refine ⟨135170556740388418936041625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180227408987184558581388833 135170556740388418936041625)
    ·
      refine ⟨101377917555291314202031219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135170556740388418936041625 101377917555291314202031219)
      ·
        refine ⟨152066876332936971303046829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101377917555291314202031219 152066876332936971303046829)
        ·
          refine ⟨57025078624851364238642561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152066876332936971303046829 57025078624851364238642561)
          ·
            refine ⟨42768808968638523178981921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57025078624851364238642561 42768808968638523178981921)
            ·
              refine ⟨32076606726478892384236441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42768808968638523178981921 32076606726478892384236441)
              ·
                refine ⟨24057455044859169288177331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32076606726478892384236441 24057455044859169288177331)
                ·
                  refine ⟨36086182567288753932265997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24057455044859169288177331 36086182567288753932265997)
                  ·
                    refine ⟨13532318462733282724599749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36086182567288753932265997 13532318462733282724599749)
                    ·
                      refine ⟨2537309711762490510862453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13532318462733282724599749 2537309711762490510862453)
                      ·
                        rfl

theorem cell23_4941393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_4941393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941393 prefixEnd_4941393 := by exact prefixLift 4941393
  have htrace : WordTrace (prefixWord ++ tailWord_4941393) baseStart_4941393 baseEnd_4941393 := by
    simpa [prefixWord, tailWord_4941393, baseEnd_4941393] using wordTrace_append hprefix tailTrace_4941393
  have hstable : (prefixWord ++ tailWord_4941393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941393).length < 2 ^ (prefixWord ++ tailWord_4941393).sum := by decide
  have hdescent : baseEnd_4941393 < baseStart_4941393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941433 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 8]
def baseStart_4941433 : Nat := 118140960795 + 4941433 * 2 ^ 59
def prefixEnd_4941433 : Nat := 4983230072969 + 3 ^ 40 * 4941433 * 2
def baseEnd_4941433 : Nat := 281925583443185594929141

theorem tailTrace_4941433 : CollatzResearch.WordTrace tailWord_4941433 prefixEnd_4941433 281925583443185594929141 := by
  unfold tailWord_4941433
  simp only [CollatzResearch.WordTrace]
  refine ⟨180228867907039645412844953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120152578604693096941896635 180228867907039645412844953)
  ·
    refine ⟨135171650930279734059633715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180228867907039645412844953 135171650930279734059633715)
    ·
      refine ⟨202757476395419601089450573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135171650930279734059633715 202757476395419601089450573)
      ·
        refine ⟨76034053648282350408543965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202757476395419601089450573 76034053648282350408543965)
        ·
          refine ⟨28512770118105881403203987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76034053648282350408543965 28512770118105881403203987)
          ·
            refine ⟨42769155177158822104805981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28512770118105881403203987 42769155177158822104805981)
            ·
              refine ⟨16038433191434558289302243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42769155177158822104805981 16038433191434558289302243)
              ·
                refine ⟨24057649787151837433953365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16038433191434558289302243 24057649787151837433953365)
                ·
                  refine ⟨281925583443185594929141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24057649787151837433953365 281925583443185594929141)
                  ·
                    rfl

theorem cell23_4941433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 8].length) (baseStart_4941433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941433 prefixEnd_4941433 := by exact prefixLift 4941433
  have htrace : WordTrace (prefixWord ++ tailWord_4941433) baseStart_4941433 baseEnd_4941433 := by
    simpa [prefixWord, tailWord_4941433, baseEnd_4941433] using wordTrace_append hprefix tailTrace_4941433
  have hstable : (prefixWord ++ tailWord_4941433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941433).length < 2 ^ (prefixWord ++ tailWord_4941433).sum := by decide
  have hdescent : baseEnd_4941433 < baseStart_4941433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941437 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_4941437 : Nat := 118140960795 + 4941437 * 2 ^ 59
def prefixEnd_4941437 : Nat := 4983230072969 + 3 ^ 40 * 4941437 * 2
def baseEnd_4941437 : Nat := 845777434970429446237417

theorem tailTrace_4941437 : CollatzResearch.WordTrace tailWord_4941437 prefixEnd_4941437 845777434970429446237417 := by
  unfold tailWord_4941437
  simp only [CollatzResearch.WordTrace]
  refine ⟨180229013799025154095990565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120152675866016769397327043 180229013799025154095990565)
  ·
    refine ⟨33792940087317216392998231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180229013799025154095990565 33792940087317216392998231)
    ·
      refine ⟨50689410130975824589497347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33792940087317216392998231 50689410130975824589497347)
      ·
        refine ⟨76034115196463736884246021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50689410130975824589497347 76034115196463736884246021)
        ·
          refine ⟨14256396599336950665796129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76034115196463736884246021 14256396599336950665796129)
          ·
            refine ⟨10692297449502712999347097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14256396599336950665796129 10692297449502712999347097)
            ·
              refine ⟨8019223087127034749510323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10692297449502712999347097 8019223087127034749510323)
              ·
                refine ⟨12028834630690552124265485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8019223087127034749510323 12028834630690552124265485)
                ·
                  refine ⟨4510812986508957046599557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12028834630690552124265485 4510812986508957046599557)
                  ·
                    refine ⟨845777434970429446237417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4510812986508957046599557 845777434970429446237417)
                    ·
                      rfl

theorem cell23_4941437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_4941437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941437 prefixEnd_4941437 := by exact prefixLift 4941437
  have htrace : WordTrace (prefixWord ++ tailWord_4941437) baseStart_4941437 baseEnd_4941437 := by
    simpa [prefixWord, tailWord_4941437, baseEnd_4941437] using wordTrace_append hprefix tailTrace_4941437
  have hstable : (prefixWord ++ tailWord_4941437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941437).length < 2 ^ (prefixWord ++ tailWord_4941437).sum := by decide
  have hdescent : baseEnd_4941437 < baseStart_4941437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941487 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 2, 3, 2]
def baseStart_4941487 : Nat := 118140960795 + 4941487 * 2 ^ 59
def prefixEnd_4941487 : Nat := 4983230072969 + 3 ^ 40 * 4941487 * 2
def baseEnd_4941487 : Nat := 2537357978944013143087021

theorem tailTrace_4941487 : CollatzResearch.WordTrace tailWord_4941487 prefixEnd_4941487 2537357978944013143087021 := by
  unfold tailWord_4941487
  simp only [CollatzResearch.WordTrace]
  refine ⟨180230837448844012635310715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120153891632562675090207143 180230837448844012635310715)
  ·
    refine ⟨270346256173266018952966073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180230837448844012635310715 270346256173266018952966073)
    ·
      refine ⟨202759692129949514214724555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270346256173266018952966073 202759692129949514214724555)
      ·
        refine ⟨304139538194924271322086833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202759692129949514214724555 304139538194924271322086833)
        ·
          refine ⟨228104653646193203491565125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304139538194924271322086833 228104653646193203491565125)
          ·
            refine ⟨42769622558661225654668461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228104653646193203491565125 42769622558661225654668461)
            ·
              refine ⟨16038608459497959620500673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42769622558661225654668461 16038608459497959620500673)
              ·
                refine ⟨12028956344623469715375505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16038608459497959620500673 12028956344623469715375505)
                ·
                  refine ⟨9021717258467602286531629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12028956344623469715375505 9021717258467602286531629)
                  ·
                    refine ⟨3383143971925350857449361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9021717258467602286531629 3383143971925350857449361)
                    ·
                      refine ⟨2537357978944013143087021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383143971925350857449361 2537357978944013143087021)
                      ·
                        rfl

theorem cell23_4941487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 3, 2].length) (baseStart_4941487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941487 prefixEnd_4941487 := by exact prefixLift 4941487
  have htrace : WordTrace (prefixWord ++ tailWord_4941487) baseStart_4941487 baseEnd_4941487 := by
    simpa [prefixWord, tailWord_4941487, baseEnd_4941487] using wordTrace_append hprefix tailTrace_4941487
  have hstable : (prefixWord ++ tailWord_4941487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941487).length < 2 ^ (prefixWord ++ tailWord_4941487).sum := by decide
  have hdescent : baseEnd_4941487 < baseStart_4941487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941514 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_4941514 : Nat := 118140960795 + 4941514 * 2 ^ 59
def prefixEnd_4941514 : Nat := 4983230072969 + 3 ^ 40 * 4941514 * 2
def baseEnd_4941514 : Nat := 845790614307228179149799

theorem tailTrace_4941514 : CollatzResearch.WordTrace tailWord_4941514 prefixEnd_4941514 845790614307228179149799 := by
  unfold tailWord_4941514
  simp only [CollatzResearch.WordTrace]
  refine ⟨45057955554936549061635899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120154548146497464164362397 45057955554936549061635899)
  ·
    refine ⟨67586933332404823592453849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45057955554936549061635899 67586933332404823592453849)
    ·
      refine ⟨50690199999303617694340387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67586933332404823592453849 50690199999303617694340387)
      ·
        refine ⟨76035299998955426541510581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50690199999303617694340387 76035299998955426541510581)
        ·
          refine ⟨7128309374902071238266617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76035299998955426541510581 7128309374902071238266617)
          ·
            refine ⟨5346232031176553428699963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7128309374902071238266617 5346232031176553428699963)
            ·
              refine ⟨8019348046764830143049945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5346232031176553428699963 8019348046764830143049945)
              ·
                refine ⟨6014511035073622607287459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8019348046764830143049945 6014511035073622607287459)
                ·
                  refine ⟨9021766552610433910931189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6014511035073622607287459 9021766552610433910931189)
                  ·
                    refine ⟨845790614307228179149799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9021766552610433910931189 845790614307228179149799)
                    ·
                      rfl

theorem cell23_4941514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_4941514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941514 prefixEnd_4941514 := by exact prefixLift 4941514
  have htrace : WordTrace (prefixWord ++ tailWord_4941514) baseStart_4941514 baseEnd_4941514 := by
    simpa [prefixWord, tailWord_4941514, baseEnd_4941514] using wordTrace_append hprefix tailTrace_4941514
  have hstable : (prefixWord ++ tailWord_4941514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941514).length < 2 ^ (prefixWord ++ tailWord_4941514).sum := by decide
  have hdescent : baseEnd_4941514 < baseStart_4941514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941530 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_4941530 : Nat := 118140960795 + 4941530 * 2 ^ 59
def prefixEnd_4941530 : Nat := 4983230072969 + 3 ^ 40 * 4941530 * 2
def baseEnd_4941530 : Nat := 2537380058612156474849323

theorem tailTrace_4941530 : CollatzResearch.WordTrace tailWord_4941530 prefixEnd_4941530 2537380058612156474849323 := by
  unfold tailWord_4941530
  simp only [CollatzResearch.WordTrace]
  refine ⟨45058101446922057744781511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120154937191792153986084029 45058101446922057744781511)
  ·
    refine ⟨67587152170383086617172267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45058101446922057744781511 67587152170383086617172267)
    ·
      refine ⟨101380728255574629925758401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67587152170383086617172267 101380728255574629925758401)
      ·
        refine ⟨76035546191680972444318801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101380728255574629925758401 76035546191680972444318801)
        ·
          refine ⟨57026659643760729333239101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76035546191680972444318801 57026659643760729333239101)
          ·
            refine ⟨21384997366410273499964663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57026659643760729333239101 21384997366410273499964663)
            ·
              refine ⟨32077496049615410249946995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21384997366410273499964663 32077496049615410249946995)
              ·
                refine ⟨48116244074423115374920493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32077496049615410249946995 48116244074423115374920493)
                ·
                  refine ⟨18043591527908668265595185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48116244074423115374920493 18043591527908668265595185)
                  ·
                    refine ⟨13532693645931501199196389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18043591527908668265595185 13532693645931501199196389)
                    ·
                      refine ⟨2537380058612156474849323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13532693645931501199196389 2537380058612156474849323)
                      ·
                        rfl

theorem cell23_4941530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_4941530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941530 prefixEnd_4941530 := by exact prefixLift 4941530
  have htrace : WordTrace (prefixWord ++ tailWord_4941530) baseStart_4941530 baseEnd_4941530 := by
    simpa [prefixWord, tailWord_4941530, baseEnd_4941530] using wordTrace_append hprefix tailTrace_4941530
  have hstable : (prefixWord ++ tailWord_4941530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941530).length < 2 ^ (prefixWord ++ tailWord_4941530).sum := by decide
  have hdescent : baseEnd_4941530 < baseStart_4941530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941544 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 2, 4]
def baseStart_4941544 : Nat := 118140960795 + 4941544 * 2 ^ 59
def prefixEnd_4941544 : Nat := 4983230072969 + 3 ^ 40 * 4941544 * 2
def baseEnd_4941544 : Nat := 845795749113773140024753

theorem tailTrace_4941544 : CollatzResearch.WordTrace tailWord_4941544 prefixEnd_4941544 845795749113773140024753 := by
  unfold tailWord_4941544
  simp only [CollatzResearch.WordTrace]
  refine ⟨90116458204818755685067843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120155277606425007580090457 90116458204818755685067843)
  ·
    refine ⟨135174687307228133527601765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90116458204818755685067843 135174687307228133527601765)
    ·
      refine ⟨25345253870105275036425331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135174687307228133527601765 25345253870105275036425331)
      ·
        refine ⟨38017880805157912554637997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25345253870105275036425331 38017880805157912554637997)
        ·
          refine ⟨14256705301934217207989249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38017880805157912554637997 14256705301934217207989249)
          ·
            refine ⟨10692528976450662905991937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14256705301934217207989249 10692528976450662905991937)
            ·
              refine ⟨8019396732337997179493953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10692528976450662905991937 8019396732337997179493953)
              ·
                refine ⟨6014547549253497884620465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8019396732337997179493953 6014547549253497884620465)
                ·
                  refine ⟨4510910661940123413465349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6014547549253497884620465 4510910661940123413465349)
                  ·
                    refine ⟨845795749113773140024753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4510910661940123413465349 845795749113773140024753)
                    ·
                      rfl

theorem cell23_4941544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_4941544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941544 prefixEnd_4941544 := by exact prefixLift 4941544
  have htrace : WordTrace (prefixWord ++ tailWord_4941544) baseStart_4941544 baseEnd_4941544 := by
    simpa [prefixWord, tailWord_4941544, baseEnd_4941544] using wordTrace_append hprefix tailTrace_4941544
  have hstable : (prefixWord ++ tailWord_4941544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941544).length < 2 ^ (prefixWord ++ tailWord_4941544).sum := by decide
  have hdescent : baseEnd_4941544 < baseStart_4941544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941551 : List Nat := [1, 1, 2, 1, 5, 1, 3, 4, 1, 2, 2]
def baseStart_4941551 : Nat := 118140960795 + 4941551 * 2 ^ 59
def prefixEnd_4941551 : Nat := 4983230072969 + 3 ^ 40 * 4941551 * 2
def baseEnd_4941551 : Nat := 2537390841705900892686727

theorem tailTrace_4941551 : CollatzResearch.WordTrace tailWord_4941551 prefixEnd_4941551 2537390841705900892686727 := by
  unfold tailWord_4941551
  simp only [CollatzResearch.WordTrace]
  refine ⟨180233171720612151565640507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120155447813741434377093671 180233171720612151565640507)
  ·
    refine ⟨270349757580918227348460761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180233171720612151565640507 270349757580918227348460761)
    ·
      refine ⟨202762318185688670511345571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270349757580918227348460761 202762318185688670511345571)
      ·
        refine ⟨304143477278533005767018357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202762318185688670511345571 304143477278533005767018357)
        ·
          refine ⟨28513450994862469290657971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 304143477278533005767018357 28513450994862469290657971)
          ·
            refine ⟨42770176492293703935986957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28513450994862469290657971 42770176492293703935986957)
            ·
              refine ⟨16038816184610138975995109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42770176492293703935986957 16038816184610138975995109)
              ·
                refine ⟨3007278034614401057999083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16038816184610138975995109 3007278034614401057999083)
                ·
                  refine ⟨4510917051921601586998625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007278034614401057999083 4510917051921601586998625)
                  ·
                    refine ⟨3383187788941201190248969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4510917051921601586998625 3383187788941201190248969)
                    ·
                      refine ⟨2537390841705900892686727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383187788941201190248969 2537390841705900892686727)
                      ·
                        rfl

theorem cell23_4941551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 2, 2].length) (baseStart_4941551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941551 prefixEnd_4941551 := by exact prefixLift 4941551
  have htrace : WordTrace (prefixWord ++ tailWord_4941551) baseStart_4941551 baseEnd_4941551 := by
    simpa [prefixWord, tailWord_4941551, baseEnd_4941551] using wordTrace_append hprefix tailTrace_4941551
  have hstable : (prefixWord ++ tailWord_4941551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941551).length < 2 ^ (prefixWord ++ tailWord_4941551).sum := by decide
  have hdescent : baseEnd_4941551 < baseStart_4941551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941600 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 4, 6]
def baseStart_4941600 : Nat := 118140960795 + 4941600 * 2 ^ 59
def prefixEnd_4941600 : Nat := 4983230072969 + 3 ^ 40 * 4941600 * 2
def baseEnd_4941600 : Nat := 845805334085990400324667

theorem tailTrace_4941600 : CollatzResearch.WordTrace tailWord_4941600 prefixEnd_4941600 845805334085990400324667 := by
  unfold tailWord_4941600
  simp only [CollatzResearch.WordTrace]
  refine ⟨90117479448717316467087127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120156639264956421956116169 90117479448717316467087127)
  ·
    refine ⟨135176219173075974700630691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90117479448717316467087127 135176219173075974700630691)
    ·
      refine ⟨202764328759613962050946037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135176219173075974700630691 202764328759613962050946037)
      ·
        refine ⟨19009155821213808942276191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202764328759613962050946037 19009155821213808942276191)
        ·
          refine ⟨28513733731820713413414287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19009155821213808942276191 28513733731820713413414287)
          ·
            refine ⟨42770600597731070120121431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28513733731820713413414287 42770600597731070120121431)
            ·
              refine ⟨64155900896596605180182147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42770600597731070120121431 64155900896596605180182147)
              ·
                refine ⟨96233851344894907770273221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64155900896596605180182147 96233851344894907770273221)
                ·
                  refine ⟨18043847127167795206926229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96233851344894907770273221 18043847127167795206926229)
                  ·
                    refine ⟨845805334085990400324667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18043847127167795206926229 845805334085990400324667)
                    ·
                      rfl

theorem cell23_4941600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_4941600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941600 prefixEnd_4941600 := by exact prefixLift 4941600
  have htrace : WordTrace (prefixWord ++ tailWord_4941600) baseStart_4941600 baseEnd_4941600 := by
    simpa [prefixWord, tailWord_4941600, baseEnd_4941600] using wordTrace_append hprefix tailTrace_4941600
  have hstable : (prefixWord ++ tailWord_4941600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941600).length < 2 ^ (prefixWord ++ tailWord_4941600).sum := by decide
  have hdescent : baseEnd_4941600 < baseStart_4941600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941601 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_4941601 : Nat := 118140960795 + 4941601 * 2 ^ 59
def prefixEnd_4941601 : Nat := 4983230072969 + 3 ^ 40 * 4941601 * 2
def baseEnd_4941601 : Nat := 2537416515738625697061497

theorem tailTrace_4941601 : CollatzResearch.WordTrace tailWord_4941601 prefixEnd_4941601 2537416515738625697061497 := by
  unfold tailWord_4941601
  simp only [CollatzResearch.WordTrace]
  refine ⟨180234995370431010104960657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120156663580287340069973771 180234995370431010104960657)
  ·
    refine ⟨135176246527823257578720493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180234995370431010104960657 135176246527823257578720493)
    ·
      refine ⟨50691092447933721592020185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135176246527823257578720493 50691092447933721592020185)
      ·
        refine ⟨38018319335950291194015139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50691092447933721592020185 38018319335950291194015139)
        ·
          refine ⟨57027479003925436791022709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38018319335950291194015139 57027479003925436791022709)
          ·
            refine ⟨5346326156618009699158379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57027479003925436791022709 5346326156618009699158379)
            ·
              refine ⟨8019489234927014548737569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5346326156618009699158379 8019489234927014548737569)
              ·
                refine ⟨6014616926195260911553177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8019489234927014548737569 6014616926195260911553177)
                ·
                  refine ⟨4510962694646445683664883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6014616926195260911553177 4510962694646445683664883)
                  ·
                    refine ⟨6766444041969668525497325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4510962694646445683664883 6766444041969668525497325)
                    ·
                      refine ⟨2537416515738625697061497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6766444041969668525497325 2537416515738625697061497)
                      ·
                        rfl

theorem cell23_4941601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_4941601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941601 prefixEnd_4941601 := by exact prefixLift 4941601
  have htrace : WordTrace (prefixWord ++ tailWord_4941601) baseStart_4941601 baseEnd_4941601 := by
    simpa [prefixWord, tailWord_4941601, baseEnd_4941601] using wordTrace_append hprefix tailTrace_4941601
  have hstable : (prefixWord ++ tailWord_4941601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941601).length < 2 ^ (prefixWord ++ tailWord_4941601).sum := by decide
  have hdescent : baseEnd_4941601 < baseStart_4941601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941624 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 1, 4, 2]
def baseStart_4941624 : Nat := 118140960795 + 4941624 * 2 ^ 59
def prefixEnd_4941624 : Nat := 4983230072969 + 3 ^ 40 * 4941624 * 2
def baseEnd_4941624 : Nat := 2537428325793679107073891

theorem tailTrace_4941624 : CollatzResearch.WordTrace tailWord_4941624 prefixEnd_4941624 2537428325793679107073891 := by
  unfold tailWord_4941624
  simp only [CollatzResearch.WordTrace]
  refine ⟨90117917124673842516523963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120157222832898456688698617 90117917124673842516523963)
  ·
    refine ⟨135176875687010763774785945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90117917124673842516523963 135176875687010763774785945)
    ·
      refine ⟨101382656765258072831089459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135176875687010763774785945 101382656765258072831089459)
      ·
        refine ⟨152073985147887109246634189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101382656765258072831089459 152073985147887109246634189)
        ·
          refine ⟨57027744430457665967487821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152073985147887109246634189 57027744430457665967487821)
          ·
            refine ⟨21385404161421624737807933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57027744430457665967487821 21385404161421624737807933)
            ·
              refine ⟨8019526560533109276677975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21385404161421624737807933 8019526560533109276677975)
              ·
                refine ⟨12029289840799663915016963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8019526560533109276677975 12029289840799663915016963)
                ·
                  refine ⟨18043934761199495872525445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12029289840799663915016963 18043934761199495872525445)
                  ·
                    refine ⟨3383237767724905476098521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18043934761199495872525445 3383237767724905476098521)
                    ·
                      refine ⟨2537428325793679107073891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383237767724905476098521 2537428325793679107073891)
                      ·
                        rfl

theorem cell23_4941624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_4941624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941624 prefixEnd_4941624 := by exact prefixLift 4941624
  have htrace : WordTrace (prefixWord ++ tailWord_4941624) baseStart_4941624 baseEnd_4941624 := by
    simpa [prefixWord, tailWord_4941624, baseEnd_4941624] using wordTrace_append hprefix tailTrace_4941624
  have hstable : (prefixWord ++ tailWord_4941624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941624).length < 2 ^ (prefixWord ++ tailWord_4941624).sum := by decide
  have hdescent : baseEnd_4941624 < baseStart_4941624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941690 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_4941690 : Nat := 118140960795 + 4941690 * 2 ^ 59
def prefixEnd_4941690 : Nat := 4983230072969 + 3 ^ 40 * 4941690 * 2
def baseEnd_4941690 : Nat := 845820738505625282949529

theorem tailTrace_4941690 : CollatzResearch.WordTrace tailWord_4941690 prefixEnd_4941690 845820738505625282949529 := by
  unfold tailWord_4941690
  simp only [CollatzResearch.WordTrace]
  refine ⟨45059560366777144576237631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120158827644739052203300349 45059560366777144576237631)
  ·
    refine ⟨67589340550165716864356447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45059560366777144576237631 67589340550165716864356447)
    ·
      refine ⟨101384010825248575296534671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67589340550165716864356447 101384010825248575296534671)
      ·
        refine ⟨152076016237872862944802007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101384010825248575296534671 152076016237872862944802007)
        ·
          refine ⟨228114024356809294417203011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152076016237872862944802007 228114024356809294417203011)
          ·
            refine ⟨342171036535213941625804517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228114024356809294417203011 342171036535213941625804517)
            ·
              refine ⟨64157069350352614054838347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 342171036535213941625804517 64157069350352614054838347)
              ·
                refine ⟨96235604025528921082257521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64157069350352614054838347 96235604025528921082257521)
                ·
                  refine ⟨72176703019146690811693141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96235604025528921082257521 72176703019146690811693141)
                  ·
                    refine ⟨845820738505625282949529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72176703019146690811693141 845820738505625282949529)
                    ·
                      rfl

theorem cell23_4941690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_4941690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941690 prefixEnd_4941690 := by exact prefixLift 4941690
  have htrace : WordTrace (prefixWord ++ tailWord_4941690) baseStart_4941690 baseEnd_4941690 := by
    simpa [prefixWord, tailWord_4941690, baseEnd_4941690] using wordTrace_append hprefix tailTrace_4941690
  have hstable : (prefixWord ++ tailWord_4941690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941690).length < 2 ^ (prefixWord ++ tailWord_4941690).sum := by decide
  have hdescent : baseEnd_4941690 < baseStart_4941690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941758 : List Nat := [4, 2, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_4941758 : Nat := 118140960795 + 4941758 * 2 ^ 59
def prefixEnd_4941758 : Nat := 4983230072969 + 3 ^ 40 * 4941758 * 2
def baseEnd_4941758 : Nat := 845832377400460527599425

theorem tailTrace_4941758 : CollatzResearch.WordTrace tailWord_4941758 prefixEnd_4941758 845832377400460527599425 := by
  unfold tailWord_4941758
  simp only [CollatzResearch.WordTrace]
  refine ⟨22530090203857778239803241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120160481087241483945617285 22530090203857778239803241)
  ·
    refine ⟨16897567652893333679852431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22530090203857778239803241 16897567652893333679852431)
    ·
      refine ⟨25346351479340000519778647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16897567652893333679852431 25346351479340000519778647)
      ·
        refine ⟨38019527219010000779667971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25346351479340000519778647 38019527219010000779667971)
        ·
          refine ⟨57029290828515001169501957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38019527219010000779667971 57029290828515001169501957)
          ·
            refine ⟨10692992030346562719281617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57029290828515001169501957 10692992030346562719281617)
            ·
              refine ⟨8019744022759922039461213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10692992030346562719281617 8019744022759922039461213)
              ·
                refine ⟨3007404008534970764797955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8019744022759922039461213 3007404008534970764797955)
                ·
                  refine ⟨4511106012802456147196933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007404008534970764797955 4511106012802456147196933)
                  ·
                    refine ⟨845832377400460527599425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4511106012802456147196933 845832377400460527599425)
                    ·
                      rfl

theorem cell23_4941758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_4941758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941758 prefixEnd_4941758 := by exact prefixLift 4941758
  have htrace : WordTrace (prefixWord ++ tailWord_4941758) baseStart_4941758 baseEnd_4941758 := by
    simpa [prefixWord, tailWord_4941758, baseEnd_4941758] using wordTrace_append hprefix tailTrace_4941758
  have hstable : (prefixWord ++ tailWord_4941758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941758).length < 2 ^ (prefixWord ++ tailWord_4941758).sum := by decide
  have hdescent : baseEnd_4941758 < baseStart_4941758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941781 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4941781 : Nat := 118140960795 + 4941781 * 2 ^ 59
def prefixEnd_4941781 : Nat := 4983230072969 + 3 ^ 40 * 4941781 * 2
def baseEnd_4941781 : Nat := 2537508942256434992810669

theorem tailTrace_4941781 : CollatzResearch.WordTrace tailWord_4941781 prefixEnd_4941781 2537508942256434992810669 := by
  unfold tailWord_4941781
  simp only [CollatzResearch.WordTrace]
  refine ⟨180241560509778900846513197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120161040339852600564342131 180241560509778900846513197)
  ·
    refine ⟨67590585191167087817442449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180241560509778900846513197 67590585191167087817442449)
    ·
      refine ⟨50692938893375315863081837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67590585191167087817442449 50692938893375315863081837)
      ·
        refine ⟨19009852085015743448655689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50692938893375315863081837 19009852085015743448655689)
        ·
          refine ⟨14257389063761807586491767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19009852085015743448655689 14257389063761807586491767)
          ·
            refine ⟨21386083595642711379737651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14257389063761807586491767 21386083595642711379737651)
            ·
              refine ⟨32079125393464067069606477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21386083595642711379737651 32079125393464067069606477)
              ·
                refine ⟨12029672022549025151102429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32079125393464067069606477 12029672022549025151102429)
                ·
                  refine ⟨4511127008455884431663411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12029672022549025151102429 4511127008455884431663411)
                  ·
                    refine ⟨6766690512683826647495117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4511127008455884431663411 6766690512683826647495117)
                    ·
                      refine ⟨2537508942256434992810669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6766690512683826647495117 2537508942256434992810669)
                      ·
                        rfl

theorem cell23_4941781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4941781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941781 prefixEnd_4941781 := by exact prefixLift 4941781
  have htrace : WordTrace (prefixWord ++ tailWord_4941781) baseStart_4941781 baseEnd_4941781 := by
    simpa [prefixWord, tailWord_4941781, baseEnd_4941781] using wordTrace_append hprefix tailTrace_4941781
  have hstable : (prefixWord ++ tailWord_4941781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941781).length < 2 ^ (prefixWord ++ tailWord_4941781).sum := by decide
  have hdescent : baseEnd_4941781 < baseStart_4941781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941807 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_4941807 : Nat := 118140960795 + 4941807 * 2 ^ 59
def prefixEnd_4941807 : Nat := 4983230072969 + 3 ^ 40 * 4941807 * 2
def baseEnd_4941807 : Nat := 2537522292753451891085549

theorem tailTrace_4941807 : CollatzResearch.WordTrace tailWord_4941807 prefixEnd_4941807 2537522292753451891085549 := by
  unfold tailWord_4941807
  simp only [CollatzResearch.WordTrace]
  refine ⟨180242508807684707286959675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120161672538456471524639783 180242508807684707286959675)
  ·
    refine ⟨270363763211527060930439513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180242508807684707286959675 270363763211527060930439513)
    ·
      refine ⟨202772822408645295697829635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270363763211527060930439513 202772822408645295697829635)
      ·
        refine ⟨304159233612967943546744453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202772822408645295697829635 304159233612967943546744453)
        ·
          refine ⟨57029856302431489415014585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304159233612967943546744453 57029856302431489415014585)
          ·
            refine ⟨42772392226823617061260939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57029856302431489415014585 42772392226823617061260939)
            ·
              refine ⟨64158588340235425591891409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42772392226823617061260939 64158588340235425591891409)
              ·
                refine ⟨48118941255176569193918557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64158588340235425591891409 48118941255176569193918557)
                ·
                  refine ⟨18044602970691213447719459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48118941255176569193918557 18044602970691213447719459)
                  ·
                    refine ⟨27066904456036820171579189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18044602970691213447719459 27066904456036820171579189)
                    ·
                      refine ⟨2537522292753451891085549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27066904456036820171579189 2537522292753451891085549)
                      ·
                        rfl

theorem cell23_4941807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_4941807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941807 prefixEnd_4941807 := by exact prefixLift 4941807
  have htrace : WordTrace (prefixWord ++ tailWord_4941807) baseStart_4941807 baseEnd_4941807 := by
    simpa [prefixWord, tailWord_4941807, baseEnd_4941807] using wordTrace_append hprefix tailTrace_4941807
  have hstable : (prefixWord ++ tailWord_4941807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941807).length < 2 ^ (prefixWord ++ tailWord_4941807).sum := by decide
  have hdescent : baseEnd_4941807 < baseStart_4941807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941821 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_4941821 : Nat := 118140960795 + 4941821 * 2 ^ 59
def prefixEnd_4941821 : Nat := 4983230072969 + 3 ^ 40 * 4941821 * 2
def baseEnd_4941821 : Nat := 2537529481482614836310485

theorem tailTrace_4941821 : CollatzResearch.WordTrace tailWord_4941821 prefixEnd_4941821 2537529481482614836310485 := by
  unfold tailWord_4941821
  simp only [CollatzResearch.WordTrace]
  refine ⟨180243019429633987677969317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120162012953089325118646211 180243019429633987677969317)
  ·
    refine ⟨33795566143056372689619247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180243019429633987677969317 33795566143056372689619247)
    ·
      refine ⟨50693349214584559034428871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33795566143056372689619247 50693349214584559034428871)
      ·
        refine ⟨76040023821876838551643307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50693349214584559034428871 76040023821876838551643307)
        ·
          refine ⟨114060035732815257827464961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76040023821876838551643307 114060035732815257827464961)
          ·
            refine ⟨85545026799611443370598721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114060035732815257827464961 85545026799611443370598721)
            ·
              refine ⟨64158770099708582527949041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85545026799611443370598721 64158770099708582527949041)
              ·
                refine ⟨48119077574781436895961781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64158770099708582527949041 48119077574781436895961781)
                ·
                  refine ⟨4511163522635759708996417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48119077574781436895961781 4511163522635759708996417)
                  ·
                    refine ⟨3383372641976819781747313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4511163522635759708996417 3383372641976819781747313)
                    ·
                      refine ⟨2537529481482614836310485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383372641976819781747313 2537529481482614836310485)
                      ·
                        rfl

theorem cell23_4941821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_4941821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941821 prefixEnd_4941821 := by exact prefixLift 4941821
  have htrace : WordTrace (prefixWord ++ tailWord_4941821) baseStart_4941821 baseEnd_4941821 := by
    simpa [prefixWord, tailWord_4941821, baseEnd_4941821] using wordTrace_append hprefix tailTrace_4941821
  have hstable : (prefixWord ++ tailWord_4941821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941821).length < 2 ^ (prefixWord ++ tailWord_4941821).sum := by decide
  have hdescent : baseEnd_4941821 < baseStart_4941821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941867 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 5]
def baseStart_4941867 : Nat := 118140960795 + 4941867 * 2 ^ 59
def prefixEnd_4941867 : Nat := 4983230072969 + 3 ^ 40 * 4941867 * 2
def baseEnd_4941867 : Nat := 2537553101592721656335273

theorem tailTrace_4941867 : CollatzResearch.WordTrace tailWord_4941867 prefixEnd_4941867 2537553101592721656335273 := by
  unfold tailWord_4941867
  simp only [CollatzResearch.WordTrace]
  refine ⟨180244697187467337534143855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120163131458311558356095903 180244697187467337534143855)
  ·
    refine ⟨270367045781201006301215783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180244697187467337534143855 270367045781201006301215783)
    ·
      refine ⟨405550568671801509451823675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270367045781201006301215783 405550568671801509451823675)
      ·
        refine ⟨608325853007702264177735513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405550568671801509451823675 608325853007702264177735513)
        ·
          refine ⟨456244389755776698133301635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608325853007702264177735513 456244389755776698133301635)
          ·
            refine ⟨684366584633665047199952453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456244389755776698133301635 684366584633665047199952453)
            ·
              refine ⟨128318734618812196349991085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 684366584633665047199952453 128318734618812196349991085)
              ·
                refine ⟨48119525482054573631246657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128318734618812196349991085 48119525482054573631246657)
                ·
                  refine ⟨36089644111540930223434993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48119525482054573631246657 36089644111540930223434993)
                  ·
                    refine ⟨27067233083655697667576245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36089644111540930223434993 27067233083655697667576245)
                    ·
                      refine ⟨2537553101592721656335273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27067233083655697667576245 2537553101592721656335273)
                      ·
                        rfl

theorem cell23_4941867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_4941867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941867 prefixEnd_4941867 := by exact prefixLift 4941867
  have htrace : WordTrace (prefixWord ++ tailWord_4941867) baseStart_4941867 baseEnd_4941867 := by
    simpa [prefixWord, tailWord_4941867, baseEnd_4941867] using wordTrace_append hprefix tailTrace_4941867
  have hstable : (prefixWord ++ tailWord_4941867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941867).length < 2 ^ (prefixWord ++ tailWord_4941867).sum := by decide
  have hdescent : baseEnd_4941867 < baseStart_4941867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941888 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 2, 1, 3]
def baseStart_4941888 : Nat := 118140960795 + 4941888 * 2 ^ 59
def prefixEnd_4941888 : Nat := 4983230072969 + 3 ^ 40 * 4941888 * 2
def baseEnd_4941888 : Nat := 2537563884686466074172677

theorem tailTrace_4941888 : CollatzResearch.WordTrace tailWord_4941888 prefixEnd_4941888 2537563884686466074172677 := by
  unfold tailWord_4941888
  simp only [CollatzResearch.WordTrace]
  refine ⟨90122731560195629060329159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120163642080260838747105545 90122731560195629060329159)
  ·
    refine ⟨135184097340293443590493739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90122731560195629060329159 135184097340293443590493739)
    ·
      refine ⟨202776146010440165385740609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135184097340293443590493739 202776146010440165385740609)
      ·
        refine ⟨152082109507830124039305457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202776146010440165385740609 152082109507830124039305457)
        ·
          refine ⟨114061582130872593029479093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152082109507830124039305457 114061582130872593029479093)
          ·
            refine ⟨10693273324769305596513665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114061582130872593029479093 10693273324769305596513665)
            ·
              refine ⟨8019954993576979197385249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10693273324769305596513665 8019954993576979197385249)
              ·
                refine ⟨6014966245182734398038937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8019954993576979197385249 6014966245182734398038937)
                ·
                  refine ⟨4511224683887050798529203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6014966245182734398038937 4511224683887050798529203)
                  ·
                    refine ⟨6766837025830576197793805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4511224683887050798529203 6766837025830576197793805)
                    ·
                      refine ⟨2537563884686466074172677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6766837025830576197793805 2537563884686466074172677)
                      ·
                        rfl

theorem cell23_4941888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_4941888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941888 prefixEnd_4941888 := by exact prefixLift 4941888
  have htrace : WordTrace (prefixWord ++ tailWord_4941888) baseStart_4941888 baseEnd_4941888 := by
    simpa [prefixWord, tailWord_4941888, baseEnd_4941888] using wordTrace_append hprefix tailTrace_4941888
  have hstable : (prefixWord ++ tailWord_4941888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941888).length < 2 ^ (prefixWord ++ tailWord_4941888).sum := by decide
  have hdescent : baseEnd_4941888 < baseStart_4941888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941889 : List Nat := [1, 2, 5, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_4941889 : Nat := 118140960795 + 4941889 * 2 ^ 59
def prefixEnd_4941889 : Nat := 4983230072969 + 3 ^ 40 * 4941889 * 2
def baseEnd_4941889 : Nat := 2537564398167120570260173

theorem tailTrace_4941889 : CollatzResearch.WordTrace tailWord_4941889 prefixEnd_4941889 2537564398167120570260173 := by
  unfold tailWord_4941889
  simp only [CollatzResearch.WordTrace]
  refine ⟨180245499593387635291444721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120163666395591756860963147 180245499593387635291444721)
  ·
    refine ⟨135184124695040726468583541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180245499593387635291444721 135184124695040726468583541)
    ·
      refine ⟨12673511690160068106429707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135184124695040726468583541 12673511690160068106429707)
      ·
        refine ⟨19010267535240102159644561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12673511690160068106429707 19010267535240102159644561)
        ·
          refine ⟨14257700651430076619733421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19010267535240102159644561 14257700651430076619733421)
          ·
            refine ⟨5346637744286278732400033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14257700651430076619733421 5346637744286278732400033)
            ·
              refine ⟨4009978308214709049300025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5346637744286278732400033 4009978308214709049300025)
              ·
                refine ⟨3007483731161031786975019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4009978308214709049300025 3007483731161031786975019)
                ·
                  refine ⟨4511225596741547680462529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007483731161031786975019 4511225596741547680462529)
                  ·
                    refine ⟨3383419197556160760346897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4511225596741547680462529 3383419197556160760346897)
                    ·
                      refine ⟨2537564398167120570260173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383419197556160760346897 2537564398167120570260173)
                      ·
                        rfl

theorem cell23_4941889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_4941889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941889 prefixEnd_4941889 := by exact prefixLift 4941889
  have htrace : WordTrace (prefixWord ++ tailWord_4941889) baseStart_4941889 baseEnd_4941889 := by
    simpa [prefixWord, tailWord_4941889, baseEnd_4941889] using wordTrace_append hprefix tailTrace_4941889
  have hstable : (prefixWord ++ tailWord_4941889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941889).length < 2 ^ (prefixWord ++ tailWord_4941889).sum := by decide
  have hdescent : baseEnd_4941889 < baseStart_4941889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941911 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 1, 4, 2]
def baseStart_4941911 : Nat := 118140960795 + 4941911 * 2 ^ 59
def prefixEnd_4941911 : Nat := 4983230072969 + 3 ^ 40 * 4941911 * 2
def baseEnd_4941911 : Nat := 2537575694741519484185071

theorem tailTrace_4941911 : CollatzResearch.WordTrace tailWord_4941911 prefixEnd_4941911 2537575694741519484185071 := by
  unfold tailWord_4941911
  simp only [CollatzResearch.WordTrace]
  refine ⟨180246301999307933048745587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120164201332871955365830391 180246301999307933048745587)
  ·
    refine ⟨270369452998961899573118381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180246301999307933048745587 270369452998961899573118381)
    ·
      refine ⟨101388544874610712339919393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270369452998961899573118381 101388544874610712339919393)
      ·
        refine ⟨76041408655958034254939545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101388544874610712339919393 76041408655958034254939545)
        ·
          refine ⟨57031056491968525691204659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76041408655958034254939545 57031056491968525691204659)
          ·
            refine ⟨85546584737952788536806989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57031056491968525691204659 85546584737952788536806989)
            ·
              refine ⟨32079969276732295701302621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85546584737952788536806989 32079969276732295701302621)
              ·
                refine ⟨12029988478774610887988483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32079969276732295701302621 12029988478774610887988483)
                ·
                  refine ⟨18044982718161916331982725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12029988478774610887988483 18044982718161916331982725)
                  ·
                    refine ⟨3383434259655359312246761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18044982718161916331982725 3383434259655359312246761)
                    ·
                      refine ⟨2537575694741519484185071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383434259655359312246761 2537575694741519484185071)
                      ·
                        rfl

theorem cell23_4941911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_4941911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941911 prefixEnd_4941911 := by exact prefixLift 4941911
  have htrace : WordTrace (prefixWord ++ tailWord_4941911) baseStart_4941911 baseEnd_4941911 := by
    simpa [prefixWord, tailWord_4941911, baseEnd_4941911] using wordTrace_append hprefix tailTrace_4941911
  have hstable : (prefixWord ++ tailWord_4941911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941911).length < 2 ^ (prefixWord ++ tailWord_4941911).sum := by decide
  have hdescent : baseEnd_4941911 < baseStart_4941911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941914 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_4941914 : Nat := 118140960795 + 4941914 * 2 ^ 59
def prefixEnd_4941914 : Nat := 4983230072969 + 3 ^ 40 * 4941914 * 2
def baseEnd_4941914 : Nat := 2537577235183482972447557

theorem tailTrace_4941914 : CollatzResearch.WordTrace tailWord_4941914 prefixEnd_4941914 2537577235183482972447557 := by
  unfold tailWord_4941914
  simp only [CollatzResearch.WordTrace]
  refine ⟨45061602854574266140276199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120164274278864709707403197 45061602854574266140276199)
  ·
    refine ⟨67592404281861399210414299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45061602854574266140276199 67592404281861399210414299)
    ·
      refine ⟨101388606422792098815621449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67592404281861399210414299 101388606422792098815621449)
      ·
        refine ⟨76041454817094074111716087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101388606422792098815621449 76041454817094074111716087)
        ·
          refine ⟨114062182225641111167574131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76041454817094074111716087 114062182225641111167574131)
          ·
            refine ⟨171093273338461666751361197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114062182225641111167574131 171093273338461666751361197)
            ·
              refine ⟨64159977501923125031760449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171093273338461666751361197 64159977501923125031760449)
              ·
                refine ⟨48119983126442343773820337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64159977501923125031760449 48119983126442343773820337)
                ·
                  refine ⟨36089987344831757830365253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48119983126442343773820337 36089987344831757830365253)
                  ·
                    refine ⟨6766872627155954593193485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36089987344831757830365253 6766872627155954593193485)
                    ·
                      refine ⟨2537577235183482972447557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6766872627155954593193485 2537577235183482972447557)
                      ·
                        rfl

theorem cell23_4941914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_4941914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941914 prefixEnd_4941914 := by exact prefixLift 4941914
  have htrace : WordTrace (prefixWord ++ tailWord_4941914) baseStart_4941914 baseEnd_4941914 := by
    simpa [prefixWord, tailWord_4941914, baseEnd_4941914] using wordTrace_append hprefix tailTrace_4941914
  have hstable : (prefixWord ++ tailWord_4941914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941914).length < 2 ^ (prefixWord ++ tailWord_4941914).sum := by decide
  have hdescent : baseEnd_4941914 < baseStart_4941914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941934 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_4941934 : Nat := 118140960795 + 4941934 * 2 ^ 59
def prefixEnd_4941934 : Nat := 4983230072969 + 3 ^ 40 * 4941934 * 2
def baseEnd_4941934 : Nat := 281954167199619210466385

theorem tailTrace_4941934 : CollatzResearch.WordTrace tailWord_4941934 prefixEnd_4941934 281954167199619210466385 := by
  unfold tailWord_4941934
  simp only [CollatzResearch.WordTrace]
  refine ⟨22530892609778075997104107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120164760585483071984555237 22530892609778075997104107)
  ·
    refine ⟨33796338914667113995656161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22530892609778075997104107 33796338914667113995656161)
    ·
      refine ⟨25347254186000335496742121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33796338914667113995656161 25347254186000335496742121)
      ·
        refine ⟨19010440639500251622556591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25347254186000335496742121 19010440639500251622556591)
        ·
          refine ⟨28515660959250377433834887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19010440639500251622556591 28515660959250377433834887)
          ·
            refine ⟨42773491438875566150752331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28515660959250377433834887 42773491438875566150752331)
            ·
              refine ⟨64160237158313349226128497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42773491438875566150752331 64160237158313349226128497)
              ·
                refine ⟨48120177868735011919596373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64160237158313349226128497 48120177868735011919596373)
                ·
                  refine ⟨281954167199619210466385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48120177868735011919596373 281954167199619210466385)
                  ·
                    rfl

theorem cell23_4941934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_4941934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941934 prefixEnd_4941934 := by exact prefixLift 4941934
  have htrace : WordTrace (prefixWord ++ tailWord_4941934) baseStart_4941934 baseEnd_4941934 := by
    simpa [prefixWord, tailWord_4941934, baseEnd_4941934] using wordTrace_append hprefix tailTrace_4941934
  have hstable : (prefixWord ++ tailWord_4941934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941934).length < 2 ^ (prefixWord ++ tailWord_4941934).sum := by decide
  have hdescent : baseEnd_4941934 < baseStart_4941934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941945 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 2, 2, 2]
def baseStart_4941945 : Nat := 118140960795 + 4941945 * 2 ^ 59
def prefixEnd_4941945 : Nat := 4983230072969 + 3 ^ 40 * 4941945 * 2
def baseEnd_4941945 : Nat := 2537593153083772351159915

theorem tailTrace_4941945 : CollatzResearch.WordTrace tailWord_4941945 prefixEnd_4941945 2537593153083772351159915 := by
  unfold tailWord_4941945
  simp only [CollatzResearch.WordTrace]
  refine ⟨180247542081184756855483289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120165028054123171236988859 180247542081184756855483289)
  ·
    refine ⟨135185656560888567641612467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180247542081184756855483289 135185656560888567641612467)
    ·
      refine ⟨202778484841332851462418701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135185656560888567641612467 202778484841332851462418701)
      ·
        refine ⟨76041931815499819298407013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202778484841332851462418701 76041931815499819298407013)
        ·
          refine ⟨14257862215406216118451315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76041931815499819298407013 14257862215406216118451315)
          ·
            refine ⟨21386793323109324177676973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14257862215406216118451315 21386793323109324177676973)
            ·
              refine ⟨8020047496165996566628865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21386793323109324177676973 8020047496165996566628865)
              ·
                refine ⟨6015035622124497424971649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8020047496165996566628865 6015035622124497424971649)
                ·
                  refine ⟨4511276716593373068728737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6015035622124497424971649 4511276716593373068728737)
                  ·
                    refine ⟨3383457537445029801546553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4511276716593373068728737 3383457537445029801546553)
                    ·
                      refine ⟨2537593153083772351159915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383457537445029801546553 2537593153083772351159915)
                      ·
                        rfl

theorem cell23_4941945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_4941945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941945 prefixEnd_4941945 := by exact prefixLift 4941945
  have htrace : WordTrace (prefixWord ++ tailWord_4941945) baseStart_4941945 baseEnd_4941945 := by
    simpa [prefixWord, tailWord_4941945, baseEnd_4941945] using wordTrace_append hprefix tailTrace_4941945
  have hstable : (prefixWord ++ tailWord_4941945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941945).length < 2 ^ (prefixWord ++ tailWord_4941945).sum := by decide
  have hdescent : baseEnd_4941945 < baseStart_4941945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4941962 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_4941962 : Nat := 118140960795 + 4941962 * 2 ^ 59
def prefixEnd_4941962 : Nat := 4983230072969 + 3 ^ 40 * 4941962 * 2
def baseEnd_4941962 : Nat := 2537601882254898784647337

theorem tailTrace_4941962 : CollatzResearch.WordTrace tailWord_4941962 prefixEnd_4941962 2537601882254898784647337 := by
  unfold tailWord_4941962
  simp only [CollatzResearch.WordTrace]
  refine ⟨45062040530530792189713035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120165441414748779172568093 45062040530530792189713035)
  ·
    refine ⟨67593060795796188284569553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45062040530530792189713035 67593060795796188284569553)
    ·
      refine ⟨50694795596847141213427165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67593060795796188284569553 50694795596847141213427165)
      ·
        refine ⟨19010548348817677955035187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50694795596847141213427165 19010548348817677955035187)
        ·
          refine ⟨28515822523226516932552781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19010548348817677955035187 28515822523226516932552781)
          ·
            refine ⟨10693433446209943849707293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28515822523226516932552781 10693433446209943849707293)
            ·
              refine ⟨4010037542328728943640235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10693433446209943849707293 4010037542328728943640235)
              ·
                refine ⟨6015056313493093415460353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010037542328728943640235 6015056313493093415460353)
                ·
                  refine ⟨4511292235119820061595265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6015056313493093415460353 4511292235119820061595265)
                  ·
                    refine ⟨3383469176339865046196449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4511292235119820061595265 3383469176339865046196449)
                    ·
                      refine ⟨2537601882254898784647337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383469176339865046196449 2537601882254898784647337)
                      ·
                        rfl

theorem cell23_4941962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_4941962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4941962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4941962 prefixEnd_4941962 := by exact prefixLift 4941962
  have htrace : WordTrace (prefixWord ++ tailWord_4941962) baseStart_4941962 baseEnd_4941962 := by
    simpa [prefixWord, tailWord_4941962, baseEnd_4941962] using wordTrace_append hprefix tailTrace_4941962
  have hstable : (prefixWord ++ tailWord_4941962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4941962).length < 2 ^ (prefixWord ++ tailWord_4941962).sum := by decide
  have hdescent : baseEnd_4941962 < baseStart_4941962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4941962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942064 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_4942064 : Nat := 118140960795 + 4942064 * 2 ^ 59
def prefixEnd_4942064 : Nat := 4983230072969 + 3 ^ 40 * 4942064 * 2
def baseEnd_4942064 : Nat := 2537654257281657385571867

theorem tailTrace_4942064 : CollatzResearch.WordTrace tailWord_4942064 prefixEnd_4942064 2537654257281657385571867 := by
  unfold tailWord_4942064
  simp only [CollatzResearch.WordTrace]
  refine ⟨90125941183876820089532623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120167921578502426786043497 90125941183876820089532623)
  ·
    refine ⟨135188911775815230134298935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90125941183876820089532623 135188911775815230134298935)
    ·
      refine ⟨202783367663722845201448403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135188911775815230134298935 202783367663722845201448403)
      ·
        refine ⟨304175051495584267802172605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202783367663722845201448403 304175051495584267802172605)
        ·
          refine ⟨114065644310844100425814727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304175051495584267802172605 114065644310844100425814727)
          ·
            refine ⟨171098466466266150638722091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114065644310844100425814727 171098466466266150638722091)
            ·
              refine ⟨256647699699399225958083137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171098466466266150638722091 256647699699399225958083137)
              ·
                refine ⟨192485774774549419468562353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256647699699399225958083137 192485774774549419468562353)
                ·
                  refine ⟨144364331080912064601421765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192485774774549419468562353 144364331080912064601421765)
                  ·
                    refine ⟨27068312077671012112766581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144364331080912064601421765 27068312077671012112766581)
                    ·
                      refine ⟨2537654257281657385571867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27068312077671012112766581 2537654257281657385571867)
                      ·
                        rfl

theorem cell23_4942064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_4942064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942064 prefixEnd_4942064 := by exact prefixLift 4942064
  have htrace : WordTrace (prefixWord ++ tailWord_4942064) baseStart_4942064 baseEnd_4942064 := by
    simpa [prefixWord, tailWord_4942064, baseEnd_4942064] using wordTrace_append hprefix tailTrace_4942064
  have hstable : (prefixWord ++ tailWord_4942064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942064).length < 2 ^ (prefixWord ++ tailWord_4942064).sum := by decide
  have hdescent : baseEnd_4942064 < baseStart_4942064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942091 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 4]
def baseStart_4942091 : Nat := 118140960795 + 4942091 * 2 ^ 59
def prefixEnd_4942091 : Nat := 4983230072969 + 3 ^ 40 * 4942091 * 2
def baseEnd_4942091 : Nat := 2537668121259328779934243

theorem tailTrace_4942091 : CollatzResearch.WordTrace tailWord_4942091 prefixEnd_4942091 2537668121259328779934243 := by
  unfold tailWord_4942091
  simp only [CollatzResearch.WordTrace]
  refine ⟨180252867138655823790298127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120168578092437215860198751 180252867138655823790298127)
  ·
    refine ⟨270379300707983735685447191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180252867138655823790298127 270379300707983735685447191)
    ·
      refine ⟨405568951061975603528170787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270379300707983735685447191 405568951061975603528170787)
      ·
        refine ⟨608353426592963405292256181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405568951061975603528170787 608353426592963405292256181)
        ·
          refine ⟨57033133743090319246149017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 608353426592963405292256181 57033133743090319246149017)
          ·
            refine ⟨42774850307317739434611763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57033133743090319246149017 42774850307317739434611763)
            ·
              refine ⟨64162275460976609151917645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42774850307317739434611763 64162275460976609151917645)
              ·
                refine ⟨24060853297866228431969117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64162275460976609151917645 24060853297866228431969117)
                ·
                  refine ⟨9022819986699835661988419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24060853297866228431969117 9022819986699835661988419)
                  ·
                    refine ⟨13534229980049753492982629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9022819986699835661988419 13534229980049753492982629)
                    ·
                      refine ⟨2537668121259328779934243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13534229980049753492982629 2537668121259328779934243)
                      ·
                        rfl

theorem cell23_4942091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 4].length) (baseStart_4942091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942091 prefixEnd_4942091 := by exact prefixLift 4942091
  have htrace : WordTrace (prefixWord ++ tailWord_4942091) baseStart_4942091 baseEnd_4942091 := by
    simpa [prefixWord, tailWord_4942091, baseEnd_4942091] using wordTrace_append hprefix tailTrace_4942091
  have hstable : (prefixWord ++ tailWord_4942091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942091).length < 2 ^ (prefixWord ++ tailWord_4942091).sum := by decide
  have hdescent : baseEnd_4942091 < baseStart_4942091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942101 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_4942101 : Nat := 118140960795 + 4942101 * 2 ^ 59
def prefixEnd_4942101 : Nat := 4983230072969 + 3 ^ 40 * 4942101 * 2
def baseEnd_4942101 : Nat := 845891085355291246936399

theorem tailTrace_4942101 : CollatzResearch.WordTrace tailWord_4942101 prefixEnd_4942101 845891085355291246936399 := by
  unfold tailWord_4942101
  simp only [CollatzResearch.WordTrace]
  refine ⟨180253231868619595498162157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120168821245746396998774771 180253231868619595498162157)
  ·
    refine ⟨67594961950732348311810809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180253231868619595498162157 67594961950732348311810809)
    ·
      refine ⟨50696221463049261233858107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67594961950732348311810809 50696221463049261233858107)
      ·
        refine ⟨76044332194573891850787161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50696221463049261233858107 76044332194573891850787161)
        ·
          refine ⟨57033249145930418888090371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76044332194573891850787161 57033249145930418888090371)
          ·
            refine ⟨85549873718895628332135557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57033249145930418888090371 85549873718895628332135557)
            ·
              refine ⟨16040601322292930312275417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85549873718895628332135557 16040601322292930312275417)
              ·
                refine ⟨12030450991719697734206563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16040601322292930312275417 12030450991719697734206563)
                ·
                  refine ⟨18045676487579546601309845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12030450991719697734206563 18045676487579546601309845)
                  ·
                    refine ⟨845891085355291246936399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18045676487579546601309845 845891085355291246936399)
                    ·
                      rfl

theorem cell23_4942101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_4942101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942101 prefixEnd_4942101 := by exact prefixLift 4942101
  have htrace : WordTrace (prefixWord ++ tailWord_4942101) baseStart_4942101 baseEnd_4942101 := by
    simpa [prefixWord, tailWord_4942101, baseEnd_4942101] using wordTrace_append hprefix tailTrace_4942101
  have hstable : (prefixWord ++ tailWord_4942101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942101).length < 2 ^ (prefixWord ++ tailWord_4942101).sum := by decide
  have hdescent : baseEnd_4942101 < baseStart_4942101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942138 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_4942138 : Nat := 118140960795 + 4942138 * 2 ^ 59
def prefixEnd_4942138 : Nat := 4983230072969 + 3 ^ 40 * 4942138 * 2
def baseEnd_4942138 : Nat := 2537692254850090096046527

theorem tailTrace_4942138 : CollatzResearch.WordTrace tailWord_4942138 prefixEnd_4942138 2537692254850090096046527 := by
  unfold tailWord_4942138
  simp only [CollatzResearch.WordTrace]
  refine ⟨45063645342371387704314767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120169720912990367211506045 45063645342371387704314767)
  ·
    refine ⟨67595468013557081556472151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45063645342371387704314767 67595468013557081556472151)
    ·
      refine ⟨101393202020335622334708227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67595468013557081556472151 101393202020335622334708227)
      ·
        refine ⟨152089803030503433502062341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101393202020335622334708227 152089803030503433502062341)
        ·
          refine ⟨28516838068219393781636689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152089803030503433502062341 28516838068219393781636689)
          ·
            refine ⟨21387628551164545336227517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28516838068219393781636689 21387628551164545336227517)
            ·
              refine ⟨8020360706686704501085319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21387628551164545336227517 8020360706686704501085319)
              ·
                refine ⟨12030541060030056751627979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8020360706686704501085319 12030541060030056751627979)
                ·
                  refine ⟨18045811590045085127441969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12030541060030056751627979 18045811590045085127441969)
                  ·
                    refine ⟨13534358692533813845581477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18045811590045085127441969 13534358692533813845581477)
                    ·
                      refine ⟨2537692254850090096046527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13534358692533813845581477 2537692254850090096046527)
                      ·
                        rfl

theorem cell23_4942138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_4942138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942138 prefixEnd_4942138 := by exact prefixLift 4942138
  have htrace : WordTrace (prefixWord ++ tailWord_4942138) baseStart_4942138 baseEnd_4942138 := by
    simpa [prefixWord, tailWord_4942138, baseEnd_4942138] using wordTrace_append hprefix tailTrace_4942138
  have hstable : (prefixWord ++ tailWord_4942138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942138).length < 2 ^ (prefixWord ++ tailWord_4942138).sum := by decide
  have hdescent : baseEnd_4942138 < baseStart_4942138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942142 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_4942142 : Nat := 118140960795 + 4942142 * 2 ^ 59
def prefixEnd_4942142 : Nat := 4983230072969 + 3 ^ 40 * 4942142 * 2
def baseEnd_4942142 : Nat := 2537694308772708080396509

theorem tailTrace_4942142 : CollatzResearch.WordTrace tailWord_4942142 prefixEnd_4942142 2537694308772708080396509 := by
  unfold tailWord_4942142
  simp only [CollatzResearch.WordTrace]
  refine ⟨22531840907683882437550585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120169818174314039666936453 22531840907683882437550585)
  ·
    refine ⟨16898880680762911828162939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22531840907683882437550585 16898880680762911828162939)
    ·
      refine ⟨25348321021144367742244409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16898880680762911828162939 25348321021144367742244409)
      ·
        refine ⟨19011240765858275806683307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25348321021144367742244409 19011240765858275806683307)
        ·
          refine ⟨28516861148787413710024961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19011240765858275806683307 28516861148787413710024961)
          ·
            refine ⟨21387645861590560282518721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28516861148787413710024961 21387645861590560282518721)
            ·
              refine ⟨16040734396192920211889041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21387645861590560282518721 16040734396192920211889041)
              ·
                refine ⟨12030550797144690158916781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16040734396192920211889041 12030550797144690158916781)
                ·
                  refine ⟨4511456548929258809593793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12030550797144690158916781 4511456548929258809593793)
                  ·
                    refine ⟨3383592411696944107195345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4511456548929258809593793 3383592411696944107195345)
                    ·
                      refine ⟨2537694308772708080396509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383592411696944107195345 2537694308772708080396509)
                      ·
                        rfl

theorem cell23_4942142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_4942142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942142 prefixEnd_4942142 := by exact prefixLift 4942142
  have htrace : WordTrace (prefixWord ++ tailWord_4942142) baseStart_4942142 baseEnd_4942142 := by
    simpa [prefixWord, tailWord_4942142, baseEnd_4942142] using wordTrace_append hprefix tailTrace_4942142
  have hstable : (prefixWord ++ tailWord_4942142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942142).length < 2 ^ (prefixWord ++ tailWord_4942142).sum := by decide
  have hdescent : baseEnd_4942142 < baseStart_4942142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4942176 : List Nat := [2, 1, 1, 3, 5, 1, 3, 2, 1, 2, 2]
def baseStart_4942176 : Nat := 118140960795 + 4942176 * 2 ^ 59
def prefixEnd_4942176 : Nat := 4983230072969 + 3 ^ 40 * 4942176 * 2
def baseEnd_4942176 : Nat := 2537711767114960947371353

theorem tailTrace_4942176 : CollatzResearch.WordTrace tailWord_4942176 prefixEnd_4942176 2537711767114960947371353 := by
  unfold tailWord_4942176
  simp only [CollatzResearch.WordTrace]
  refine ⟨90127983671673941653571191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120170644895565255538094921 90127983671673941653571191)
  ·
    refine ⟨135191975507510912480356787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90127983671673941653571191 135191975507510912480356787)
    ·
      refine ⟨202787963261266368720535181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135191975507510912480356787 202787963261266368720535181)
      ·
        refine ⟨76045486222974888270200693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202787963261266368720535181 76045486222974888270200693)
        ·
          refine ⟨7129264333403895775331315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76045486222974888270200693 7129264333403895775331315)
          ·
            refine ⟨10693896500105843662996973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7129264333403895775331315 10693896500105843662996973)
            ·
              refine ⟨4010211187539691373623865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10693896500105843662996973 4010211187539691373623865)
              ·
                refine ⟨3007658390654768530217899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4010211187539691373623865 3007658390654768530217899)
                ·
                  refine ⟨4511487585982152795326849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007658390654768530217899 4511487585982152795326849)
                  ·
                    refine ⟨3383615689486614596495137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4511487585982152795326849 3383615689486614596495137)
                    ·
                      refine ⟨2537711767114960947371353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3383615689486614596495137 2537711767114960947371353)
                      ·
                        rfl

theorem cell23_4942176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_4942176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4942176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4942176 prefixEnd_4942176 := by exact prefixLift 4942176
  have htrace : WordTrace (prefixWord ++ tailWord_4942176) baseStart_4942176 baseEnd_4942176 := by
    simpa [prefixWord, tailWord_4942176, baseEnd_4942176] using wordTrace_append hprefix tailTrace_4942176
  have hstable : (prefixWord ++ tailWord_4942176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4942176).length < 2 ^ (prefixWord ++ tailWord_4942176).sum := by decide
  have hdescent : baseEnd_4942176 < baseStart_4942176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4942176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
