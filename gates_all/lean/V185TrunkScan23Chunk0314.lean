import V185TrunkScan23Chunk0313

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1857433 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 3, 4]
def baseStart_1857433 : Nat := 118140960795 + 1857433 * 2 ^ 59
def prefixEnd_1857433 : Nat := 4983230072969 + 3 ^ 40 * 1857433 * 2
def baseEnd_1857433 : Nat := 317918637507578839515109

theorem tailTrace_1857433 : CollatzResearch.WordTrace tailWord_1857433 prefixEnd_1857433 317918637507578839515109 := by
  unfold tailWord_1857433
  simp only [CollatzResearch.WordTrace]
  refine ⟨67746147079844940145992953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45164098053229960097328635 67746147079844940145992953)
  ·
    refine ⟨50809610309883705109494715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67746147079844940145992953 50809610309883705109494715)
    ·
      refine ⟨76214415464825557664242073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50809610309883705109494715 76214415464825557664242073)
      ·
        refine ⟨57160811598619168248181555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76214415464825557664242073 57160811598619168248181555)
        ·
          refine ⟨85741217397928752372272333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57160811598619168248181555 85741217397928752372272333)
          ·
            refine ⟨32152956524223282139602125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85741217397928752372272333 32152956524223282139602125)
            ·
              refine ⟨12057358696583730802350797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32152956524223282139602125 12057358696583730802350797)
              ·
                refine ⟨4521509511218899050881549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12057358696583730802350797 4521509511218899050881549)
                ·
                  refine ⟨1695566066707087144080581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4521509511218899050881549 1695566066707087144080581)
                  ·
                    refine ⟨317918637507578839515109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695566066707087144080581 317918637507578839515109)
                    ·
                      rfl

theorem cell23_1857433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 4].length) (baseStart_1857433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857433 prefixEnd_1857433 := by exact prefixLift 1857433
  have htrace : WordTrace (prefixWord ++ tailWord_1857433) baseStart_1857433 baseEnd_1857433 := by
    simpa [prefixWord, tailWord_1857433, baseEnd_1857433] using wordTrace_append hprefix tailTrace_1857433
  have hstable : (prefixWord ++ tailWord_1857433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857433).length < 2 ^ (prefixWord ++ tailWord_1857433).sum := by decide
  have hdescent : baseEnd_1857433 < baseStart_1857433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857466 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1857466 : Nat := 118140960795 + 1857466 * 2 ^ 59
def prefixEnd_1857466 : Nat := 4983230072969 + 3 ^ 40 * 1857466 * 2
def baseEnd_1857466 : Nat := 953772857384334889432675

theorem tailTrace_1857466 : CollatzResearch.WordTrace tailWord_1857466 prefixEnd_1857466 953772857384334889432675 := by
  unfold tailWord_1857466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16936837672181346695486063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45164900459150257854629501 16936837672181346695486063)
  ·
    refine ⟨25405256508272020043229095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16936837672181346695486063 25405256508272020043229095)
    ·
      refine ⟨38107884762408030064843643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25405256508272020043229095 38107884762408030064843643)
      ·
        refine ⟨57161827143612045097265465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38107884762408030064843643 57161827143612045097265465)
        ·
          refine ⟨42871370357709033822949099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57161827143612045097265465 42871370357709033822949099)
          ·
            refine ⟨64307055536563550734423649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42871370357709033822949099 64307055536563550734423649)
            ·
              refine ⟨48230291652422663050817737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64307055536563550734423649 48230291652422663050817737)
              ·
                refine ⟨36172718739316997288113303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48230291652422663050817737 36172718739316997288113303)
                ·
                  refine ⟨54259078108975495932169955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36172718739316997288113303 54259078108975495932169955)
                  ·
                    refine ⟨81388617163463243898254933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54259078108975495932169955 81388617163463243898254933)
                    ·
                      refine ⟨953772857384334889432675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 81388617163463243898254933 953772857384334889432675)
                      ·
                        rfl

theorem cell23_1857466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1857466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857466 prefixEnd_1857466 := by exact prefixLift 1857466
  have htrace : WordTrace (prefixWord ++ tailWord_1857466) baseStart_1857466 baseEnd_1857466 := by
    simpa [prefixWord, tailWord_1857466, baseEnd_1857466] using wordTrace_append hprefix tailTrace_1857466
  have hstable : (prefixWord ++ tailWord_1857466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857466).length < 2 ^ (prefixWord ++ tailWord_1857466).sum := by decide
  have hdescent : baseEnd_1857466 < baseStart_1857466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857484 : List Nat := [2, 2, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_1857484 : Nat := 118140960795 + 1857484 * 2 ^ 59
def prefixEnd_1857484 : Nat := 4983230072969 + 3 ^ 40 * 1857484 * 2
def baseEnd_1857484 : Nat := 317927366678705273002531

theorem tailTrace_1857484 : CollatzResearch.WordTrace tailWord_1857484 prefixEnd_1857484 317927366678705273002531 := by
  unfold tailWord_1857484
  simp only [CollatzResearch.WordTrace]
  refine ⟨33874003601330087928049753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45165338135106783904066337 33874003601330087928049753)
  ·
    refine ⟨25405502700997565946037315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33874003601330087928049753 25405502700997565946037315)
    ·
      refine ⟨38108254051496348919055973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25405502700997565946037315 38108254051496348919055973)
      ·
        refine ⟨7145297634655565422322995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38108254051496348919055973 7145297634655565422322995)
        ·
          refine ⟨10717946451983348133484493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145297634655565422322995 10717946451983348133484493)
          ·
            refine ⟨4019229919493755550056685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10717946451983348133484493 4019229919493755550056685)
            ·
              refine ⟨1507211219810158331271257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4019229919493755550056685 1507211219810158331271257)
              ·
                refine ⟨1130408414857618748453443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507211219810158331271257 1130408414857618748453443)
                ·
                  refine ⟨1695612622286428122680165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130408414857618748453443 1695612622286428122680165)
                  ·
                    refine ⟨317927366678705273002531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695612622286428122680165 317927366678705273002531)
                    ·
                      rfl

theorem cell23_1857484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_1857484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857484 prefixEnd_1857484 := by exact prefixLift 1857484
  have htrace : WordTrace (prefixWord ++ tailWord_1857484) baseStart_1857484 baseEnd_1857484 := by
    simpa [prefixWord, tailWord_1857484, baseEnd_1857484] using wordTrace_append hprefix tailTrace_1857484
  have hstable : (prefixWord ++ tailWord_1857484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857484).length < 2 ^ (prefixWord ++ tailWord_1857484).sum := by decide
  have hdescent : baseEnd_1857484 < baseStart_1857484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857497 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 6]
def baseStart_1857497 : Nat := 118140960795 + 1857497 * 2 ^ 59
def prefixEnd_1857497 : Nat := 4983230072969 + 3 ^ 40 * 1857497 * 2
def baseEnd_1857497 : Nat := 105976530587180474238337

theorem tailTrace_1857497 : CollatzResearch.WordTrace tailWord_1857497 prefixEnd_1857497 105976530587180474238337 := by
  unfold tailWord_1857497
  simp only [CollatzResearch.WordTrace]
  refine ⟨67748481351613079076322745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45165654234408719384215163 67748481351613079076322745)
  ·
    refine ⟨50811361013709809307242059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67748481351613079076322745 50811361013709809307242059)
    ·
      refine ⟨76217041520564713960863089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50811361013709809307242059 76217041520564713960863089)
      ·
        refine ⟨57162781140423535470647317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76217041520564713960863089 57162781140423535470647317)
        ·
          refine ⟨2679505365957353225186593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57162781140423535470647317 2679505365957353225186593)
          ·
            refine ⟨2009629024468014918889945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679505365957353225186593 2009629024468014918889945)
            ·
              refine ⟨1507221768351011189167459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009629024468014918889945 1507221768351011189167459)
              ·
                refine ⟨2260832652526516783751189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507221768351011189167459 2260832652526516783751189)
                ·
                  refine ⟨105976530587180474238337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2260832652526516783751189 105976530587180474238337)
                  ·
                    rfl

theorem cell23_1857497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 6].length) (baseStart_1857497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857497 prefixEnd_1857497 := by exact prefixLift 1857497
  have htrace : WordTrace (prefixWord ++ tailWord_1857497) baseStart_1857497 baseEnd_1857497 := by
    simpa [prefixWord, tailWord_1857497, baseEnd_1857497] using wordTrace_append hprefix tailTrace_1857497
  have hstable : (prefixWord ++ tailWord_1857497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857497).length < 2 ^ (prefixWord ++ tailWord_1857497).sum := by decide
  have hdescent : baseEnd_1857497 < baseStart_1857497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857523 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 6, 4]
def baseStart_1857523 : Nat := 118140960795 + 1857523 * 2 ^ 59
def prefixEnd_1857523 : Nat := 4983230072969 + 3 ^ 40 * 1857523 * 2
def baseEnd_1857523 : Nat := 317934041927213722139971

theorem tailTrace_1857523 : CollatzResearch.WordTrace tailWord_1857523 prefixEnd_1857523 317934041927213722139971 := by
  unfold tailWord_1857523
  simp only [CollatzResearch.WordTrace]
  refine ⟨67749429649518885516769223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45166286433012590344512815 67749429649518885516769223)
  ·
    refine ⟨101624144474278328275153835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67749429649518885516769223 101624144474278328275153835)
    ·
      refine ⟨152436216711417492412730753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101624144474278328275153835 152436216711417492412730753)
      ·
        refine ⟨114327162533563119309548065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152436216711417492412730753 114327162533563119309548065)
        ·
          refine ⟨85745371900172339482161049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114327162533563119309548065 85745371900172339482161049)
          ·
            refine ⟨64309028925129254611620787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85745371900172339482161049 64309028925129254611620787)
            ·
              refine ⟨96463543387693881917431181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64309028925129254611620787 96463543387693881917431181)
              ·
                refine ⟨36173828770385205719036693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96463543387693881917431181 36173828770385205719036693)
                ·
                  refine ⟨1695648223611806518079845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36173828770385205719036693 1695648223611806518079845)
                  ·
                    refine ⟨317934041927213722139971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695648223611806518079845 317934041927213722139971)
                    ·
                      rfl

theorem cell23_1857523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 4].length) (baseStart_1857523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857523 prefixEnd_1857523 := by exact prefixLift 1857523
  have htrace : WordTrace (prefixWord ++ tailWord_1857523) baseStart_1857523 baseEnd_1857523 := by
    simpa [prefixWord, tailWord_1857523, baseEnd_1857523] using wordTrace_append hprefix tailTrace_1857523
  have hstable : (prefixWord ++ tailWord_1857523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857523).length < 2 ^ (prefixWord ++ tailWord_1857523).sum := by decide
  have hdescent : baseEnd_1857523 < baseStart_1857523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857534 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1857534 : Nat := 118140960795 + 1857534 * 2 ^ 59
def prefixEnd_1857534 : Nat := 4983230072969 + 3 ^ 40 * 1857534 * 2
def baseEnd_1857534 : Nat := 953807774068840623382363

theorem tailTrace_1857534 : CollatzResearch.WordTrace tailWord_1857534 prefixEnd_1857534 953807774068840623382363 := by
  unfold tailWord_1857534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8468728856559879299427457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45166553901652689596946437 8468728856559879299427457)
  ·
    refine ⟨6351546642419909474570593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8468728856559879299427457 6351546642419909474570593)
    ·
      refine ⟨4763659981814932105927945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6351546642419909474570593 4763659981814932105927945)
      ·
        refine ⟨3572744986361199079445959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4763659981814932105927945 3572744986361199079445959)
        ·
          refine ⟨5359117479541798619168939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572744986361199079445959 5359117479541798619168939)
          ·
            refine ⟨8038676219312697928753409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359117479541798619168939 8038676219312697928753409)
            ·
              refine ⟨6029007164484523446565057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8038676219312697928753409 6029007164484523446565057)
              ·
                refine ⟨4521755373363392584923793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6029007164484523446565057 4521755373363392584923793)
                ·
                  refine ⟨3391316530022544438692845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4521755373363392584923793 3391316530022544438692845)
                  ·
                    refine ⟨1271743698758454164509817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3391316530022544438692845 1271743698758454164509817)
                    ·
                      refine ⟨953807774068840623382363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271743698758454164509817 953807774068840623382363)
                      ·
                        rfl

theorem cell23_1857534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1857534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857534 prefixEnd_1857534 := by exact prefixLift 1857534
  have htrace : WordTrace (prefixWord ++ tailWord_1857534) baseStart_1857534 baseEnd_1857534 := by
    simpa [prefixWord, tailWord_1857534, baseEnd_1857534] using wordTrace_append hprefix tailTrace_1857534
  have hstable : (prefixWord ++ tailWord_1857534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857534).length < 2 ^ (prefixWord ++ tailWord_1857534).sum := by decide
  have hdescent : baseEnd_1857534 < baseStart_1857534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857541 : List Nat := [1, 3, 1, 1, 2, 6, 2, 2, 1, 1, 3]
def baseStart_1857541 : Nat := 118140960795 + 1857541 * 2 ^ 59
def prefixEnd_1857541 : Nat := 4983230072969 + 3 ^ 40 * 1857541 * 2
def baseEnd_1857541 : Nat := 953811368433422095994831

theorem tailTrace_1857541 : CollatzResearch.WordTrace tailWord_1857541 prefixEnd_1857541 953811368433422095994831 := by
  unfold tailWord_1857541
  simp only [CollatzResearch.WordTrace]
  refine ⟨67750086163453674590924477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45166724108969116393949651 67750086163453674590924477)
  ·
    refine ⟨25406282311295127971596679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67750086163453674590924477 25406282311295127971596679)
    ·
      refine ⟨38109423466942691957395019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25406282311295127971596679 38109423466942691957395019)
      ·
        refine ⟨57164135200414037936092529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38109423466942691957395019 57164135200414037936092529)
        ·
          refine ⟨42873101400310528452069397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57164135200414037936092529 42873101400310528452069397)
          ·
            refine ⟨2009676628139556021190753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42873101400310528452069397 2009676628139556021190753)
            ·
              refine ⟨1507257471104667015893065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009676628139556021190753 1507257471104667015893065)
              ·
                refine ⟨1130443103328500261919799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507257471104667015893065 1130443103328500261919799)
                ·
                  refine ⟨1695664654992750392879699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130443103328500261919799 1695664654992750392879699)
                  ·
                    refine ⟨2543496982489125589319549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1695664654992750392879699 2543496982489125589319549)
                    ·
                      refine ⟨953811368433422095994831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2543496982489125589319549 953811368433422095994831)
                      ·
                        rfl

theorem cell23_1857541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_1857541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857541 prefixEnd_1857541 := by exact prefixLift 1857541
  have htrace : WordTrace (prefixWord ++ tailWord_1857541) baseStart_1857541 baseEnd_1857541 := by
    simpa [prefixWord, tailWord_1857541, baseEnd_1857541] using wordTrace_append hprefix tailTrace_1857541
  have hstable : (prefixWord ++ tailWord_1857541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857541).length < 2 ^ (prefixWord ++ tailWord_1857541).sum := by decide
  have hdescent : baseEnd_1857541 < baseStart_1857541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857547 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 3, 2, 2]
def baseStart_1857547 : Nat := 118140960795 + 1857547 * 2 ^ 59
def prefixEnd_1857547 : Nat := 4983230072969 + 3 ^ 40 * 1857547 * 2
def baseEnd_1857547 : Nat := 953814449317349072519803

theorem tailTrace_1857547 : CollatzResearch.WordTrace tailWord_1857547 prefixEnd_1857547 953814449317349072519803 := by
  unfold tailWord_1857547
  simp only [CollatzResearch.WordTrace]
  refine ⟨67750305001431937615642895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45166870000954625077095263 67750305001431937615642895)
  ·
    refine ⟨101625457502147906423464343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67750305001431937615642895 101625457502147906423464343)
    ·
      refine ⟨152438186253221859635196515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101625457502147906423464343 152438186253221859635196515)
      ·
        refine ⟨228657279379832789452794773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152438186253221859635196515 228657279379832789452794773)
        ·
          refine ⟨10718309970929662005599755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228657279379832789452794773 10718309970929662005599755)
          ·
            refine ⟨16077464956394493008399633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10718309970929662005599755 16077464956394493008399633)
            ·
              refine ⟨12058098717295869756299725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16077464956394493008399633 12058098717295869756299725)
              ·
                refine ⟨4521787018985951158612397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12058098717295869756299725 4521787018985951158612397)
                ·
                  refine ⟨1695670132119731684479649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4521787018985951158612397 1695670132119731684479649)
                  ·
                    refine ⟨1271752599089798763359737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1695670132119731684479649 1271752599089798763359737)
                    ·
                      refine ⟨953814449317349072519803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271752599089798763359737 953814449317349072519803)
                      ·
                        rfl

theorem cell23_1857547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 2, 2].length) (baseStart_1857547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857547 prefixEnd_1857547 := by exact prefixLift 1857547
  have htrace : WordTrace (prefixWord ++ tailWord_1857547) baseStart_1857547 baseEnd_1857547 := by
    simpa [prefixWord, tailWord_1857547, baseEnd_1857547] using wordTrace_append hprefix tailTrace_1857547
  have hstable : (prefixWord ++ tailWord_1857547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857547).length < 2 ^ (prefixWord ++ tailWord_1857547).sum := by decide
  have hdescent : baseEnd_1857547 < baseStart_1857547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857550 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1857550 : Nat := 118140960795 + 1857550 * 2 ^ 59
def prefixEnd_1857550 : Nat := 4983230072969 + 3 ^ 40 * 1857550 * 2
def baseEnd_1857550 : Nat := 953815989759312560782289

theorem tailTrace_1857550 : CollatzResearch.WordTrace tailWord_1857550 prefixEnd_1857550 953815989759312560782289 := by
  unfold tailWord_1857550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8468801802552633641000263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45166942946947379418668069 8468801802552633641000263)
  ·
    refine ⟨12703202703828950461500395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8468801802552633641000263 12703202703828950461500395)
    ·
      refine ⟨19054804055743425692250593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12703202703828950461500395 19054804055743425692250593)
      ·
        refine ⟨14291103041807569269187945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19054804055743425692250593 14291103041807569269187945)
        ·
          refine ⟨10718327281355676951890959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14291103041807569269187945 10718327281355676951890959)
          ·
            refine ⟨16077490922033515427836439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10718327281355676951890959 16077490922033515427836439)
            ·
              refine ⟨24116236383050273141754659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16077490922033515427836439 24116236383050273141754659)
              ·
                refine ⟨36174354574575409712631989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24116236383050273141754659 36174354574575409712631989)
                ·
                  refine ⟨3391345741366444660559249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36174354574575409712631989 3391345741366444660559249)
                  ·
                    refine ⟨2543509306024833495419437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3391345741366444660559249 2543509306024833495419437)
                    ·
                      refine ⟨953815989759312560782289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2543509306024833495419437 953815989759312560782289)
                      ·
                        rfl

theorem cell23_1857550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1857550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857550 prefixEnd_1857550 := by exact prefixLift 1857550
  have htrace : WordTrace (prefixWord ++ tailWord_1857550) baseStart_1857550 baseEnd_1857550 := by
    simpa [prefixWord, tailWord_1857550, baseEnd_1857550] using wordTrace_append hprefix tailTrace_1857550
  have hstable : (prefixWord ++ tailWord_1857550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857550).length < 2 ^ (prefixWord ++ tailWord_1857550).sum := by decide
  have hdescent : baseEnd_1857550 < baseStart_1857550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857560 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1857560 : Nat := 118140960795 + 1857560 * 2 ^ 59
def prefixEnd_1857560 : Nat := 4983230072969 + 3 ^ 40 * 1857560 * 2
def baseEnd_1857560 : Nat := 953821124565857521657243

theorem tailTrace_1857560 : CollatzResearch.WordTrace tailWord_1857560 prefixEnd_1857560 953821124565857521657243 := by
  unfold tailWord_1857560
  simp only [CollatzResearch.WordTrace]
  refine ⟨33875389575192420417933067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45167186100256560557244089 33875389575192420417933067)
  ·
    refine ⟨50813084362788630626899601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33875389575192420417933067 50813084362788630626899601)
    ·
      refine ⟨38109813272091472970174701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50813084362788630626899601 38109813272091472970174701)
      ·
        refine ⟨14291179977034302363815513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38109813272091472970174701 14291179977034302363815513)
        ·
          refine ⟨10718384982775726772861635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14291179977034302363815513 10718384982775726772861635)
          ·
            refine ⟨16077577474163590159292453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10718384982775726772861635 16077577474163590159292453)
            ·
              refine ⟨3014545776405673154867335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16077577474163590159292453 3014545776405673154867335)
              ·
                refine ⟨4521818664608509732301003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014545776405673154867335 4521818664608509732301003)
                ·
                  refine ⟨6782727996912764598451505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521818664608509732301003 6782727996912764598451505)
                  ·
                    refine ⟨5087045997684573448838629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6782727996912764598451505 5087045997684573448838629)
                    ·
                      refine ⟨953821124565857521657243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5087045997684573448838629 953821124565857521657243)
                      ·
                        rfl

theorem cell23_1857560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1857560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857560 prefixEnd_1857560 := by exact prefixLift 1857560
  have htrace : WordTrace (prefixWord ++ tailWord_1857560) baseStart_1857560 baseEnd_1857560 := by
    simpa [prefixWord, tailWord_1857560, baseEnd_1857560] using wordTrace_append hprefix tailTrace_1857560
  have hstable : (prefixWord ++ tailWord_1857560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857560).length < 2 ^ (prefixWord ++ tailWord_1857560).sum := by decide
  have hdescent : baseEnd_1857560 < baseStart_1857560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857564 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_1857564 : Nat := 118140960795 + 1857564 * 2 ^ 59
def prefixEnd_1857564 : Nat := 4983230072969 + 3 ^ 40 * 1857564 * 2
def baseEnd_1857564 : Nat := 953823178488475506007225

theorem tailTrace_1857564 : CollatzResearch.WordTrace tailWord_1857564 prefixEnd_1857564 953823178488475506007225 := by
  unfold tailWord_1857564
  simp only [CollatzResearch.WordTrace]
  refine ⟨33875462521185174759505873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45167283361580233012674497 33875462521185174759505873)
  ·
    refine ⟨25406596890888881069629405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33875462521185174759505873 25406596890888881069629405)
    ·
      refine ⟨9527473834083330401111027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25406596890888881069629405 9527473834083330401111027)
      ·
        refine ⟨14291210751124995601666541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9527473834083330401111027 14291210751124995601666541)
        ·
          refine ⟨5359204031671873350624953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14291210751124995601666541 5359204031671873350624953)
          ·
            refine ⟨4019403023753905012968715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5359204031671873350624953 4019403023753905012968715)
            ·
              refine ⟨6029104535630857519453073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019403023753905012968715 6029104535630857519453073)
              ·
                refine ⟨4521828401723143139589805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6029104535630857519453073 4521828401723143139589805)
                ·
                  refine ⟨1695685650646178677346177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4521828401723143139589805 1695685650646178677346177)
                  ·
                    refine ⟨1271764237984634008009633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1695685650646178677346177 1271764237984634008009633)
                    ·
                      refine ⟨953823178488475506007225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271764237984634008009633 953823178488475506007225)
                      ·
                        rfl

theorem cell23_1857564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_1857564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857564 prefixEnd_1857564 := by exact prefixLift 1857564
  have htrace : WordTrace (prefixWord ++ tailWord_1857564) baseStart_1857564 baseEnd_1857564 := by
    simpa [prefixWord, tailWord_1857564, baseEnd_1857564] using wordTrace_append hprefix tailTrace_1857564
  have hstable : (prefixWord ++ tailWord_1857564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857564).length < 2 ^ (prefixWord ++ tailWord_1857564).sum := by decide
  have hdescent : baseEnd_1857564 < baseStart_1857564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857570 : List Nat := [3, 3, 1, 1, 1, 2, 5, 7]
def baseStart_1857570 : Nat := 118140960795 + 1857570 * 2 ^ 59
def prefixEnd_1857570 : Nat := 4983230072969 + 3 ^ 40 * 1857570 * 2
def baseEnd_1857570 : Nat := 35326898495274166019711

theorem tailTrace_1857570 : CollatzResearch.WordTrace tailWord_1857570 prefixEnd_1857570 35326898495274166019711 := by
  unfold tailWord_1857570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16937785970087153135932541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45167429253565741695820109 16937785970087153135932541)
  ·
    refine ⟨6351669738782682425974703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16937785970087153135932541 6351669738782682425974703)
    ·
      refine ⟨9527504608174023638962055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351669738782682425974703 9527504608174023638962055)
      ·
        refine ⟨14291256912261035458443083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9527504608174023638962055 14291256912261035458443083)
        ·
          refine ⟨21436885368391553187664625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14291256912261035458443083 21436885368391553187664625)
          ·
            refine ⟨16077664026293664890748469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21436885368391553187664625 16077664026293664890748469)
            ·
              refine ⟨1507281002465031083507669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16077664026293664890748469 1507281002465031083507669)
              ·
                refine ⟨35326898495274166019711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1507281002465031083507669 35326898495274166019711)
                ·
                  rfl

theorem cell23_1857570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 7].length) (baseStart_1857570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857570 prefixEnd_1857570 := by exact prefixLift 1857570
  have htrace : WordTrace (prefixWord ++ tailWord_1857570) baseStart_1857570 baseEnd_1857570 := by
    simpa [prefixWord, tailWord_1857570, baseEnd_1857570] using wordTrace_append hprefix tailTrace_1857570
  have hstable : (prefixWord ++ tailWord_1857570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857570).length < 2 ^ (prefixWord ++ tailWord_1857570).sum := by decide
  have hdescent : baseEnd_1857570 < baseStart_1857570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857584 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 1, 2, 3]
def baseStart_1857584 : Nat := 118140960795 + 1857584 * 2 ^ 59
def prefixEnd_1857584 : Nat := 4983230072969 + 3 ^ 40 * 1857584 * 2
def baseEnd_1857584 : Nat := 953833448101565427757133

theorem tailTrace_1857584 : CollatzResearch.WordTrace tailWord_1857584 prefixEnd_1857584 953833448101565427757133 := by
  unfold tailWord_1857584
  simp only [CollatzResearch.WordTrace]
  refine ⟨33875827251148946467369903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45167769668198595289826537 33875827251148946467369903)
  ·
    refine ⟨50813740876723419701054855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33875827251148946467369903 50813740876723419701054855)
    ·
      refine ⟨76220611315085129551582283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50813740876723419701054855 76220611315085129551582283)
      ·
        refine ⟨114330916972627694327373425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76220611315085129551582283 114330916972627694327373425)
        ·
          refine ⟨85748187729470770745530069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114330916972627694327373425 85748187729470770745530069)
          ·
            refine ⟨2009723149909471189348361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85748187729470770745530069 2009723149909471189348361)
            ·
              refine ⟨1507292362432103392011271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009723149909471189348361 1507292362432103392011271)
              ·
                refine ⟨2260938543648155088016907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507292362432103392011271 2260938543648155088016907)
                ·
                  refine ⟨3391407815472232632025361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260938543648155088016907 3391407815472232632025361)
                  ·
                    refine ⟨2543555861604174474019021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3391407815472232632025361 2543555861604174474019021)
                    ·
                      refine ⟨953833448101565427757133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2543555861604174474019021 953833448101565427757133)
                      ·
                        rfl

theorem cell23_1857584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 2, 3].length) (baseStart_1857584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857584 prefixEnd_1857584 := by exact prefixLift 1857584
  have htrace : WordTrace (prefixWord ++ tailWord_1857584) baseStart_1857584 baseEnd_1857584 := by
    simpa [prefixWord, tailWord_1857584, baseEnd_1857584] using wordTrace_append hprefix tailTrace_1857584
  have hstable : (prefixWord ++ tailWord_1857584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857584).length < 2 ^ (prefixWord ++ tailWord_1857584).sum := by decide
  have hdescent : baseEnd_1857584 < baseStart_1857584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857597 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1857597 : Nat := 118140960795 + 1857597 * 2 ^ 59
def prefixEnd_1857597 : Nat := 4983230072969 + 3 ^ 40 * 1857597 * 2
def baseEnd_1857597 : Nat := 953840123350073876894573

theorem tailTrace_1857597 : CollatzResearch.WordTrace tailWord_1857597 prefixEnd_1857597 953840123350073876894573 := by
  unfold tailWord_1857597
  simp only [CollatzResearch.WordTrace]
  refine ⟨67752128651250796154963045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45168085767500530769975363 67752128651250796154963045)
  ·
    refine ⟨12703524122109524279055571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67752128651250796154963045 12703524122109524279055571)
    ·
      refine ⟨19055286183164286418583357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12703524122109524279055571 19055286183164286418583357)
      ·
        refine ⟨7145732318686607406968759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19055286183164286418583357 7145732318686607406968759)
        ·
          refine ⟨10718598478029911110453139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145732318686607406968759 10718598478029911110453139)
          ·
            refine ⟨16077897717044866665679709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10718598478029911110453139 16077897717044866665679709)
            ·
              refine ⟨6029211643891824999629891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16077897717044866665679709 6029211643891824999629891)
              ·
                refine ⟨9043817465837737499444837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029211643891824999629891 9043817465837737499444837)
                ·
                  refine ⟨1695715774844575781145907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9043817465837737499444837 1695715774844575781145907)
                  ·
                    refine ⟨2543573662266863671718861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1695715774844575781145907 2543573662266863671718861)
                    ·
                      refine ⟨953840123350073876894573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2543573662266863671718861 953840123350073876894573)
                      ·
                        rfl

theorem cell23_1857597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1857597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857597 prefixEnd_1857597 := by exact prefixLift 1857597
  have htrace : WordTrace (prefixWord ++ tailWord_1857597) baseStart_1857597 baseEnd_1857597 := by
    simpa [prefixWord, tailWord_1857597, baseEnd_1857597] using wordTrace_append hprefix tailTrace_1857597
  have hstable : (prefixWord ++ tailWord_1857597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857597).length < 2 ^ (prefixWord ++ tailWord_1857597).sum := by decide
  have hdescent : baseEnd_1857597 < baseStart_1857597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857603 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 4]
def baseStart_1857603 : Nat := 118140960795 + 1857603 * 2 ^ 59
def prefixEnd_1857603 : Nat := 4983230072969 + 3 ^ 40 * 1857603 * 2
def baseEnd_1857603 : Nat := 953843204234000853419545

theorem tailTrace_1857603 : CollatzResearch.WordTrace tailWord_1857603 prefixEnd_1857603 953843204234000853419545 := by
  unfold tailWord_1857603
  simp only [CollatzResearch.WordTrace]
  refine ⟨67752347489229059179681463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45168231659486039453120975 67752347489229059179681463)
  ·
    refine ⟨101628521233843588769522195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67752347489229059179681463 101628521233843588769522195)
    ·
      refine ⟨152442781850765383154283293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101628521233843588769522195 152442781850765383154283293)
      ·
        refine ⟨57166043194037018682856235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152442781850765383154283293 57166043194037018682856235)
        ·
          refine ⟨85749064791055528024284353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57166043194037018682856235 85749064791055528024284353)
          ·
            refine ⟨64311798593291646018213265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85749064791055528024284353 64311798593291646018213265)
            ·
              refine ⟨48233848944968734513659949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64311798593291646018213265 48233848944968734513659949)
              ·
                refine ⟨18087693354363275442622481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48233848944968734513659949 18087693354363275442622481)
                ·
                  refine ⟨13565770015772456581966861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18087693354363275442622481 13565770015772456581966861)
                  ·
                    refine ⟨5087163755914671218237573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13565770015772456581966861 5087163755914671218237573)
                    ·
                      refine ⟨953843204234000853419545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5087163755914671218237573 953843204234000853419545)
                      ·
                        rfl

theorem cell23_1857603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_1857603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857603 prefixEnd_1857603 := by exact prefixLift 1857603
  have htrace : WordTrace (prefixWord ++ tailWord_1857603) baseStart_1857603 baseEnd_1857603 := by
    simpa [prefixWord, tailWord_1857603, baseEnd_1857603] using wordTrace_append hprefix tailTrace_1857603
  have hstable : (prefixWord ++ tailWord_1857603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857603).length < 2 ^ (prefixWord ++ tailWord_1857603).sum := by decide
  have hdescent : baseEnd_1857603 < baseStart_1857603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857624 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 1, 3, 2]
def baseStart_1857624 : Nat := 118140960795 + 1857624 * 2 ^ 59
def prefixEnd_1857624 : Nat := 4983230072969 + 3 ^ 40 * 1857624 * 2
def baseEnd_1857624 : Nat := 953853987327745271256949

theorem tailTrace_1857624 : CollatzResearch.WordTrace tailWord_1857624 prefixEnd_1857624 953853987327745271256949 := by
  unfold tailWord_1857624
  simp only [CollatzResearch.WordTrace]
  refine ⟨33876556711076489883097963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45168742281435319844130617 33876556711076489883097963)
  ·
    refine ⟨50814835066614734824646945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33876556711076489883097963 50814835066614734824646945)
    ·
      refine ⟨38111126299961051118485209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50814835066614734824646945 38111126299961051118485209)
      ·
        refine ⟨28583344724970788338863907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38111126299961051118485209 28583344724970788338863907)
        ·
          refine ⟨42875017087456182508295861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28583344724970788338863907 42875017087456182508295861)
          ·
            refine ⟨4019532851949017110152737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42875017087456182508295861 4019532851949017110152737)
            ·
              refine ⟨3014649638961762832614553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4019532851949017110152737 3014649638961762832614553)
              ·
                refine ⟨2260987229221322124460915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3014649638961762832614553 2260987229221322124460915)
                ·
                  refine ⟨3391480843831983186691373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260987229221322124460915 3391480843831983186691373)
                  ·
                    refine ⟨1271805316436993695009265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3391480843831983186691373 1271805316436993695009265)
                    ·
                      refine ⟨953853987327745271256949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271805316436993695009265 953853987327745271256949)
                      ·
                        rfl

theorem cell23_1857624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_1857624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857624 prefixEnd_1857624 := by exact prefixLift 1857624
  have htrace : WordTrace (prefixWord ++ tailWord_1857624) baseStart_1857624 baseEnd_1857624 := by
    simpa [prefixWord, tailWord_1857624, baseEnd_1857624] using wordTrace_append hprefix tailTrace_1857624
  have hstable : (prefixWord ++ tailWord_1857624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857624).length < 2 ^ (prefixWord ++ tailWord_1857624).sum := by decide
  have hdescent : baseEnd_1857624 < baseStart_1857624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857660 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 7]
def baseStart_1857660 : Nat := 118140960795 + 1857660 * 2 ^ 59
def prefixEnd_1857660 : Nat := 4983230072969 + 3 ^ 40 * 1857660 * 2
def baseEnd_1857660 : Nat := 105985830292367458934087

theorem tailTrace_1857660 : CollatzResearch.WordTrace tailWord_1857660 prefixEnd_1857660 105985830292367458934087 := by
  unfold tailWord_1857660
  simp only [CollatzResearch.WordTrace]
  refine ⟨33877213225011278957253217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45169617633348371943004289 33877213225011278957253217)
  ·
    refine ⟨25407909918758459217939913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33877213225011278957253217 25407909918758459217939913)
    ·
      refine ⟨19055932439068844413454935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25407909918758459217939913 19055932439068844413454935)
      ·
        refine ⟨28583898658603266620182403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19055932439068844413454935 28583898658603266620182403)
        ·
          refine ⟨42875847987904899930273605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28583898658603266620182403 42875847987904899930273605)
          ·
            refine ⟨8039221497732168736926301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42875847987904899930273605 8039221497732168736926301)
            ·
              refine ⟨3014708061649563276347363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8039221497732168736926301 3014708061649563276347363)
              ·
                refine ⟨4522062092474344914521045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014708061649563276347363 4522062092474344914521045)
                ·
                  refine ⟨105985830292367458934087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4522062092474344914521045 105985830292367458934087)
                  ·
                    rfl

theorem cell23_1857660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_1857660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857660 prefixEnd_1857660 := by exact prefixLift 1857660
  have htrace : WordTrace (prefixWord ++ tailWord_1857660) baseStart_1857660 baseEnd_1857660 := by
    simpa [prefixWord, tailWord_1857660, baseEnd_1857660] using wordTrace_append hprefix tailTrace_1857660
  have hstable : (prefixWord ++ tailWord_1857660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857660).length < 2 ^ (prefixWord ++ tailWord_1857660).sum := by decide
  have hdescent : baseEnd_1857660 < baseStart_1857660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857671 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_1857671 : Nat := 118140960795 + 1857671 * 2 ^ 59
def prefixEnd_1857671 : Nat := 4983230072969 + 3 ^ 40 * 1857671 * 2
def baseEnd_1857671 : Nat := 953878120918506587369233

theorem tailTrace_1857671 : CollatzResearch.WordTrace tailWord_1857671 prefixEnd_1857671 953878120918506587369233 := by
  unfold tailWord_1857671
  simp only [CollatzResearch.WordTrace]
  refine ⟨67754827652982706793156867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45169885101988471195437911 67754827652982706793156867)
  ·
    refine ⟨101632241479474060189735301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67754827652982706793156867 101632241479474060189735301)
    ·
      refine ⟨19056045277401386285575369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101632241479474060189735301 19056045277401386285575369)
      ·
        refine ⟨14292033958051039714181527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19056045277401386285575369 14292033958051039714181527)
        ·
          refine ⟨21438050937076559571272291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14292033958051039714181527 21438050937076559571272291)
          ·
            refine ⟨32157076405614839356908437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21438050937076559571272291 32157076405614839356908437)
            ·
              refine ⟨1507362956513195594855083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32157076405614839356908437 1507362956513195594855083)
              ·
                refine ⟨2261044434769793392282625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507362956513195594855083 2261044434769793392282625)
                ·
                  refine ⟨1695783326077345044211969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2261044434769793392282625 1695783326077345044211969)
                  ·
                    refine ⟨1271837494558008783158977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1695783326077345044211969 1271837494558008783158977)
                    ·
                      refine ⟨953878120918506587369233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271837494558008783158977 953878120918506587369233)
                      ·
                        rfl

theorem cell23_1857671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_1857671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857671 prefixEnd_1857671 := by exact prefixLift 1857671
  have htrace : WordTrace (prefixWord ++ tailWord_1857671) baseStart_1857671 baseEnd_1857671 := by
    simpa [prefixWord, tailWord_1857671, baseEnd_1857671] using wordTrace_append hprefix tailTrace_1857671
  have hstable : (prefixWord ++ tailWord_1857671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857671).length < 2 ^ (prefixWord ++ tailWord_1857671).sum := by decide
  have hdescent : baseEnd_1857671 < baseStart_1857671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857683 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 7]
def baseStart_1857683 : Nat := 118140960795 + 1857683 * 2 ^ 59
def prefixEnd_1857683 : Nat := 4983230072969 + 3 ^ 40 * 1857683 * 2
def baseEnd_1857683 : Nat := 953884282686360540419177

theorem tailTrace_1857683 : CollatzResearch.WordTrace tailWord_1857683 prefixEnd_1857683 953884282686360540419177 := by
  unfold tailWord_1857683
  simp only [CollatzResearch.WordTrace]
  refine ⟨67755265328939232842593703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45170176885959488561729135 67755265328939232842593703)
  ·
    refine ⟨101632897993408849263890555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67755265328939232842593703 101632897993408849263890555)
    ·
      refine ⟨152449346990113273895835833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101632897993408849263890555 152449346990113273895835833)
      ·
        refine ⟨114337010242584955421876875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152449346990113273895835833 114337010242584955421876875)
        ·
          refine ⟨171505515363877433132815313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114337010242584955421876875 171505515363877433132815313)
          ·
            refine ⟨128629136522908074849611485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171505515363877433132815313 128629136522908074849611485)
            ·
              refine ⟨48235926196090528068604307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128629136522908074849611485 48235926196090528068604307)
              ·
                refine ⟨72353889294135792102906461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48235926196090528068604307 72353889294135792102906461)
                ·
                  refine ⟨27132708485300922038589923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72353889294135792102906461 27132708485300922038589923)
                  ·
                    refine ⟨40699062727951383057884885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27132708485300922038589923 40699062727951383057884885)
                    ·
                      refine ⟨953884282686360540419177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40699062727951383057884885 953884282686360540419177)
                      ·
                        rfl

theorem cell23_1857683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_1857683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857683 prefixEnd_1857683 := by exact prefixLift 1857683
  have htrace : WordTrace (prefixWord ++ tailWord_1857683) baseStart_1857683 baseEnd_1857683 := by
    simpa [prefixWord, tailWord_1857683, baseEnd_1857683] using wordTrace_append hprefix tailTrace_1857683
  have hstable : (prefixWord ++ tailWord_1857683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857683).length < 2 ^ (prefixWord ++ tailWord_1857683).sum := by decide
  have hdescent : baseEnd_1857683 < baseStart_1857683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857754 : List Nat := [3, 1, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_1857754 : Nat := 118140960795 + 1857754 * 2 ^ 59
def prefixEnd_1857754 : Nat := 4983230072969 + 3 ^ 40 * 1857754 * 2
def baseEnd_1857754 : Nat := 317973579937609920877117

theorem tailTrace_1857754 : CollatzResearch.WordTrace tailWord_1857754 prefixEnd_1857754 317973579937609920877117 := by
  unfold tailWord_1857754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16939463727920502992107079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45171903274454674645618877 16939463727920502992107079)
  ·
    refine ⟨25409195591880754488160619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16939463727920502992107079 25409195591880754488160619)
    ·
      refine ⟨38113793387821131732240929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25409195591880754488160619 38113793387821131732240929)
      ·
        refine ⟨28585345040865848799180697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38113793387821131732240929 28585345040865848799180697)
        ·
          refine ⟨21439008780649386599385523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28585345040865848799180697 21439008780649386599385523)
          ·
            refine ⟨32158513170974079899078285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21439008780649386599385523 32158513170974079899078285)
            ·
              refine ⟨12059442439115279962154357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32158513170974079899078285 12059442439115279962154357)
              ·
                refine ⟨1130572728667057496451971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12059442439115279962154357 1130572728667057496451971)
                ·
                  refine ⟨1695859093000586244677957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130572728667057496451971 1695859093000586244677957)
                  ·
                    refine ⟨317973579937609920877117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695859093000586244677957 317973579937609920877117)
                    ·
                      rfl

theorem cell23_1857754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_1857754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857754 prefixEnd_1857754 := by exact prefixLift 1857754
  have htrace : WordTrace (prefixWord ++ tailWord_1857754) baseStart_1857754 baseEnd_1857754 := by
    simpa [prefixWord, tailWord_1857754, baseEnd_1857754] using wordTrace_append hprefix tailTrace_1857754
  have hstable : (prefixWord ++ tailWord_1857754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857754).length < 2 ^ (prefixWord ++ tailWord_1857754).sum := by decide
  have hdescent : baseEnd_1857754 < baseStart_1857754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857757 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1857757 : Nat := 118140960795 + 1857757 * 2 ^ 59
def prefixEnd_1857757 : Nat := 4983230072969 + 3 ^ 40 * 1857757 * 2
def baseEnd_1857757 : Nat := 953922280254793250893837

theorem tailTrace_1857757 : CollatzResearch.WordTrace tailWord_1857757 prefixEnd_1857757 953922280254793250893837 := by
  unfold tailWord_1857757
  simp only [CollatzResearch.WordTrace]
  refine ⟨67757964330671143480787525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45171976220447428987191683 67757964330671143480787525)
  ·
    refine ⟨12704618312000839402647661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67757964330671143480787525 12704618312000839402647661)
    ·
      refine ⟨4764231867000314775992873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12704618312000839402647661 4764231867000314775992873)
      ·
        refine ⟨3573173900250236081994655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4764231867000314775992873 3573173900250236081994655)
        ·
          refine ⟨5359760850375354122991983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573173900250236081994655 5359760850375354122991983)
          ·
            refine ⟨8039641275563031184487975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359760850375354122991983 8039641275563031184487975)
            ·
              refine ⟨12059461913344546776731963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039641275563031184487975 12059461913344546776731963)
              ·
                refine ⟨18089192870016820165097945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12059461913344546776731963 18089192870016820165097945)
                ·
                  refine ⟨13566894652512615123823459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18089192870016820165097945 13566894652512615123823459)
                  ·
                    refine ⟨20350341978768922685735189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13566894652512615123823459 20350341978768922685735189)
                    ·
                      refine ⟨953922280254793250893837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20350341978768922685735189 953922280254793250893837)
                      ·
                        rfl

theorem cell23_1857757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1857757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857757 prefixEnd_1857757 := by exact prefixLift 1857757
  have htrace : WordTrace (prefixWord ++ tailWord_1857757) baseStart_1857757 baseEnd_1857757 := by
    simpa [prefixWord, tailWord_1857757, baseEnd_1857757] using wordTrace_append hprefix tailTrace_1857757
  have hstable : (prefixWord ++ tailWord_1857757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857757).length < 2 ^ (prefixWord ++ tailWord_1857757).sum := by decide
  have hdescent : baseEnd_1857757 < baseStart_1857757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857767 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 8]
def baseStart_1857767 : Nat := 118140960795 + 1857767 * 2 ^ 59
def prefixEnd_1857767 : Nat := 4983230072969 + 3 ^ 40 * 1857767 * 2
def baseEnd_1857767 : Nat := 105991935006815356863199

theorem tailTrace_1857767 : CollatzResearch.WordTrace tailWord_1857767 prefixEnd_1857767 105991935006815356863199 := by
  unfold tailWord_1857767
  simp only [CollatzResearch.WordTrace]
  refine ⟨67758329060634915188651555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45172219373756610125767703 67758329060634915188651555)
  ·
    refine ⟨101637493590952372782977333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67758329060634915188651555 101637493590952372782977333)
    ·
      refine ⟨9528515024151784948404125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101637493590952372782977333 9528515024151784948404125)
      ·
        refine ⟨3573193134056919355651547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9528515024151784948404125 3573193134056919355651547)
        ·
          refine ⟨5359789701085379033477321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573193134056919355651547 5359789701085379033477321)
          ·
            refine ⟨4019842275814034275107991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5359789701085379033477321 4019842275814034275107991)
            ·
              refine ⟨6029763413721051412661987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019842275814034275107991 6029763413721051412661987)
              ·
                refine ⟨9044645120581577118992981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029763413721051412661987 9044645120581577118992981)
                ·
                  refine ⟨105991935006815356863199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9044645120581577118992981 105991935006815356863199)
                  ·
                    rfl

theorem cell23_1857767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 8].length) (baseStart_1857767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857767 prefixEnd_1857767 := by exact prefixLift 1857767
  have htrace : WordTrace (prefixWord ++ tailWord_1857767) baseStart_1857767 baseEnd_1857767 := by
    simpa [prefixWord, tailWord_1857767, baseEnd_1857767] using wordTrace_append hprefix tailTrace_1857767
  have hstable : (prefixWord ++ tailWord_1857767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857767).length < 2 ^ (prefixWord ++ tailWord_1857767).sum := by decide
  have hdescent : baseEnd_1857767 < baseStart_1857767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857770 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1857770 : Nat := 118140960795 + 1857770 * 2 ^ 59
def prefixEnd_1857770 : Nat := 4983230072969 + 3 ^ 40 * 1857770 * 2
def baseEnd_1857770 : Nat := 953928955503301700031277

theorem tailTrace_1857770 : CollatzResearch.WordTrace tailWord_1857770 prefixEnd_1857770 953928955503301700031277 := by
  unfold tailWord_1857770
  simp only [CollatzResearch.WordTrace]
  refine ⟨16939609619906011675252691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45172292319749364467340509 16939609619906011675252691)
  ·
    refine ⟨25409414429859017512879037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16939609619906011675252691 25409414429859017512879037)
    ·
      refine ⟨9528530411197131567329639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25409414429859017512879037 9528530411197131567329639)
      ·
        refine ⟨14292795616795697350994459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9528530411197131567329639 14292795616795697350994459)
        ·
          refine ⟨21439193425193546026491689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14292795616795697350994459 21439193425193546026491689)
          ·
            refine ⟨16079395068895159519868767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21439193425193546026491689 16079395068895159519868767)
            ·
              refine ⟨24119092603342739279803151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16079395068895159519868767 24119092603342739279803151)
              ·
                refine ⟨36178638905014108919704727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24119092603342739279803151 36178638905014108919704727)
                ·
                  refine ⟨54267958357521163379557091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36178638905014108919704727 54267958357521163379557091)
                  ·
                    refine ⟨81401937536281745069335637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54267958357521163379557091 81401937536281745069335637)
                    ·
                      refine ⟨953928955503301700031277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 81401937536281745069335637 953928955503301700031277)
                      ·
                        rfl

theorem cell23_1857770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1857770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857770 prefixEnd_1857770 := by exact prefixLift 1857770
  have htrace : WordTrace (prefixWord ++ tailWord_1857770) baseStart_1857770 baseEnd_1857770 := by
    simpa [prefixWord, tailWord_1857770, baseEnd_1857770] using wordTrace_append hprefix tailTrace_1857770
  have hstable : (prefixWord ++ tailWord_1857770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857770).length < 2 ^ (prefixWord ++ tailWord_1857770).sum := by decide
  have hdescent : baseEnd_1857770 < baseStart_1857770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857804 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 2, 3, 2]
def baseStart_1857804 : Nat := 118140960795 + 1857804 * 2 ^ 59
def prefixEnd_1857804 : Nat := 4983230072969 + 3 ^ 40 * 1857804 * 2
def baseEnd_1857804 : Nat := 953946413845554567006121

theorem tailTrace_1857804 : CollatzResearch.WordTrace tailWord_1857804 prefixEnd_1857804 953946413845554567006121 := by
  unfold tailWord_1857804
  simp only [CollatzResearch.WordTrace]
  refine ⟨33879839280750435253874233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45173119041000580338498977 33879839280750435253874233)
  ·
    refine ⟨25409879460562826440405675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33879839280750435253874233 25409879460562826440405675)
    ·
      refine ⟨38114819190844239660608513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25409879460562826440405675 38114819190844239660608513)
      ·
        refine ⟨28586114393133179745456385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38114819190844239660608513 28586114393133179745456385)
        ·
          refine ⟨21439585794849884809092289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28586114393133179745456385 21439585794849884809092289)
          ·
            refine ⟨16079689346137413606819217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21439585794849884809092289 16079689346137413606819217)
            ·
              refine ⟨12059767009603060205114413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16079689346137413606819217 12059767009603060205114413)
              ·
                refine ⟨4522412628601147576917905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12059767009603060205114413 4522412628601147576917905)
                ·
                  refine ⟨3391809471450860682688429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4522412628601147576917905 3391809471450860682688429)
                  ·
                    refine ⟨1271928551794072756008161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3391809471450860682688429 1271928551794072756008161)
                    ·
                      refine ⟨953946413845554567006121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271928551794072756008161 953946413845554567006121)
                      ·
                        rfl

theorem cell23_1857804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_1857804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857804 prefixEnd_1857804 := by exact prefixLift 1857804
  have htrace : WordTrace (prefixWord ++ tailWord_1857804) baseStart_1857804 baseEnd_1857804 := by
    simpa [prefixWord, tailWord_1857804, baseEnd_1857804] using wordTrace_append hprefix tailTrace_1857804
  have hstable : (prefixWord ++ tailWord_1857804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857804).length < 2 ^ (prefixWord ++ tailWord_1857804).sum := by decide
  have hdescent : baseEnd_1857804 < baseStart_1857804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857827 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 4, 4]
def baseStart_1857827 : Nat := 118140960795 + 1857827 * 2 ^ 59
def prefixEnd_1857827 : Nat := 4983230072969 + 3 ^ 40 * 1857827 * 2
def baseEnd_1857827 : Nat := 317986074633535992339505

theorem tailTrace_1857827 : CollatzResearch.WordTrace tailWord_1857827 prefixEnd_1857827 317986074633535992339505 := by
  unfold tailWord_1857827
  simp only [CollatzResearch.WordTrace]
  refine ⟨67760517440417545435835735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45173678293611696957223823 67760517440417545435835735)
  ·
    refine ⟨101640776160626318153753603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67760517440417545435835735 101640776160626318153753603)
    ·
      refine ⟨152461164240939477230630405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101640776160626318153753603 152461164240939477230630405)
      ·
        refine ⟨28586468295176151980743201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152461164240939477230630405 28586468295176151980743201)
        ·
          refine ⟨21439851221382113985557401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28586468295176151980743201 21439851221382113985557401)
          ·
            refine ⟨16079888416036585489168051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21439851221382113985557401 16079888416036585489168051)
            ·
              refine ⟨24119832624054878233752077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16079888416036585489168051 24119832624054878233752077)
              ·
                refine ⟨9044937234020579337657029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24119832624054878233752077 9044937234020579337657029)
                ·
                  refine ⟨1695925731378858625810693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9044937234020579337657029 1695925731378858625810693)
                  ·
                    refine ⟨317986074633535992339505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695925731378858625810693 317986074633535992339505)
                    ·
                      rfl

theorem cell23_1857827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 4].length) (baseStart_1857827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857827 prefixEnd_1857827 := by exact prefixLift 1857827
  have htrace : WordTrace (prefixWord ++ tailWord_1857827) baseStart_1857827 baseEnd_1857827 := by
    simpa [prefixWord, tailWord_1857827, baseEnd_1857827] using wordTrace_append hprefix tailTrace_1857827
  have hstable : (prefixWord ++ tailWord_1857827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857827).length < 2 ^ (prefixWord ++ tailWord_1857827).sum := by decide
  have hdescent : baseEnd_1857827 < baseStart_1857827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857868 : List Nat := [2, 2, 1, 3, 2, 1, 2, 5, 1, 2, 2]
def baseStart_1857868 : Nat := 118140960795 + 1857868 * 2 ^ 59
def prefixEnd_1857868 : Nat := 4983230072969 + 3 ^ 40 * 1857868 * 2
def baseEnd_1857868 : Nat := 953979276607442316605827

theorem tailTrace_1857868 : CollatzResearch.WordTrace tailWord_1857868 prefixEnd_1857868 953979276607442316605827 := by
  unfold tailWord_1857868
  simp only [CollatzResearch.WordTrace]
  refine ⟨33881006416634504719039129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45174675222179339625385505 33881006416634504719039129)
  ·
    refine ⟨25410754812475878539279347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33881006416634504719039129 25410754812475878539279347)
    ·
      refine ⟨38116132218713817808919021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25410754812475878539279347 38116132218713817808919021)
      ·
        refine ⟨14293549582017681678344633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38116132218713817808919021 14293549582017681678344633)
        ·
          refine ⟨10720162186513261258758475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14293549582017681678344633 10720162186513261258758475)
          ·
            refine ⟨16080243279769891888137713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10720162186513261258758475 16080243279769891888137713)
            ·
              refine ⟨12060182459827418916103285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16080243279769891888137713 12060182459827418916103285)
              ·
                refine ⟨1130642105608820523384683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12060182459827418916103285 1130642105608820523384683)
                ·
                  refine ⟨1695963158413230785077025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130642105608820523384683 1695963158413230785077025)
                  ·
                    refine ⟨1271972368809923088807769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1695963158413230785077025 1271972368809923088807769)
                    ·
                      refine ⟨953979276607442316605827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271972368809923088807769 953979276607442316605827)
                      ·
                        rfl

theorem cell23_1857868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_1857868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857868 prefixEnd_1857868 := by exact prefixLift 1857868
  have htrace : WordTrace (prefixWord ++ tailWord_1857868) baseStart_1857868 baseEnd_1857868 := by
    simpa [prefixWord, tailWord_1857868, baseEnd_1857868] using wordTrace_append hprefix tailTrace_1857868
  have hstable : (prefixWord ++ tailWord_1857868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857868).length < 2 ^ (prefixWord ++ tailWord_1857868).sum := by decide
  have hdescent : baseEnd_1857868 < baseStart_1857868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857901 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1857901 : Nat := 118140960795 + 1857901 * 2 ^ 59
def prefixEnd_1857901 : Nat := 4983230072969 + 3 ^ 40 * 1857901 * 2
def baseEnd_1857901 : Nat := 953996221469040687493175

theorem tailTrace_1857901 : CollatzResearch.WordTrace tailWord_1857901 prefixEnd_1857901 953996221469040687493175 := by
  unfold tailWord_1857901
  simp only [CollatzResearch.WordTrace]
  refine ⟨67763216442149456074029557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45175477628099637382686371 67763216442149456074029557)
  ·
    refine ⟨6352801541451511506940271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67763216442149456074029557 6352801541451511506940271)
    ·
      refine ⟨9529202312177267260410407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6352801541451511506940271 9529202312177267260410407)
      ·
        refine ⟨14293803468265900890615611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9529202312177267260410407 14293803468265900890615611)
        ·
          refine ⟨21440705202398851335923417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14293803468265900890615611 21440705202398851335923417)
          ·
            refine ⟨16080528901799138501942563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21440705202398851335923417 16080528901799138501942563)
            ·
              refine ⟨24120793352698707752913845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16080528901799138501942563 24120793352698707752913845)
              ·
                refine ⟨2261324376815503851835673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24120793352698707752913845 2261324376815503851835673)
                ·
                  refine ⟨1695993282611627888876755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2261324376815503851835673 1695993282611627888876755)
                  ·
                    refine ⟨2543989923917441833315133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1695993282611627888876755 2543989923917441833315133)
                    ·
                      refine ⟨953996221469040687493175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2543989923917441833315133 953996221469040687493175)
                      ·
                        rfl

theorem cell23_1857901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1857901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857901 prefixEnd_1857901 := by exact prefixLift 1857901
  have htrace : WordTrace (prefixWord ++ tailWord_1857901) baseStart_1857901 baseEnd_1857901 := by
    simpa [prefixWord, tailWord_1857901, baseEnd_1857901] using wordTrace_append hprefix tailTrace_1857901
  have hstable : (prefixWord ++ tailWord_1857901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857901).length < 2 ^ (prefixWord ++ tailWord_1857901).sum := by decide
  have hdescent : baseEnd_1857901 < baseStart_1857901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857922 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_1857922 : Nat := 118140960795 + 1857922 * 2 ^ 59
def prefixEnd_1857922 : Nat := 4983230072969 + 3 ^ 40 * 1857922 * 2
def baseEnd_1857922 : Nat := 954007004562785105330579

theorem tailTrace_1857922 : CollatzResearch.WordTrace tailWord_1857922 prefixEnd_1857922 954007004562785105330579 := by
  unfold tailWord_1857922
  simp only [CollatzResearch.WordTrace]
  refine ⟨16940995593768344165136005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45175988250048917773696013 16940995593768344165136005)
  ·
    refine ⟨3176436673831564530963001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16940995593768344165136005 3176436673831564530963001)
    ·
      refine ⟨2382327505373673398222251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3176436673831564530963001 2382327505373673398222251)
      ·
        refine ⟨3573491258060510097333377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382327505373673398222251 3573491258060510097333377)
        ·
          refine ⟨2680118443545382573000033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3573491258060510097333377 2680118443545382573000033)
          ·
            refine ⟨2010088832659036929750025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2680118443545382573000033 2010088832659036929750025)
            ·
              refine ⟨1507566624494277697312519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010088832659036929750025 1507566624494277697312519)
              ·
                refine ⟨2261349936741416545968779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507566624494277697312519 2261349936741416545968779)
                ·
                  refine ⟨3392024905112124818953169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261349936741416545968779 3392024905112124818953169)
                  ·
                    refine ⟨2544018678834093614214877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3392024905112124818953169 2544018678834093614214877)
                    ·
                      refine ⟨954007004562785105330579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2544018678834093614214877 954007004562785105330579)
                      ·
                        rfl

theorem cell23_1857922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_1857922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857922 prefixEnd_1857922 := by exact prefixLift 1857922
  have htrace : WordTrace (prefixWord ++ tailWord_1857922) baseStart_1857922 baseEnd_1857922 := by
    simpa [prefixWord, tailWord_1857922, baseEnd_1857922] using wordTrace_append hprefix tailTrace_1857922
  have hstable : (prefixWord ++ tailWord_1857922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857922).length < 2 ^ (prefixWord ++ tailWord_1857922).sum := by decide
  have hdescent : baseEnd_1857922 < baseStart_1857922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857927 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1857927 : Nat := 118140960795 + 1857927 * 2 ^ 59
def prefixEnd_1857927 : Nat := 4983230072969 + 3 ^ 40 * 1857927 * 2
def baseEnd_1857927 : Nat := 954009571966057585768055

theorem tailTrace_1857927 : CollatzResearch.WordTrace tailWord_1857927 prefixEnd_1857927 954009571966057585768055 := by
  unfold tailWord_1857927
  simp only [CollatzResearch.WordTrace]
  refine ⟨67764164740055262514476035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45176109826703508342984023 67764164740055262514476035)
  ·
    refine ⟨101646247110082893771714053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67764164740055262514476035 101646247110082893771714053)
    ·
      refine ⟨19058671333140542582196385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101646247110082893771714053 19058671333140542582196385)
      ·
        refine ⟨14294003499855406936647289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19058671333140542582196385 14294003499855406936647289)
        ·
          refine ⟨10720502624891555202485467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14294003499855406936647289 10720502624891555202485467)
          ·
            refine ⟨16080753937337332803728201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10720502624891555202485467 16080753937337332803728201)
            ·
              refine ⟨12060565453002999602796151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16080753937337332803728201 12060565453002999602796151)
              ·
                refine ⟨18090848179504499404194227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12060565453002999602796151 18090848179504499404194227)
                ·
                  refine ⟨27136272269256749106291341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18090848179504499404194227 27136272269256749106291341)
                  ·
                    refine ⟨10176102100971280914859253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27136272269256749106291341 10176102100971280914859253)
                    ·
                      refine ⟨954009571966057585768055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10176102100971280914859253 954009571966057585768055)
                      ·
                        rfl

theorem cell23_1857927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1857927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857927 prefixEnd_1857927 := by exact prefixLift 1857927
  have htrace : WordTrace (prefixWord ++ tailWord_1857927) baseStart_1857927 baseEnd_1857927 := by
    simpa [prefixWord, tailWord_1857927, baseEnd_1857927] using wordTrace_append hprefix tailTrace_1857927
  have hstable : (prefixWord ++ tailWord_1857927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857927).length < 2 ^ (prefixWord ++ tailWord_1857927).sum := by decide
  have hdescent : baseEnd_1857927 < baseStart_1857927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857934 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_1857934 : Nat := 118140960795 + 1857934 * 2 ^ 59
def prefixEnd_1857934 : Nat := 4983230072969 + 3 ^ 40 * 1857934 * 2
def baseEnd_1857934 : Nat := 318004388776879686126841

theorem tailTrace_1857934 : CollatzResearch.WordTrace tailWord_1857934 prefixEnd_1857934 318004388776879686126841 := by
  unfold tailWord_1857934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470552506378737838747607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45176280034019935139987237 8470552506378737838747607)
  ·
    refine ⟨12705828759568106758121411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8470552506378737838747607 12705828759568106758121411)
    ·
      refine ⟨19058743139352160137182117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12705828759568106758121411 19058743139352160137182117)
      ·
        refine ⟨3573514338628530025721647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19058743139352160137182117 3573514338628530025721647)
        ·
          refine ⟨5360271507942795038582471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573514338628530025721647 5360271507942795038582471)
          ·
            refine ⟨8040407261914192557873707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360271507942795038582471 8040407261914192557873707)
            ·
              refine ⟨12060610892871288836810561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8040407261914192557873707 12060610892871288836810561)
              ·
                refine ⟨9045458169653466627607921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12060610892871288836810561 9045458169653466627607921)
                ·
                  refine ⟨6784093627240099970705941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9045458169653466627607921 6784093627240099970705941)
                  ·
                    refine ⟨318004388776879686126841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6784093627240099970705941 318004388776879686126841)
                    ·
                      rfl

theorem cell23_1857934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_1857934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857934 prefixEnd_1857934 := by exact prefixLift 1857934
  have htrace : WordTrace (prefixWord ++ tailWord_1857934) baseStart_1857934 baseEnd_1857934 := by
    simpa [prefixWord, tailWord_1857934, baseEnd_1857934] using wordTrace_append hprefix tailTrace_1857934
  have hstable : (prefixWord ++ tailWord_1857934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857934).length < 2 ^ (prefixWord ++ tailWord_1857934).sum := by decide
  have hdescent : baseEnd_1857934 < baseStart_1857934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857954 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1857954 : Nat := 118140960795 + 1857954 * 2 ^ 59
def prefixEnd_1857954 : Nat := 4983230072969 + 3 ^ 40 * 1857954 * 2
def baseEnd_1857954 : Nat := 954023435943728980130431

theorem tailTrace_1857954 : CollatzResearch.WordTrace tailWord_1857954 prefixEnd_1857954 954023435943728980130431 := by
  unfold tailWord_1857954
  simp only [CollatzResearch.WordTrace]
  refine ⟨16941287377739361531427229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45176766340638297417139277 16941287377739361531427229)
  ·
    refine ⟨6352982766652260574285211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16941287377739361531427229 6352982766652260574285211)
    ·
      refine ⟨9529474149978390861427817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6352982766652260574285211 9529474149978390861427817)
      ·
        refine ⟨7147105612483793146070863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9529474149978390861427817 7147105612483793146070863)
        ·
          refine ⟨10720658418725689719106295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147105612483793146070863 10720658418725689719106295)
          ·
            refine ⟨16080987628088534578659443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10720658418725689719106295 16080987628088534578659443)
            ·
              refine ⟨24121481442132801867989165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16080987628088534578659443 24121481442132801867989165)
              ·
                refine ⟨9045555540799800700495937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24121481442132801867989165 9045555540799800700495937)
                ·
                  refine ⟨6784166655599850525371953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9045555540799800700495937 6784166655599850525371953)
                  ·
                    refine ⟨5088124991699887894028965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6784166655599850525371953 5088124991699887894028965)
                    ·
                      refine ⟨954023435943728980130431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5088124991699887894028965 954023435943728980130431)
                      ·
                        rfl

theorem cell23_1857954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1857954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857954 prefixEnd_1857954 := by exact prefixLift 1857954
  have htrace : WordTrace (prefixWord ++ tailWord_1857954) baseStart_1857954 baseEnd_1857954 := by
    simpa [prefixWord, tailWord_1857954, baseEnd_1857954] using wordTrace_append hprefix tailTrace_1857954
  have hstable : (prefixWord ++ tailWord_1857954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857954).length < 2 ^ (prefixWord ++ tailWord_1857954).sum := by decide
  have hdescent : baseEnd_1857954 < baseStart_1857954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857981 : List Nat := [1, 4, 1, 2, 2, 2, 3, 3, 5]
def baseStart_1857981 : Nat := 118140960795 + 1857981 * 2 ^ 59
def prefixEnd_1857981 : Nat := 4983230072969 + 3 ^ 40 * 1857981 * 2
def baseEnd_1857981 : Nat := 106004144435711152721423

theorem tailTrace_1857981 : CollatzResearch.WordTrace tailWord_1857981 prefixEnd_1857981 106004144435711152721423 := by
  unfold tailWord_1857981
  simp only [CollatzResearch.WordTrace]
  refine ⟨67766134281859629736941797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45177422854573086491294531 67766134281859629736941797)
  ·
    refine ⟨12706150177848680575676587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67766134281859629736941797 12706150177848680575676587)
    ·
      refine ⟨19059225266773020863514881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12706150177848680575676587 19059225266773020863514881)
      ·
        refine ⟨14294418950079765647636161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19059225266773020863514881 14294418950079765647636161)
        ·
          refine ⟨10720814212559824235727121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14294418950079765647636161 10720814212559824235727121)
          ·
            refine ⟨8040610659419868176795341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10720814212559824235727121 8040610659419868176795341)
            ·
              refine ⟨3015228997282450566298253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8040610659419868176795341 3015228997282450566298253)
              ·
                refine ⟨1130710873980918962361845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3015228997282450566298253 1130710873980918962361845)
                ·
                  refine ⟨106004144435711152721423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1130710873980918962361845 106004144435711152721423)
                  ·
                    rfl

theorem cell23_1857981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_1857981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857981 prefixEnd_1857981 := by exact prefixLift 1857981
  have htrace : WordTrace (prefixWord ++ tailWord_1857981) baseStart_1857981 baseEnd_1857981 := by
    simpa [prefixWord, tailWord_1857981, baseEnd_1857981] using wordTrace_append hprefix tailTrace_1857981
  have hstable : (prefixWord ++ tailWord_1857981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857981).length < 2 ^ (prefixWord ++ tailWord_1857981).sum := by decide
  have hdescent : baseEnd_1857981 < baseStart_1857981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857984 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 1, 7, 2]
def baseStart_1857984 : Nat := 118140960795 + 1857984 * 2 ^ 59
def prefixEnd_1857984 : Nat := 4983230072969 + 3 ^ 40 * 1857984 * 2
def baseEnd_1857984 : Nat := 954038840363363862755293

theorem tailTrace_1857984 : CollatzResearch.WordTrace tailWord_1857984 prefixEnd_1857984 954038840363363862755293 := by
  unfold tailWord_1857984
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883121850424380624650503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45177495800565840832867337 33883121850424380624650503)
  ·
    refine ⟨50824682775636570936975755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33883121850424380624650503 50824682775636570936975755)
    ·
      refine ⟨76237024163454856405463633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50824682775636570936975755 76237024163454856405463633)
      ·
        refine ⟨57177768122591142304097725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76237024163454856405463633 57177768122591142304097725)
        ·
          refine ⟨21441663045971678364036647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57177768122591142304097725 21441663045971678364036647)
          ·
            refine ⟨32162494568957517546054971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21441663045971678364036647 32162494568957517546054971)
            ·
              refine ⟨48243741853436276319082457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32162494568957517546054971 48243741853436276319082457)
              ·
                refine ⟨36182806390077207239311843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48243741853436276319082457 36182806390077207239311843)
                ·
                  refine ⟨54274209585115810858967765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36182806390077207239311843 54274209585115810858967765)
                  ·
                    refine ⟨1272051787151151817007057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54274209585115810858967765 1272051787151151817007057)
                    ·
                      refine ⟨954038840363363862755293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272051787151151817007057 954038840363363862755293)
                      ·
                        rfl

theorem cell23_1857984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_1857984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857984 prefixEnd_1857984 := by exact prefixLift 1857984
  have htrace : WordTrace (prefixWord ++ tailWord_1857984) baseStart_1857984 baseEnd_1857984 := by
    simpa [prefixWord, tailWord_1857984, baseEnd_1857984] using wordTrace_append hprefix tailTrace_1857984
  have hstable : (prefixWord ++ tailWord_1857984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857984).length < 2 ^ (prefixWord ++ tailWord_1857984).sum := by decide
  have hdescent : baseEnd_1857984 < baseStart_1857984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857987 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 5]
def baseStart_1857987 : Nat := 118140960795 + 1857987 * 2 ^ 59
def prefixEnd_1857987 : Nat := 4983230072969 + 3 ^ 40 * 1857987 * 2
def baseEnd_1857987 : Nat := 954040380805327351017779

theorem tailTrace_1857987 : CollatzResearch.WordTrace tailWord_1857987 prefixEnd_1857987 954040380805327351017779 := by
  unfold tailWord_1857987
  simp only [CollatzResearch.WordTrace]
  refine ⟨67766353119837892761660215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45177568746558595174440143 67766353119837892761660215)
  ·
    refine ⟨101649529679756839142490323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67766353119837892761660215 101649529679756839142490323)
    ·
      refine ⟨152474294519635258713735485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101649529679756839142490323 152474294519635258713735485)
      ·
        refine ⟨57177860444863222017650807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152474294519635258713735485 57177860444863222017650807)
        ·
          refine ⟨85766790667294833026476211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57177860444863222017650807 85766790667294833026476211)
          ·
            refine ⟨128650186000942249539714317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85766790667294833026476211 128650186000942249539714317)
            ·
              refine ⟨48243819750353343577392869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128650186000942249539714317 48243819750353343577392869)
              ·
                refine ⟨9045716203191251920761163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48243819750353343577392869 9045716203191251920761163)
                ·
                  refine ⟨13568574304786877881141745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9045716203191251920761163 13568574304786877881141745)
                  ·
                    refine ⟨10176430728590158410856309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13568574304786877881141745 10176430728590158410856309)
                    ·
                      refine ⟨954040380805327351017779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10176430728590158410856309 954040380805327351017779)
                      ·
                        rfl

theorem cell23_1857987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_1857987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857987 prefixEnd_1857987 := by exact prefixLift 1857987
  have htrace : WordTrace (prefixWord ++ tailWord_1857987) baseStart_1857987 baseEnd_1857987 := by
    simpa [prefixWord, tailWord_1857987, baseEnd_1857987] using wordTrace_append hprefix tailTrace_1857987
  have hstable : (prefixWord ++ tailWord_1857987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857987).length < 2 ^ (prefixWord ++ tailWord_1857987).sum := by decide
  have hdescent : baseEnd_1857987 < baseStart_1857987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857994 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_1857994 : Nat := 118140960795 + 1857994 * 2 ^ 59
def prefixEnd_1857994 : Nat := 4983230072969 + 3 ^ 40 * 1857994 * 2
def baseEnd_1857994 : Nat := 318014658389969607876749

theorem tailTrace_1857994 : CollatzResearch.WordTrace tailWord_1857994 prefixEnd_1857994 318014658389969607876749 := by
  unfold tailWord_1857994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16941652107703133239291259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45177738953875021971443357 16941652107703133239291259)
  ·
    refine ⟨25412478161554699858936889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16941652107703133239291259 25412478161554699858936889)
    ·
      refine ⟨19059358621166024894202667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25412478161554699858936889 19059358621166024894202667)
      ·
        refine ⟨28589037931749037341304001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19059358621166024894202667 28589037931749037341304001)
        ·
          refine ⟨21441778448811778005978001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28589037931749037341304001 21441778448811778005978001)
          ·
            refine ⟨16081333836608833504483501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21441778448811778005978001 16081333836608833504483501)
            ·
              refine ⟨6030500188728312564181313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16081333836608833504483501 6030500188728312564181313)
              ·
                refine ⟨4522875141546234423135985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6030500188728312564181313 4522875141546234423135985)
                ·
                  refine ⟨3392156356159675817351989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4522875141546234423135985 3392156356159675817351989)
                  ·
                    refine ⟨318014658389969607876749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3392156356159675817351989 318014658389969607876749)
                    ·
                      rfl

theorem cell23_1857994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_1857994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857994 prefixEnd_1857994 := by exact prefixLift 1857994
  have htrace : WordTrace (prefixWord ++ tailWord_1857994) baseStart_1857994 baseEnd_1857994 := by
    simpa [prefixWord, tailWord_1857994, baseEnd_1857994] using wordTrace_append hprefix tailTrace_1857994
  have hstable : (prefixWord ++ tailWord_1857994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857994).length < 2 ^ (prefixWord ++ tailWord_1857994).sum := by decide
  have hdescent : baseEnd_1857994 < baseStart_1857994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858004 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1858004 : Nat := 118140960795 + 1858004 * 2 ^ 59
def prefixEnd_1858004 : Nat := 4983230072969 + 3 ^ 40 * 1858004 * 2
def baseEnd_1858004 : Nat := 954049109976453784505201

theorem tailTrace_1858004 : CollatzResearch.WordTrace tailWord_1858004 prefixEnd_1858004 954049109976453784505201 := by
  unfold tailWord_1858004
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883486580388152332514533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45177982107184203110019377 33883486580388152332514533)
  ·
    refine ⟨6353153733822778562346475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33883486580388152332514533 6353153733822778562346475)
    ·
      refine ⟨9529730600734167843519713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353153733822778562346475 9529730600734167843519713)
      ·
        refine ⟨7147297950550625882639785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9529730600734167843519713 7147297950550625882639785)
        ·
          refine ⟨5360473462912969411979839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7147297950550625882639785 5360473462912969411979839)
          ·
            refine ⟨8040710194369454117969759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360473462912969411979839 8040710194369454117969759)
            ·
              refine ⟨12061065291554181176954639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8040710194369454117969759 12061065291554181176954639)
              ·
                refine ⟨18091597937331271765431959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12061065291554181176954639 18091597937331271765431959)
                ·
                  refine ⟨27137396905996907648147939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18091597937331271765431959 27137396905996907648147939)
                  ·
                    refine ⟨40706095358995361472221909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27137396905996907648147939 40706095358995361472221909)
                    ·
                      refine ⟨954049109976453784505201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40706095358995361472221909 954049109976453784505201)
                      ·
                        rfl

theorem cell23_1858004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1858004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858004 prefixEnd_1858004 := by exact prefixLift 1858004
  have htrace : WordTrace (prefixWord ++ tailWord_1858004) baseStart_1858004 baseEnd_1858004 := by
    simpa [prefixWord, tailWord_1858004, baseEnd_1858004] using wordTrace_append hprefix tailTrace_1858004
  have hstable : (prefixWord ++ tailWord_1858004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858004).length < 2 ^ (prefixWord ++ tailWord_1858004).sum := by decide
  have hdescent : baseEnd_1858004 < baseStart_1858004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858058 : List Nat := [3, 1, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_1858058 : Nat := 118140960795 + 1858058 * 2 ^ 59
def prefixEnd_1858058 : Nat := 4983230072969 + 3 ^ 40 * 1858058 * 2
def baseEnd_1858058 : Nat := 318025612643932191076651

theorem tailTrace_1858058 : CollatzResearch.WordTrace tailWord_1858058 prefixEnd_1858058 318025612643932191076651 := by
  unfold tailWord_1858058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16942235675645167971873707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45179295135053781258329885 16942235675645167971873707)
  ·
    refine ⟨25413353513467751957810561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16942235675645167971873707 25413353513467751957810561)
    ·
      refine ⟨19060015135100813968357921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25413353513467751957810561 19060015135100813968357921)
      ·
        refine ⟨14295011351325610476268441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19060015135100813968357921 14295011351325610476268441)
        ·
          refine ⟨10721258513494207857201331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14295011351325610476268441 10721258513494207857201331)
          ·
            refine ⟨16081887770241311785801997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721258513494207857201331 16081887770241311785801997)
            ·
              refine ⟨6030707913840491919675749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16081887770241311785801997 6030707913840491919675749)
              ·
                refine ⟨1130757733845092234939203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6030707913840491919675749 1130757733845092234939203)
                ·
                  refine ⟨1696136600767638352408805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130757733845092234939203 1696136600767638352408805)
                  ·
                    refine ⟨318025612643932191076651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696136600767638352408805 318025612643932191076651)
                    ·
                      rfl

theorem cell23_1858058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_1858058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858058 prefixEnd_1858058 := by exact prefixLift 1858058
  have htrace : WordTrace (prefixWord ++ tailWord_1858058) baseStart_1858058 baseEnd_1858058 := by
    simpa [prefixWord, tailWord_1858058, baseEnd_1858058] using wordTrace_append hprefix tailTrace_1858058
  have hstable : (prefixWord ++ tailWord_1858058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858058).length < 2 ^ (prefixWord ++ tailWord_1858058).sum := by decide
  have hdescent : baseEnd_1858058 < baseStart_1858058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858101 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1858101 : Nat := 118140960795 + 1858101 * 2 ^ 59
def prefixEnd_1858101 : Nat := 4983230072969 + 3 ^ 40 * 1858101 * 2
def baseEnd_1858101 : Nat := 318032972533313301664085

theorem tailTrace_1858101 : CollatzResearch.WordTrace tailWord_1858101 prefixEnd_1858101 318032972533313301664085 := by
  unfold tailWord_1858101
  simp only [CollatzResearch.WordTrace]
  refine ⟨67770511041424890231310157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45180340694283260154206771 67770511041424890231310157)
  ·
    refine ⟨25413941640534333836741309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67770511041424890231310157 25413941640534333836741309)
    ·
      refine ⟨9530228115200375188777991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25413941640534333836741309 9530228115200375188777991)
      ·
        refine ⟨14295342172800562783166987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9530228115200375188777991 14295342172800562783166987)
        ·
          refine ⟨21443013259200844174750481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14295342172800562783166987 21443013259200844174750481)
          ·
            refine ⟨16082259944400633131062861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21443013259200844174750481 16082259944400633131062861)
            ·
              refine ⟨6030847479150237424148573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16082259944400633131062861 6030847479150237424148573)
              ·
                refine ⟨2261567804681339034055715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6030847479150237424148573 2261567804681339034055715)
                ·
                  refine ⟨3392351707022008551083573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261567804681339034055715 3392351707022008551083573)
                  ·
                    refine ⟨318032972533313301664085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3392351707022008551083573 318032972533313301664085)
                    ·
                      rfl

theorem cell23_1858101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1858101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858101 prefixEnd_1858101 := by exact prefixLift 1858101
  have htrace : WordTrace (prefixWord ++ tailWord_1858101) baseStart_1858101 baseEnd_1858101 := by
    simpa [prefixWord, tailWord_1858101, baseEnd_1858101] using wordTrace_append hprefix tailTrace_1858101
  have hstable : (prefixWord ++ tailWord_1858101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858101).length < 2 ^ (prefixWord ++ tailWord_1858101).sum := by decide
  have hdescent : baseEnd_1858101 < baseStart_1858101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858149 : List Nat := [1, 3, 1, 3, 5, 1, 1, 3, 1, 1, 3]
def baseStart_1858149 : Nat := 118140960795 + 1858149 * 2 ^ 59
def prefixEnd_1858149 : Nat := 4983230072969 + 3 ^ 40 * 1858149 * 2
def baseEnd_1858149 : Nat := 954123564671355717192035

theorem tailTrace_1858149 : CollatzResearch.WordTrace tailWord_1858149 prefixEnd_1858149 954123564671355717192035 := by
  unfold tailWord_1858149
  simp only [CollatzResearch.WordTrace]
  refine ⟨67772261745250994429057501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45181507830167329619371667 67772261745250994429057501)
  ·
    refine ⟨25414598154469122910896563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67772261745250994429057501 25414598154469122910896563)
    ·
      refine ⟨38121897231703684366344845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25414598154469122910896563 38121897231703684366344845)
      ·
        refine ⟨14295711461888881637379317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38121897231703684366344845 14295711461888881637379317)
        ·
          refine ⟨1340222949552082653504311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14295711461888881637379317 1340222949552082653504311)
          ·
            refine ⟨2010334424328123980256467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340222949552082653504311 2010334424328123980256467)
            ·
              refine ⟨3015501636492185970384701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010334424328123980256467 3015501636492185970384701)
              ·
                refine ⟨1130813113684569738894263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3015501636492185970384701 1130813113684569738894263)
                ·
                  refine ⟨1696219670526854608341395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130813113684569738894263 1696219670526854608341395)
                  ·
                    refine ⟨2544329505790281912512093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1696219670526854608341395 2544329505790281912512093)
                    ·
                      refine ⟨954123564671355717192035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2544329505790281912512093 954123564671355717192035)
                      ·
                        rfl

theorem cell23_1858149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_1858149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858149 prefixEnd_1858149 := by exact prefixLift 1858149
  have htrace : WordTrace (prefixWord ++ tailWord_1858149) baseStart_1858149 baseEnd_1858149 := by
    simpa [prefixWord, tailWord_1858149, baseEnd_1858149] using wordTrace_append hprefix tailTrace_1858149
  have hstable : (prefixWord ++ tailWord_1858149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858149).length < 2 ^ (prefixWord ++ tailWord_1858149).sum := by decide
  have hdescent : baseEnd_1858149 < baseStart_1858149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858155 : List Nat := [1, 1, 1, 1, 2, 2, 1, 9, 1, 2, 2]
def baseStart_1858155 : Nat := 118140960795 + 1858155 * 2 ^ 59
def prefixEnd_1858155 : Nat := 4983230072969 + 3 ^ 40 * 1858155 * 2
def baseEnd_1858155 : Nat := 954126645555282693717007

theorem tailTrace_1858155 : CollatzResearch.WordTrace tailWord_1858155 prefixEnd_1858155 954126645555282693717007 := by
  unfold tailWord_1858155
  simp only [CollatzResearch.WordTrace]
  refine ⟨67772480583229257453775919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45181653722152838302517279 67772480583229257453775919)
  ·
    refine ⟨101658720874843886180663879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67772480583229257453775919 101658720874843886180663879)
    ·
      refine ⟨152488081312265829270995819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101658720874843886180663879 152488081312265829270995819)
      ·
        refine ⟨228732121968398743906493729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152488081312265829270995819 228732121968398743906493729)
        ·
          refine ⟨171549091476299057929870297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228732121968398743906493729 171549091476299057929870297)
          ·
            refine ⟨128661818607224293447402723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171549091476299057929870297 128661818607224293447402723)
            ·
              refine ⟨192992727910836440171104085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128661818607224293447402723 192992727910836440171104085)
              ·
                refine ⟨1130816765102557266627563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 192992727910836440171104085 1130816765102557266627563)
                ·
                  refine ⟨1696225147653835899941345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130816765102557266627563 1696225147653835899941345)
                  ·
                    refine ⟨1272168860740376924956009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1696225147653835899941345 1272168860740376924956009)
                    ·
                      refine ⟨954126645555282693717007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272168860740376924956009 954126645555282693717007)
                      ·
                        rfl

theorem cell23_1858155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 2, 2].length) (baseStart_1858155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858155 prefixEnd_1858155 := by exact prefixLift 1858155
  have htrace : WordTrace (prefixWord ++ tailWord_1858155) baseStart_1858155 baseEnd_1858155 := by
    simpa [prefixWord, tailWord_1858155, baseEnd_1858155] using wordTrace_append hprefix tailTrace_1858155
  have hstable : (prefixWord ++ tailWord_1858155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858155).length < 2 ^ (prefixWord ++ tailWord_1858155).sum := by decide
  have hdescent : baseEnd_1858155 < baseStart_1858155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858158 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1858158 : Nat := 118140960795 + 1858158 * 2 ^ 59
def prefixEnd_1858158 : Nat := 4983230072969 + 3 ^ 40 * 1858158 * 2
def baseEnd_1858158 : Nat := 954128185997246181979493

theorem tailTrace_1858158 : CollatzResearch.WordTrace tailWord_1858158 prefixEnd_1858158 954128185997246181979493 := by
  unfold tailWord_1858158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471573750277298620766891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45181726668145592644090085 8471573750277298620766891)
  ·
    refine ⟨12707360625415947931150337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8471573750277298620766891 12707360625415947931150337)
    ·
      refine ⟨9530520469061960948362753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12707360625415947931150337 9530520469061960948362753)
      ·
        refine ⟨7147890351796470711272065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9530520469061960948362753 7147890351796470711272065)
        ·
          refine ⟨5360917763847353033454049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7147890351796470711272065 5360917763847353033454049)
          ·
            refine ⟨4020688322885514775090537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5360917763847353033454049 4020688322885514775090537)
            ·
              refine ⟨3015516242164136081317903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4020688322885514775090537 3015516242164136081317903)
              ·
                refine ⟨4523274363246204121976855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015516242164136081317903 4523274363246204121976855)
                ·
                  refine ⟨6784911544869306182965283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4523274363246204121976855 6784911544869306182965283)
                  ·
                    refine ⟨10177367317303959274447925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6784911544869306182965283 10177367317303959274447925)
                    ·
                      refine ⟨954128185997246181979493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10177367317303959274447925 954128185997246181979493)
                      ·
                        rfl

theorem cell23_1858158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1858158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858158 prefixEnd_1858158 := by exact prefixLift 1858158
  have htrace : WordTrace (prefixWord ++ tailWord_1858158) baseStart_1858158 baseEnd_1858158 := by
    simpa [prefixWord, tailWord_1858158, baseEnd_1858158] using wordTrace_append hprefix tailTrace_1858158
  have hstable : (prefixWord ++ tailWord_1858158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858158).length < 2 ^ (prefixWord ++ tailWord_1858158).sum := by decide
  have hdescent : baseEnd_1858158 < baseStart_1858158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858222 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1858222 : Nat := 118140960795 + 1858222 * 2 ^ 59
def prefixEnd_1858222 : Nat := 4983230072969 + 3 ^ 40 * 1858222 * 2
def baseEnd_1858222 : Nat := 954161048759133931579199

theorem tailTrace_1858222 : CollatzResearch.WordTrace tailWord_1858222 prefixEnd_1858222 954161048759133931579199 := by
  unfold tailWord_1858222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471865534248315987058115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45183282849324351930976613 8471865534248315987058115)
  ·
    refine ⟨12707798301372473980587173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8471865534248315987058115 12707798301372473980587173)
    ·
      refine ⟨2382712181507338871360095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12707798301372473980587173 2382712181507338871360095)
      ·
        refine ⟨3574068272261008307040143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382712181507338871360095 3574068272261008307040143)
        ·
          refine ⟨5361102408391512460560215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574068272261008307040143 5361102408391512460560215)
          ·
            refine ⟨8041653612587268690840323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361102408391512460560215 8041653612587268690840323)
            ·
              refine ⟨12062480418880903036260485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041653612587268690840323 12062480418880903036260485)
              ·
                refine ⟨2261715078540169319298841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12062480418880903036260485 2261715078540169319298841)
                ·
                  refine ⟨1696286308905126989474131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2261715078540169319298841 1696286308905126989474131)
                  ·
                    refine ⟨2544429463357690484211197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1696286308905126989474131 2544429463357690484211197)
                    ·
                      refine ⟨954161048759133931579199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2544429463357690484211197 954161048759133931579199)
                      ·
                        rfl

theorem cell23_1858222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1858222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858222 prefixEnd_1858222 := by exact prefixLift 1858222
  have htrace : WordTrace (prefixWord ++ tailWord_1858222) baseStart_1858222 baseEnd_1858222 := by
    simpa [prefixWord, tailWord_1858222, baseEnd_1858222] using wordTrace_append hprefix tailTrace_1858222
  have hstable : (prefixWord ++ tailWord_1858222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858222).length < 2 ^ (prefixWord ++ tailWord_1858222).sum := by decide
  have hdescent : baseEnd_1858222 < baseStart_1858222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858224 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_1858224 : Nat := 118140960795 + 1858224 * 2 ^ 59
def prefixEnd_1858224 : Nat := 4983230072969 + 3 ^ 40 * 1858224 * 2
def baseEnd_1858224 : Nat := 954162075720442923754189

theorem tailTrace_1858224 : CollatzResearch.WordTrace tailWord_1858224 prefixEnd_1858224 954162075720442923754189 := by
  unfold tailWord_1858224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33887498609989641119018863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45183331479986188158691817 33887498609989641119018863)
  ·
    refine ⟨50831247914984461678528295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33887498609989641119018863 50831247914984461678528295)
    ·
      refine ⟨76246871872476692517792443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50831247914984461678528295 76246871872476692517792443)
      ·
        refine ⟨114370307808715038776688665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76246871872476692517792443 114370307808715038776688665)
        ·
          refine ⟨85777730856536279082516499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114370307808715038776688665 85777730856536279082516499)
          ·
            refine ⟨128666596284804418623774749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85777730856536279082516499 128666596284804418623774749)
            ·
              refine ⟨48249973606801656983915531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128666596284804418623774749 48249973606801656983915531)
              ·
                refine ⟨72374960410202485475873297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48249973606801656983915531 72374960410202485475873297)
                ·
                  refine ⟨54281220307651864106904973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72374960410202485475873297 54281220307651864106904973)
                  ·
                    refine ⟨20355457615369449040089365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54281220307651864106904973 20355457615369449040089365)
                    ·
                      refine ⟨954162075720442923754189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20355457615369449040089365 954162075720442923754189)
                      ·
                        rfl

theorem cell23_1858224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_1858224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858224 prefixEnd_1858224 := by exact prefixLift 1858224
  have htrace : WordTrace (prefixWord ++ tailWord_1858224) baseStart_1858224 baseEnd_1858224 := by
    simpa [prefixWord, tailWord_1858224, baseEnd_1858224] using wordTrace_append hprefix tailTrace_1858224
  have hstable : (prefixWord ++ tailWord_1858224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858224).length < 2 ^ (prefixWord ++ tailWord_1858224).sum := by decide
  have hdescent : baseEnd_1858224 < baseStart_1858224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858281 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 2, 5]
def baseStart_1858281 : Nat := 118140960795 + 1858281 * 2 ^ 59
def prefixEnd_1858281 : Nat := 4983230072969 + 3 ^ 40 * 1858281 * 2
def baseEnd_1858281 : Nat := 318063781372583066913809

theorem tailTrace_1858281 : CollatzResearch.WordTrace tailWord_1858281 prefixEnd_1858281 318063781372583066913809 := by
  unfold tailWord_1858281
  simp only [CollatzResearch.WordTrace]
  refine ⟨67777076180772780972862697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45184717453848520648575131 67777076180772780972862697)
  ·
    refine ⟨50832807135579585729647023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67777076180772780972862697 50832807135579585729647023)
    ·
      refine ⟨76249210703369378594470535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50832807135579585729647023 76249210703369378594470535)
      ·
        refine ⟨114373816055054067891705803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76249210703369378594470535 114373816055054067891705803)
        ·
          refine ⟨171560724082581101837558705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114373816055054067891705803 171560724082581101837558705)
          ·
            refine ⟨128670543061935826378169029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171560724082581101837558705 128670543061935826378169029)
            ·
              refine ⟨24125726824112967445906693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128670543061935826378169029 24125726824112967445906693)
              ·
                refine ⟨4523573779521181396107505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24125726824112967445906693 4523573779521181396107505)
                ·
                  refine ⟨3392680334640886047080629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523573779521181396107505 3392680334640886047080629)
                  ·
                    refine ⟨318063781372583066913809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3392680334640886047080629 318063781372583066913809)
                    ·
                      rfl

theorem cell23_1858281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_1858281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858281 prefixEnd_1858281 := by exact prefixLift 1858281
  have htrace : WordTrace (prefixWord ++ tailWord_1858281) baseStart_1858281 baseEnd_1858281 := by
    simpa [prefixWord, tailWord_1858281, baseEnd_1858281] using wordTrace_append hprefix tailTrace_1858281
  have hstable : (prefixWord ++ tailWord_1858281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858281).length < 2 ^ (prefixWord ++ tailWord_1858281).sum := by decide
  have hdescent : baseEnd_1858281 < baseStart_1858281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858301 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_1858301 : Nat := 118140960795 + 1858301 * 2 ^ 59
def prefixEnd_1858301 : Nat := 4983230072969 + 3 ^ 40 * 1858301 * 2
def baseEnd_1858301 : Nat := 954201613730839122491335

theorem tailTrace_1858301 : CollatzResearch.WordTrace tailWord_1858301 prefixEnd_1858301 954201613730839122491335 := by
  unfold tailWord_1858301
  simp only [CollatzResearch.WordTrace]
  refine ⟨67777805640700324388590757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45185203760466882925727171 67777805640700324388590757)
  ·
    refine ⟨12708338557631310822860767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67777805640700324388590757 12708338557631310822860767)
    ·
      refine ⟨19062507836446966234291151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12708338557631310822860767 19062507836446966234291151)
      ·
        refine ⟨28593761754670449351436727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19062507836446966234291151 28593761754670449351436727)
        ·
          refine ⟨42890642632005674027155091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28593761754670449351436727 42890642632005674027155091)
          ·
            refine ⟨64335963948008511040732637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42890642632005674027155091 64335963948008511040732637)
            ·
              refine ⟨24125986480503191640274739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64335963948008511040732637 24125986480503191640274739)
              ·
                refine ⟨36188979720754787460412109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24125986480503191640274739 36188979720754787460412109)
                ·
                  refine ⟨13570867395283045297654541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36188979720754787460412109 13570867395283045297654541)
                  ·
                    refine ⟨5089075273231141986620453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13570867395283045297654541 5089075273231141986620453)
                    ·
                      refine ⟨954201613730839122491335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5089075273231141986620453 954201613730839122491335)
                      ·
                        rfl

theorem cell23_1858301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_1858301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858301 prefixEnd_1858301 := by exact prefixLift 1858301
  have htrace : WordTrace (prefixWord ++ tailWord_1858301) baseStart_1858301 baseEnd_1858301 := by
    simpa [prefixWord, tailWord_1858301, baseEnd_1858301] using wordTrace_append hprefix tailTrace_1858301
  have hstable : (prefixWord ++ tailWord_1858301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858301).length < 2 ^ (prefixWord ++ tailWord_1858301).sum := by decide
  have hdescent : baseEnd_1858301 < baseStart_1858301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858318 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1858318 : Nat := 118140960795 + 1858318 * 2 ^ 59
def prefixEnd_1858318 : Nat := 4983230072969 + 3 ^ 40 * 1858318 * 2
def baseEnd_1858318 : Nat := 954210342901965555978757

theorem tailTrace_1858318 : CollatzResearch.WordTrace tailWord_1858318 prefixEnd_1858318 954210342901965555978757 := by
  unfold tailWord_1858318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8472303210204842036494951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45185617121092490861306405 8472303210204842036494951)
  ·
    refine ⟨12708454815307263054742427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8472303210204842036494951 12708454815307263054742427)
    ·
      refine ⟨19062682222960894582113641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12708454815307263054742427 19062682222960894582113641)
      ·
        refine ⟨14297011667220670936585231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19062682222960894582113641 14297011667220670936585231)
        ·
          refine ⟨21445517500831006404877847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14297011667220670936585231 21445517500831006404877847)
          ·
            refine ⟨32168276251246509607316771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21445517500831006404877847 32168276251246509607316771)
            ·
              refine ⟨48252414376869764410975157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32168276251246509607316771 48252414376869764410975157)
              ·
                refine ⟨4523663847831540413528921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48252414376869764410975157 4523663847831540413528921)
                ·
                  refine ⟨3392747885873655310146691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523663847831540413528921 3392747885873655310146691)
                  ·
                    refine ⟨5089121828810482965220037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3392747885873655310146691 5089121828810482965220037)
                    ·
                      refine ⟨954210342901965555978757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5089121828810482965220037 954210342901965555978757)
                      ·
                        rfl

theorem cell23_1858318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1858318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858318 prefixEnd_1858318 := by exact prefixLift 1858318
  have htrace : WordTrace (prefixWord ++ tailWord_1858318) baseStart_1858318 baseEnd_1858318 := by
    simpa [prefixWord, tailWord_1858318, baseEnd_1858318] using wordTrace_append hprefix tailTrace_1858318
  have hstable : (prefixWord ++ tailWord_1858318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858318).length < 2 ^ (prefixWord ++ tailWord_1858318).sum := by decide
  have hdescent : baseEnd_1858318 < baseStart_1858318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858341 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 8]
def baseStart_1858341 : Nat := 118140960795 + 1858341 * 2 ^ 59
def prefixEnd_1858341 : Nat := 4983230072969 + 3 ^ 40 * 1858341 * 2
def baseEnd_1858341 : Nat := 106024683661890996221239

theorem tailTrace_1858341 : CollatzResearch.WordTrace tailWord_1858341 prefixEnd_1858341 106024683661890996221239 := by
  unfold tailWord_1858341
  simp only [CollatzResearch.WordTrace]
  refine ⟨67779264560555411220046877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45186176373703607480031251 67779264560555411220046877)
  ·
    refine ⟨25417224210208279207517579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67779264560555411220046877 25417224210208279207517579)
    ·
      refine ⟨38125836315312418811276369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25417224210208279207517579 38125836315312418811276369)
      ·
        refine ⟨28594377236484314108457277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38125836315312418811276369 28594377236484314108457277)
        ·
          refine ⟨10722891463681617790671479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28594377236484314108457277 10722891463681617790671479)
          ·
            refine ⟨16084337195522426686007219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10722891463681617790671479 16084337195522426686007219)
            ·
              refine ⟨24126505793283640029010829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16084337195522426686007219 24126505793283640029010829)
              ·
                refine ⟨9047439672481365010879061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24126505793283640029010829 9047439672481365010879061)
                ·
                  refine ⟨106024683661890996221239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9047439672481365010879061 106024683661890996221239)
                  ·
                    rfl

theorem cell23_1858341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_1858341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858341 prefixEnd_1858341 := by exact prefixLift 1858341
  have htrace : WordTrace (prefixWord ++ tailWord_1858341) baseStart_1858341 baseEnd_1858341 := by
    simpa [prefixWord, tailWord_1858341, baseEnd_1858341] using wordTrace_append hprefix tailTrace_1858341
  have hstable : (prefixWord ++ tailWord_1858341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858341).length < 2 ^ (prefixWord ++ tailWord_1858341).sum := by decide
  have hdescent : baseEnd_1858341 < baseStart_1858341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858396 : List Nat := [2, 2, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1858396 : Nat := 118140960795 + 1858396 * 2 ^ 59
def prefixEnd_1858396 : Nat := 4983230072969 + 3 ^ 40 * 1858396 * 2
def baseEnd_1858396 : Nat := 318083464797672083601133

theorem tailTrace_1858396 : CollatzResearch.WordTrace tailWord_1858396 prefixEnd_1858396 318083464797672083601133 := by
  unfold tailWord_1858396
  simp only [CollatzResearch.WordTrace]
  refine ⟨33890635287678077806649521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45187513716904103742199361 33890635287678077806649521)
  ·
    refine ⟨25417976465758558354987141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33890635287678077806649521 25417976465758558354987141)
    ·
      refine ⟨4765870587329729691560089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25417976465758558354987141 4765870587329729691560089)
      ·
        refine ⟨3574402940497297268670067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4765870587329729691560089 3574402940497297268670067)
        ·
          refine ⟨5361604410745945903005101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574402940497297268670067 5361604410745945903005101)
          ·
            refine ⟨2010601654029729713626913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5361604410745945903005101 2010601654029729713626913)
            ·
              refine ⟨1507951240522297285220185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010601654029729713626913 1507951240522297285220185)
              ·
                refine ⟨1130963430391722963915139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507951240522297285220185 1130963430391722963915139)
                ·
                  refine ⟨1696445145587584445872709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130963430391722963915139 1696445145587584445872709)
                  ·
                    refine ⟨318083464797672083601133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696445145587584445872709 318083464797672083601133)
                    ·
                      rfl

theorem cell23_1858396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1858396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858396 prefixEnd_1858396 := by exact prefixLift 1858396
  have htrace : WordTrace (prefixWord ++ tailWord_1858396) baseStart_1858396 baseEnd_1858396 := by
    simpa [prefixWord, tailWord_1858396, baseEnd_1858396] using wordTrace_append hprefix tailTrace_1858396
  have hstable : (prefixWord ++ tailWord_1858396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858396).length < 2 ^ (prefixWord ++ tailWord_1858396).sum := by decide
  have hdescent : baseEnd_1858396 < baseStart_1858396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858418 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_1858418 : Nat := 118140960795 + 1858418 * 2 ^ 59
def prefixEnd_1858418 : Nat := 4983230072969 + 3 ^ 40 * 1858418 * 2
def baseEnd_1858418 : Nat := 318087230322471721576099

theorem tailTrace_1858418 : CollatzResearch.WordTrace tailWord_1858418 prefixEnd_1858418 318087230322471721576099 := by
  unfold tailWord_1858418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945518245319113342649977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45188048654184302247066605 16945518245319113342649977)
  ·
    refine ⟨12709138683989335006987483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16945518245319113342649977 12709138683989335006987483)
    ·
      refine ⟨19063708025984002510481225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12709138683989335006987483 19063708025984002510481225)
      ·
        refine ⟨14297781019488001882860919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19063708025984002510481225 14297781019488001882860919)
        ·
          refine ⟨21446671529232002824291379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14297781019488001882860919 21446671529232002824291379)
          ·
            refine ⟨32170007293848004236437069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21446671529232002824291379 32170007293848004236437069)
            ·
              refine ⟨12063752735193001588663901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32170007293848004236437069 12063752735193001588663901)
              ·
                refine ⟨4523907275697375595748963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12063752735193001588663901 4523907275697375595748963)
                ·
                  refine ⟨6785860913546063393623445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4523907275697375595748963 6785860913546063393623445)
                  ·
                    refine ⟨318087230322471721576099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6785860913546063393623445 318087230322471721576099)
                    ·
                      rfl

theorem cell23_1858418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_1858418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858418 prefixEnd_1858418 := by exact prefixLift 1858418
  have htrace : WordTrace (prefixWord ++ tailWord_1858418) baseStart_1858418 baseEnd_1858418 := by
    simpa [prefixWord, tailWord_1858418, baseEnd_1858418] using wordTrace_append hprefix tailTrace_1858418
  have hstable : (prefixWord ++ tailWord_1858418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858418).length < 2 ^ (prefixWord ++ tailWord_1858418).sum := by decide
  have hdescent : baseEnd_1858418 < baseStart_1858418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858431 : List Nat := [1, 1, 2, 2, 1, 1, 4, 11]
def baseStart_1858431 : Nat := 118140960795 + 1858431 * 2 ^ 59
def prefixEnd_1858431 : Nat := 4983230072969 + 3 ^ 40 * 1858431 * 2
def baseEnd_1858431 : Nat := 35343272822811985698731

theorem tailTrace_1858431 : CollatzResearch.WordTrace tailWord_1858431 prefixEnd_1858431 35343272822811985698731 := by
  unfold tailWord_1858431
  simp only [CollatzResearch.WordTrace]
  refine ⟨67782547130229356590823147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45188364753486237727215431 67782547130229356590823147)
  ·
    refine ⟨101673820695344034886234721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67782547130229356590823147 101673820695344034886234721)
    ·
      refine ⟨76255365521508026164676041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101673820695344034886234721 76255365521508026164676041)
      ·
        refine ⟨57191524141131019623507031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76255365521508026164676041 57191524141131019623507031)
        ·
          refine ⟨85787286211696529435260547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57191524141131019623507031 85787286211696529435260547)
          ·
            refine ⟨128680929317544794152890821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85787286211696529435260547 128680929317544794152890821)
            ·
              refine ⟨24127674247039648903667029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128680929317544794152890821 24127674247039648903667029)
              ·
                refine ⟨35343272822811985698731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24127674247039648903667029 35343272822811985698731)
                ·
                  rfl

theorem cell23_1858431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 11].length) (baseStart_1858431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858431 prefixEnd_1858431 := by exact prefixLift 1858431
  have htrace : WordTrace (prefixWord ++ tailWord_1858431) baseStart_1858431 baseEnd_1858431 := by
    simpa [prefixWord, tailWord_1858431, baseEnd_1858431] using wordTrace_append hprefix tailTrace_1858431
  have hstable : (prefixWord ++ tailWord_1858431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858431).length < 2 ^ (prefixWord ++ tailWord_1858431).sum := by decide
  have hdescent : baseEnd_1858431 < baseStart_1858431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858442 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1858442 : Nat := 118140960795 + 1858442 * 2 ^ 59
def prefixEnd_1858442 : Nat := 4983230072969 + 3 ^ 40 * 1858442 * 2
def baseEnd_1858442 : Nat := 954274014503123070828187

theorem tailTrace_1858442 : CollatzResearch.WordTrace tailWord_1858442 prefixEnd_1858442 954274014503123070828187 := by
  unfold tailWord_1858442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945737083297376367368395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45188632222126336979649053 16945737083297376367368395)
  ·
    refine ⟨25418605624946064551052593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16945737083297376367368395 25418605624946064551052593)
    ·
      refine ⟨19063954218709548413289445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25418605624946064551052593 19063954218709548413289445)
      ·
        refine ⟨3574491416008040327491771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19063954218709548413289445 3574491416008040327491771)
        ·
          refine ⟨5361737124012060491237657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574491416008040327491771 5361737124012060491237657)
          ·
            refine ⟨4021302843009045368428243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5361737124012060491237657 4021302843009045368428243)
            ·
              refine ⟨6031954264513568052642365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021302843009045368428243 6031954264513568052642365)
              ·
                refine ⟨2261982849192588019740887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6031954264513568052642365 2261982849192588019740887)
                ·
                  refine ⟨3392974273788882029611331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261982849192588019740887 3392974273788882029611331)
                  ·
                    refine ⟨5089461410683323044416997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3392974273788882029611331 5089461410683323044416997)
                    ·
                      refine ⟨954274014503123070828187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5089461410683323044416997 954274014503123070828187)
                      ·
                        rfl

theorem cell23_1858442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1858442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858442 prefixEnd_1858442 := by exact prefixLift 1858442
  have htrace : WordTrace (prefixWord ++ tailWord_1858442) baseStart_1858442 baseEnd_1858442 := by
    simpa [prefixWord, tailWord_1858442, baseEnd_1858442] using wordTrace_append hprefix tailTrace_1858442
  have hstable : (prefixWord ++ tailWord_1858442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858442).length < 2 ^ (prefixWord ++ tailWord_1858442).sum := by decide
  have hdescent : baseEnd_1858442 < baseStart_1858442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858488 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1858488 : Nat := 118140960795 + 1858488 * 2 ^ 59
def prefixEnd_1858488 : Nat := 4983230072969 + 3 ^ 40 * 1858488 * 2
def baseEnd_1858488 : Nat := 954297634613229890852975

theorem tailTrace_1858488 : CollatzResearch.WordTrace tailWord_1858488 prefixEnd_1858488 954297634613229890852975 := by
  unfold tailWord_1858488
  simp only [CollatzResearch.WordTrace]
  refine ⟨33892313045511427662824059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45189750727348570217098745 33892313045511427662824059)
  ·
    refine ⟨50838469568267141494236089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33892313045511427662824059 50838469568267141494236089)
    ·
      refine ⟨38128852176200356120677067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50838469568267141494236089 38128852176200356120677067)
      ·
        refine ⟨57193278264300534181015601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38128852176200356120677067 57193278264300534181015601)
        ·
          refine ⟨42894958698225400635761701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57193278264300534181015601 42894958698225400635761701)
          ·
            refine ⟨8042804755917262619205319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42894958698225400635761701 8042804755917262619205319)
            ·
              refine ⟨12064207133875893928807979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042804755917262619205319 12064207133875893928807979)
              ·
                refine ⟨18096310700813840893211969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064207133875893928807979 18096310700813840893211969)
                ·
                  refine ⟨13572233025610380669908977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18096310700813840893211969 13572233025610380669908977)
                  ·
                    refine ⟨10179174769207785502431733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13572233025610380669908977 10179174769207785502431733)
                    ·
                      refine ⟨954297634613229890852975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10179174769207785502431733 954297634613229890852975)
                      ·
                        rfl

theorem cell23_1858488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1858488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858488 prefixEnd_1858488 := by exact prefixLift 1858488
  have htrace : WordTrace (prefixWord ++ tailWord_1858488) baseStart_1858488 baseEnd_1858488 := by
    simpa [prefixWord, tailWord_1858488, baseEnd_1858488] using wordTrace_append hprefix tailTrace_1858488
  have hstable : (prefixWord ++ tailWord_1858488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858488).length < 2 ^ (prefixWord ++ tailWord_1858488).sum := by decide
  have hdescent : baseEnd_1858488 < baseStart_1858488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858493 : List Nat := [1, 4, 1, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_1858493 : Nat := 118140960795 + 1858493 * 2 ^ 59
def prefixEnd_1858493 : Nat := 4983230072969 + 3 ^ 40 * 1858493 * 2
def baseEnd_1858493 : Nat := 954300202016502371290453

theorem tailTrace_1858493 : CollatzResearch.WordTrace tailWord_1858493 prefixEnd_1858493 954300202016502371290453 := by
  unfold tailWord_1858493
  simp only [CollatzResearch.WordTrace]
  refine ⟨67784808456004741179580133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45189872304003160786386755 67784808456004741179580133)
  ·
    refine ⟨12709651585500888971171275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67784808456004741179580133 12709651585500888971171275)
    ·
      refine ⟨19064477378251333456756913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12709651585500888971171275 19064477378251333456756913)
      ·
        refine ⟨14298358033688500092567685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19064477378251333456756913 14298358033688500092567685)
        ·
          refine ⟨2680942131316593767356441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14298358033688500092567685 2680942131316593767356441)
          ·
            refine ⟨2010706598487445325517331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2680942131316593767356441 2010706598487445325517331)
            ·
              refine ⟨3016059897731167988275997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010706598487445325517331 3016059897731167988275997)
              ·
                refine ⟨1131022461649187995603499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3016059897731167988275997 1131022461649187995603499)
                ·
                  refine ⟨1696533692473781993405249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131022461649187995603499 1696533692473781993405249)
                  ·
                    refine ⟨1272400269355336495053937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1696533692473781993405249 1272400269355336495053937)
                    ·
                      refine ⟨954300202016502371290453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272400269355336495053937 954300202016502371290453)
                      ·
                        rfl

theorem cell23_1858493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_1858493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858493 prefixEnd_1858493 := by exact prefixLift 1858493
  have htrace : WordTrace (prefixWord ++ tailWord_1858493) baseStart_1858493 baseEnd_1858493 := by
    simpa [prefixWord, tailWord_1858493, baseEnd_1858493] using wordTrace_append hprefix tailTrace_1858493
  have hstable : (prefixWord ++ tailWord_1858493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858493).length < 2 ^ (prefixWord ++ tailWord_1858493).sum := by decide
  have hdescent : baseEnd_1858493 < baseStart_1858493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858532 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_1858532 : Nat := 118140960795 + 1858532 * 2 ^ 59
def prefixEnd_1858532 : Nat := 4983230072969 + 3 ^ 40 * 1858532 * 2
def baseEnd_1858532 : Nat := 954320227762027718702773

theorem tailTrace_1858532 : CollatzResearch.WordTrace tailWord_1858532 prefixEnd_1858532 954320227762027718702773 := by
  unfold tailWord_1858532
  simp only [CollatzResearch.WordTrace]
  refine ⟨33893115451431725420124925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45190820601908967226833233 33893115451431725420124925)
  ·
    refine ⟨12709918294286897032546847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33893115451431725420124925 12709918294286897032546847)
    ·
      refine ⟨19064877441430345548820271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12709918294286897032546847 19064877441430345548820271)
      ·
        refine ⟨28597316162145518323230407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19064877441430345548820271 28597316162145518323230407)
        ·
          refine ⟨42895974243218277484845611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28597316162145518323230407 42895974243218277484845611)
          ·
            refine ⟨64343961364827416227268417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42895974243218277484845611 64343961364827416227268417)
            ·
              refine ⟨48257971023620562170451313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64343961364827416227268417 48257971023620562170451313)
              ·
                refine ⟨36193478267715421627838485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48257971023620562170451313 36193478267715421627838485)
                ·
                  refine ⟨1696569293799160388804929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36193478267715421627838485 1696569293799160388804929)
                  ·
                    refine ⟨1272426970349370291603697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1696569293799160388804929 1272426970349370291603697)
                    ·
                      refine ⟨954320227762027718702773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272426970349370291603697 954320227762027718702773)
                      ·
                        rfl

theorem cell23_1858532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_1858532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858532 prefixEnd_1858532 := by exact prefixLift 1858532
  have htrace : WordTrace (prefixWord ++ tailWord_1858532) baseStart_1858532 baseEnd_1858532 := by
    simpa [prefixWord, tailWord_1858532, baseEnd_1858532] using wordTrace_append hprefix tailTrace_1858532
  have hstable : (prefixWord ++ tailWord_1858532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858532).length < 2 ^ (prefixWord ++ tailWord_1858532).sum := by decide
  have hdescent : baseEnd_1858532 < baseStart_1858532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858535 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1858535 : Nat := 118140960795 + 1858535 * 2 ^ 59
def prefixEnd_1858535 : Nat := 4983230072969 + 3 ^ 40 * 1858535 * 2
def baseEnd_1858535 : Nat := 954321768203991206965259

theorem tailTrace_1858535 : CollatzResearch.WordTrace tailWord_1858535 prefixEnd_1858535 954321768203991206965259 := by
  unfold tailWord_1858535
  simp only [CollatzResearch.WordTrace]
  refine ⟨67786340321852582352609059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45190893547901721568406039 67786340321852582352609059)
  ·
    refine ⟨101679510482778873528913589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67786340321852582352609059 101679510482778873528913589)
    ·
      refine ⟨9532454107760519393335649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101679510482778873528913589 9532454107760519393335649)
      ·
        refine ⟨7149340580820389545001737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9532454107760519393335649 7149340580820389545001737)
        ·
          refine ⟨5362005435615292158751303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7149340580820389545001737 5362005435615292158751303)
          ·
            refine ⟨8043008153422938238126955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362005435615292158751303 8043008153422938238126955)
            ·
              refine ⟨12064512230134407357190433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043008153422938238126955 12064512230134407357190433)
              ·
                refine ⟨9048384172600805517892825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12064512230134407357190433 9048384172600805517892825)
                ·
                  refine ⟨6786288129450604138419619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9048384172600805517892825 6786288129450604138419619)
                  ·
                    refine ⟨10179432194175906207629429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6786288129450604138419619 10179432194175906207629429)
                    ·
                      refine ⟨954321768203991206965259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10179432194175906207629429 954321768203991206965259)
                      ·
                        rfl

theorem cell23_1858535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1858535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858535 prefixEnd_1858535 := by exact prefixLift 1858535
  have htrace : WordTrace (prefixWord ++ tailWord_1858535) baseStart_1858535 baseEnd_1858535 := by
    simpa [prefixWord, tailWord_1858535, baseEnd_1858535] using wordTrace_append hprefix tailTrace_1858535
  have hstable : (prefixWord ++ tailWord_1858535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858535).length < 2 ^ (prefixWord ++ tailWord_1858535).sum := by decide
  have hdescent : baseEnd_1858535 < baseStart_1858535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858555 : List Nat := [1, 1, 1, 1, 1, 3, 3, 7, 5]
def baseStart_1858555 : Nat := 118140960795 + 1858555 * 2 ^ 59
def prefixEnd_1858555 : Nat := 4983230072969 + 3 ^ 40 * 1858555 * 2
def baseEnd_1858555 : Nat := 106036893090786792079463

theorem tailTrace_1858555 : CollatzResearch.WordTrace tailWord_1858555 prefixEnd_1858555 106036893090786792079463 := by
  unfold tailWord_1858555
  simp only [CollatzResearch.WordTrace]
  refine ⟨67787069781780125768337119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45191379854520083845558079 67787069781780125768337119)
  ·
    refine ⟨101680604672670188652505679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67787069781780125768337119 101680604672670188652505679)
    ·
      refine ⟨152520907009005282978758519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101680604672670188652505679 152520907009005282978758519)
      ·
        refine ⟨228781360513507924468137779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152520907009005282978758519 228781360513507924468137779)
        ·
          refine ⟨343172040770261886702206669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228781360513507924468137779 343172040770261886702206669)
          ·
            refine ⟨128689515288848207513327501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343172040770261886702206669 128689515288848207513327501)
            ·
              refine ⟨48258568233318077817497813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128689515288848207513327501 48258568233318077817497813)
              ·
                refine ⟨1131060192968392448847605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48258568233318077817497813 1131060192968392448847605)
                ·
                  refine ⟨106036893090786792079463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1131060192968392448847605 106036893090786792079463)
                  ·
                    rfl

theorem cell23_1858555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 5].length) (baseStart_1858555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858555 prefixEnd_1858555 := by exact prefixLift 1858555
  have htrace : WordTrace (prefixWord ++ tailWord_1858555) baseStart_1858555 baseEnd_1858555 := by
    simpa [prefixWord, tailWord_1858555, baseEnd_1858555] using wordTrace_append hprefix tailTrace_1858555
  have hstable : (prefixWord ++ tailWord_1858555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858555).length < 2 ^ (prefixWord ++ tailWord_1858555).sum := by decide
  have hdescent : baseEnd_1858555 < baseStart_1858555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858565 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_1858565 : Nat := 118140960795 + 1858565 * 2 ^ 59
def prefixEnd_1858565 : Nat := 4983230072969 + 3 ^ 40 * 1858565 * 2
def baseEnd_1858565 : Nat := 954337172623626089590121

theorem tailTrace_1858565 : CollatzResearch.WordTrace tailWord_1858565 prefixEnd_1858565 954337172623626089590121 := by
  unfold tailWord_1858565
  simp only [CollatzResearch.WordTrace]
  refine ⟨67787434511743897476201149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45191623007829264984134099 67787434511743897476201149)
  ·
    refine ⟨25420287941903961553575431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67787434511743897476201149 25420287941903961553575431)
    ·
      refine ⟨38130431912855942330363147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25420287941903961553575431 38130431912855942330363147)
      ·
        refine ⟨57195647869283913495544721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38130431912855942330363147 57195647869283913495544721)
        ·
          refine ⟨42896735901962935121658541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57195647869283913495544721 42896735901962935121658541)
          ·
            refine ⟨16086275963236100670621953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42896735901962935121658541 16086275963236100670621953)
            ·
              refine ⟨12064706972427075502966465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16086275963236100670621953 12064706972427075502966465)
              ·
                refine ⟨9048530229320306627224849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12064706972427075502966465 9048530229320306627224849)
                ·
                  refine ⟨6786397671990229970418637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9048530229320306627224849 6786397671990229970418637)
                  ·
                    refine ⟨2544899126996336238906989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6786397671990229970418637 2544899126996336238906989)
                    ·
                      refine ⟨954337172623626089590121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2544899126996336238906989 954337172623626089590121)
                      ·
                        rfl

theorem cell23_1858565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_1858565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858565 prefixEnd_1858565 := by exact prefixLift 1858565
  have htrace : WordTrace (prefixWord ++ tailWord_1858565) baseStart_1858565 baseEnd_1858565 := by
    simpa [prefixWord, tailWord_1858565, baseEnd_1858565] using wordTrace_append hprefix tailTrace_1858565
  have hstable : (prefixWord ++ tailWord_1858565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858565).length < 2 ^ (prefixWord ++ tailWord_1858565).sum := by decide
  have hdescent : baseEnd_1858565 < baseStart_1858565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858572 : List Nat := [2, 2, 1, 2, 3, 3, 1, 4, 5]
def baseStart_1858572 : Nat := 118140960795 + 1858572 * 2 ^ 59
def prefixEnd_1858572 : Nat := 4983230072969 + 3 ^ 40 * 1858572 * 2
def baseEnd_1858572 : Nat := 106037862998689729133621

theorem tailTrace_1858572 : CollatzResearch.WordTrace tailWord_1858572 prefixEnd_1858572 106037862998689729133621 := by
  unfold tailWord_1858572
  simp only [CollatzResearch.WordTrace]
  refine ⟨33893844911359268835852985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45191793215145691781137313 33893844911359268835852985)
  ·
    refine ⟨25420383683519451626889739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33893844911359268835852985 25420383683519451626889739)
    ·
      refine ⟨38130575525279177440334609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25420383683519451626889739 38130575525279177440334609)
      ·
        refine ⟨28597931643959383080250957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38130575525279177440334609 28597931643959383080250957)
        ·
          refine ⟨10724224366484768655094109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28597931643959383080250957 10724224366484768655094109)
          ·
            refine ⟨4021584137431788245660291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10724224366484768655094109 4021584137431788245660291)
            ·
              refine ⟨6032376206147682368490437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021584137431788245660291 6032376206147682368490437)
              ·
                refine ⟨1131070538652690444091957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6032376206147682368490437 1131070538652690444091957)
                ·
                  refine ⟨106037862998689729133621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1131070538652690444091957 106037862998689729133621)
                  ·
                    rfl

theorem cell23_1858572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_1858572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858572 prefixEnd_1858572 := by exact prefixLift 1858572
  have htrace : WordTrace (prefixWord ++ tailWord_1858572) baseStart_1858572 baseEnd_1858572 := by
    simpa [prefixWord, tailWord_1858572, baseEnd_1858572] using wordTrace_append hprefix tailTrace_1858572
  have hstable : (prefixWord ++ tailWord_1858572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858572).length < 2 ^ (prefixWord ++ tailWord_1858572).sum := by decide
  have hdescent : baseEnd_1858572 < baseStart_1858572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858602 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1858602 : Nat := 118140960795 + 1858602 * 2 ^ 59
def prefixEnd_1858602 : Nat := 4983230072969 + 3 ^ 40 * 1858602 * 2
def baseEnd_1858602 : Nat := 318118723802614148275817

theorem tailTrace_1858602 : CollatzResearch.WordTrace tailWord_1858602 prefixEnd_1858602 318118723802614148275817 := by
  unfold tailWord_1858602
  simp only [CollatzResearch.WordTrace]
  refine ⟨16947196003152463198824515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45192522675073235196865373 16947196003152463198824515)
  ·
    refine ⟨25420794004728694798236773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16947196003152463198824515 25420794004728694798236773)
    ·
      refine ⟨4766398875886630274669395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25420794004728694798236773 4766398875886630274669395)
      ·
        refine ⟨7149598313829945412004093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766398875886630274669395 7149598313829945412004093)
        ·
          refine ⟨2681099367686229529501535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7149598313829945412004093 2681099367686229529501535)
          ·
            refine ⟨4021649051529344294252303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681099367686229529501535 4021649051529344294252303)
            ·
              refine ⟨6032473577294016441378455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021649051529344294252303 6032473577294016441378455)
              ·
                refine ⟨9048710365941024662067683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6032473577294016441378455 9048710365941024662067683)
                ·
                  refine ⟨13573065548911536993101525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9048710365941024662067683 13573065548911536993101525)
                  ·
                    refine ⟨318118723802614148275817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13573065548911536993101525 318118723802614148275817)
                    ·
                      rfl

theorem cell23_1858602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1858602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858602 prefixEnd_1858602 := by exact prefixLift 1858602
  have htrace : WordTrace (prefixWord ++ tailWord_1858602) baseStart_1858602 baseEnd_1858602 := by
    simpa [prefixWord, tailWord_1858602, baseEnd_1858602] using wordTrace_append hprefix tailTrace_1858602
  have hstable : (prefixWord ++ tailWord_1858602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858602).length < 2 ^ (prefixWord ++ tailWord_1858602).sum := by decide
  have hdescent : baseEnd_1858602 < baseStart_1858602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858615 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 7, 4]
def baseStart_1858615 : Nat := 118140960795 + 1858615 * 2 ^ 59
def prefixEnd_1858615 : Nat := 4983230072969 + 3 ^ 40 * 1858615 * 2
def baseEnd_1858615 : Nat := 318120948885450297988297

theorem tailTrace_1858615 : CollatzResearch.WordTrace tailWord_1858615 prefixEnd_1858615 318120948885450297988297 := by
  unfold tailWord_1858615
  simp only [CollatzResearch.WordTrace]
  refine ⟨67789258161562756015521299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45192838774375170677014199 67789258161562756015521299)
  ·
    refine ⟨101683887242344134023281949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67789258161562756015521299 101683887242344134023281949)
    ·
      refine ⟨38131457715879050258730731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101683887242344134023281949 38131457715879050258730731)
      ·
        refine ⟨57197186573818575388096097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38131457715879050258730731 57197186573818575388096097)
        ·
          refine ⟨42897889930363931541072073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57197186573818575388096097 42897889930363931541072073)
          ·
            refine ⟨32173417447772948655804055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42897889930363931541072073 32173417447772948655804055)
            ·
              refine ⟨48260126171659422983706083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32173417447772948655804055 48260126171659422983706083)
              ·
                refine ⟨72390189257489134475559125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48260126171659422983706083 72390189257489134475559125)
                ·
                  refine ⟨1696645060722401589270917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 72390189257489134475559125 1696645060722401589270917)
                  ·
                    refine ⟨318120948885450297988297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696645060722401589270917 318120948885450297988297)
                    ·
                      rfl

theorem cell23_1858615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_1858615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858615 prefixEnd_1858615 := by exact prefixLift 1858615
  have htrace : WordTrace (prefixWord ++ tailWord_1858615) baseStart_1858615 baseEnd_1858615 := by
    simpa [prefixWord, tailWord_1858615, baseEnd_1858615] using wordTrace_append hprefix tailTrace_1858615
  have hstable : (prefixWord ++ tailWord_1858615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858615).length < 2 ^ (prefixWord ++ tailWord_1858615).sum := by decide
  have hdescent : baseEnd_1858615 < baseStart_1858615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858632 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 3, 4]
def baseStart_1858632 : Nat := 118140960795 + 1858632 * 2 ^ 59
def prefixEnd_1858632 : Nat := 4983230072969 + 3 ^ 40 * 1858632 * 2
def baseEnd_1858632 : Nat := 318123858609159109150771

theorem tailTrace_1858632 : CollatzResearch.WordTrace tailWord_1858632 prefixEnd_1858632 318123858609159109150771 := by
  unfold tailWord_1858632
  simp only [CollatzResearch.WordTrace]
  refine ⟨33894939101250583959445075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45193252135000778612593433 33894939101250583959445075)
  ·
    refine ⟨50842408651875875939167613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33894939101250583959445075 50842408651875875939167613)
    ·
      refine ⟨19065903244453453477187855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50842408651875875939167613 19065903244453453477187855)
      ·
        refine ⟨28598854866680180215781783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19065903244453453477187855 28598854866680180215781783)
        ·
          refine ⟨42898282300020270323672675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28598854866680180215781783 42898282300020270323672675)
          ·
            refine ⟨64347423450030405485509013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42898282300020270323672675 64347423450030405485509013)
            ·
              refine ⟨3016285474220175257133235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64347423450030405485509013 3016285474220175257133235)
              ·
                refine ⟨4524428211330262885699853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016285474220175257133235 4524428211330262885699853)
                ·
                  refine ⟨1696660579248848582137445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4524428211330262885699853 1696660579248848582137445)
                  ·
                    refine ⟨318123858609159109150771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696660579248848582137445 318123858609159109150771)
                    ·
                      rfl

theorem cell23_1858632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_1858632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858632 prefixEnd_1858632 := by exact prefixLift 1858632
  have htrace : WordTrace (prefixWord ++ tailWord_1858632) baseStart_1858632 baseEnd_1858632 := by
    simpa [prefixWord, tailWord_1858632, baseEnd_1858632] using wordTrace_append hprefix tailTrace_1858632
  have hstable : (prefixWord ++ tailWord_1858632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858632).length < 2 ^ (prefixWord ++ tailWord_1858632).sum := by decide
  have hdescent : baseEnd_1858632 < baseStart_1858632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858642 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_1858642 : Nat := 118140960795 + 1858642 * 2 ^ 59
def prefixEnd_1858642 : Nat := 4983230072969 + 3 ^ 40 * 1858642 * 2
def baseEnd_1858642 : Nat := 954376710634022288327267

theorem tailTrace_1858642 : CollatzResearch.WordTrace tailWord_1858642 prefixEnd_1858642 954376710634022288327267 := by
  unfold tailWord_1858642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16947560733116234906688545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45193495288309959751169453 16947560733116234906688545)
  ·
    refine ⟨12710670549837176180016409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16947560733116234906688545 12710670549837176180016409)
    ·
      refine ⟨9533002912377882135012307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12710670549837176180016409 9533002912377882135012307)
      ·
        refine ⟨14299504368566823202518461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9533002912377882135012307 14299504368566823202518461)
        ·
          refine ⟨5362314138212558700944423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14299504368566823202518461 5362314138212558700944423)
          ·
            refine ⟨8043471207318838051416635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362314138212558700944423 8043471207318838051416635)
            ·
              refine ⟨12065206810978257077124953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043471207318838051416635 12065206810978257077124953)
              ·
                refine ⟨9048905108233692807843715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12065206810978257077124953 9048905108233692807843715)
                ·
                  refine ⟨13573357662350539211765573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9048905108233692807843715 13573357662350539211765573)
                  ·
                    refine ⟨2545004561690726102206045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13573357662350539211765573 2545004561690726102206045)
                    ·
                      refine ⟨954376710634022288327267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2545004561690726102206045 954376710634022288327267)
                      ·
                        rfl

theorem cell23_1858642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_1858642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858642 prefixEnd_1858642 := by exact prefixLift 1858642
  have htrace : WordTrace (prefixWord ++ tailWord_1858642) baseStart_1858642 baseEnd_1858642 := by
    simpa [prefixWord, tailWord_1858642, baseEnd_1858642] using wordTrace_append hprefix tailTrace_1858642
  have hstable : (prefixWord ++ tailWord_1858642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858642).length < 2 ^ (prefixWord ++ tailWord_1858642).sum := by decide
  have hdescent : baseEnd_1858642 < baseStart_1858642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858655 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 3]
def baseStart_1858655 : Nat := 118140960795 + 1858655 * 2 ^ 59
def prefixEnd_1858655 : Nat := 4983230072969 + 3 ^ 40 * 1858655 * 2
def baseEnd_1858655 : Nat := 954383385882530737464707

theorem tailTrace_1858655 : CollatzResearch.WordTrace tailWord_1858655 prefixEnd_1858655 954383385882530737464707 := by
  unfold tailWord_1858655
  simp only [CollatzResearch.WordTrace]
  refine ⟨67790717081417842846977419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45193811387611895231318279 67790717081417842846977419)
  ·
    refine ⟨101686075622126764270466129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67790717081417842846977419 101686075622126764270466129)
    ·
      refine ⟨76264556716595073202849597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101686075622126764270466129 76264556716595073202849597)
      ·
        refine ⟨28599208768723152451068599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76264556716595073202849597 28599208768723152451068599)
        ·
          refine ⟨42898813153084728676602899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28599208768723152451068599 42898813153084728676602899)
          ·
            refine ⟨64348219729627093014904349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42898813153084728676602899 64348219729627093014904349)
            ·
              refine ⟨24130582398610159880589131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64348219729627093014904349 24130582398610159880589131)
              ·
                refine ⟨36195873597915239820883697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24130582398610159880589131 36195873597915239820883697)
                ·
                  refine ⟨27146905198436429865662773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36195873597915239820883697 27146905198436429865662773)
                  ·
                    refine ⟨2545022362353415299905885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27146905198436429865662773 2545022362353415299905885)
                    ·
                      refine ⟨954383385882530737464707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2545022362353415299905885 954383385882530737464707)
                      ·
                        rfl

theorem cell23_1858655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_1858655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858655 prefixEnd_1858655 := by exact prefixLift 1858655
  have htrace : WordTrace (prefixWord ++ tailWord_1858655) baseStart_1858655 baseEnd_1858655 := by
    simpa [prefixWord, tailWord_1858655, baseEnd_1858655] using wordTrace_append hprefix tailTrace_1858655
  have hstable : (prefixWord ++ tailWord_1858655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858655).length < 2 ^ (prefixWord ++ tailWord_1858655).sum := by decide
  have hdescent : baseEnd_1858655 < baseStart_1858655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858666 : List Nat := [3, 1, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_1858666 : Nat := 118140960795 + 1858666 * 2 ^ 59
def prefixEnd_1858666 : Nat := 4983230072969 + 3 ^ 40 * 1858666 * 2
def baseEnd_1858666 : Nat := 318129678056576731475719

theorem tailTrace_1858666 : CollatzResearch.WordTrace tailWord_1858666 prefixEnd_1858666 318129678056576731475719 := by
  unfold tailWord_1858666
  simp only [CollatzResearch.WordTrace]
  refine ⟨16947779571094497931406963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45194078856251994483751901 16947779571094497931406963)
  ·
    refine ⟨25421669356641746897110445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16947779571094497931406963 25421669356641746897110445)
    ·
      refine ⟨9533126008740655086416417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25421669356641746897110445 9533126008740655086416417)
      ·
        refine ⟨7149844506555491314812313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9533126008740655086416417 7149844506555491314812313)
        ·
          refine ⟨5362383379916618486109235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7149844506555491314812313 5362383379916618486109235)
          ·
            refine ⟨8043575069874927729163853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362383379916618486109235 8043575069874927729163853)
            ·
              refine ⟨3016340651203097898436445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8043575069874927729163853 3016340651203097898436445)
              ·
                refine ⟨1131127744201161711913667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3016340651203097898436445 1131127744201161711913667)
                ·
                  refine ⟨1696691616301742567870501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131127744201161711913667 1696691616301742567870501)
                  ·
                    refine ⟨318129678056576731475719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696691616301742567870501 318129678056576731475719)
                    ·
                      rfl

theorem cell23_1858666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_1858666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858666 prefixEnd_1858666 := by exact prefixLift 1858666
  have htrace : WordTrace (prefixWord ++ tailWord_1858666) baseStart_1858666 baseEnd_1858666 := by
    simpa [prefixWord, tailWord_1858666, baseEnd_1858666] using wordTrace_append hprefix tailTrace_1858666
  have hstable : (prefixWord ++ tailWord_1858666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858666).length < 2 ^ (prefixWord ++ tailWord_1858666).sum := by decide
  have hdescent : baseEnd_1858666 < baseStart_1858666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858695 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1858695 : Nat := 118140960795 + 1858695 * 2 ^ 59
def prefixEnd_1858695 : Nat := 4983230072969 + 3 ^ 40 * 1858695 * 2
def baseEnd_1858695 : Nat := 954403925108710580964523

theorem tailTrace_1858695 : CollatzResearch.WordTrace tailWord_1858695 prefixEnd_1858695 954403925108710580964523 := by
  unfold tailWord_1858695
  simp only [CollatzResearch.WordTrace]
  refine ⟨67792176001272929678433539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45194784000848619785622359 67792176001272929678433539)
  ·
    refine ⟨101688264001909394517650309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67792176001272929678433539 101688264001909394517650309)
    ·
      refine ⟨19066549500358011472059433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101688264001909394517650309 19066549500358011472059433)
      ·
        refine ⟨14299912125268508604044575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19066549500358011472059433 14299912125268508604044575)
        ·
          refine ⟨21449868187902762906066863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14299912125268508604044575 21449868187902762906066863)
          ·
            refine ⟨32174802281854144359100295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21449868187902762906066863 32174802281854144359100295)
            ·
              refine ⟨48262203422781216538650443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32174802281854144359100295 48262203422781216538650443)
              ·
                refine ⟨72393305134171824807975665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48262203422781216538650443 72393305134171824807975665)
                ·
                  refine ⟨54294978850628868605981749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72393305134171824807975665 54294978850628868605981749)
                  ·
                    refine ⟨5090154267246456431810789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54294978850628868605981749 5090154267246456431810789)
                    ·
                      refine ⟨954403925108710580964523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5090154267246456431810789 954403925108710580964523)
                      ·
                        rfl

theorem cell23_1858695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1858695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858695 prefixEnd_1858695 := by exact prefixLift 1858695
  have htrace : WordTrace (prefixWord ++ tailWord_1858695) baseStart_1858695 baseEnd_1858695 := by
    simpa [prefixWord, tailWord_1858695, baseEnd_1858695] using wordTrace_append hprefix tailTrace_1858695
  have hstable : (prefixWord ++ tailWord_1858695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858695).length < 2 ^ (prefixWord ++ tailWord_1858695).sum := by decide
  have hdescent : baseEnd_1858695 < baseStart_1858695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858696 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 6]
def baseStart_1858696 : Nat := 118140960795 + 1858696 * 2 ^ 59
def prefixEnd_1858696 : Nat := 4983230072969 + 3 ^ 40 * 1858696 * 2
def baseEnd_1858696 : Nat := 106044937621040564116891

theorem tailTrace_1858696 : CollatzResearch.WordTrace tailWord_1858696 prefixEnd_1858696 106044937621040564116891 := by
  unfold tailWord_1858696
  simp only [CollatzResearch.WordTrace]
  refine ⟨33896106237134653424609971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45194808316179537899479961 33896106237134653424609971)
  ·
    refine ⟨50844159355701980136914957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33896106237134653424609971 50844159355701980136914957)
    ·
      refine ⟨19066559758388242551343109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50844159355701980136914957 19066559758388242551343109)
      ·
        refine ⟨3574979954697795478376833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19066559758388242551343109 3574979954697795478376833)
        ·
          refine ⟨2681234966023346608782625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3574979954697795478376833 2681234966023346608782625)
          ·
            refine ⟨2010926224517509956586969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2681234966023346608782625 2010926224517509956586969)
            ·
              refine ⟨1508194668388132467440227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010926224517509956586969 1508194668388132467440227)
              ·
                refine ⟨2262292002582198701160341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508194668388132467440227 2262292002582198701160341)
                ·
                  refine ⟨106044937621040564116891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2262292002582198701160341 106044937621040564116891)
                  ·
                    rfl

theorem cell23_1858696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 6].length) (baseStart_1858696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858696 prefixEnd_1858696 := by exact prefixLift 1858696
  have htrace : WordTrace (prefixWord ++ tailWord_1858696) baseStart_1858696 baseEnd_1858696 := by
    simpa [prefixWord, tailWord_1858696, baseEnd_1858696] using wordTrace_append hprefix tailTrace_1858696
  have hstable : (prefixWord ++ tailWord_1858696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858696).length < 2 ^ (prefixWord ++ tailWord_1858696).sum := by decide
  have hdescent : baseEnd_1858696 < baseStart_1858696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858716 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_1858716 : Nat := 118140960795 + 1858716 * 2 ^ 59
def prefixEnd_1858716 : Nat := 4983230072969 + 3 ^ 40 * 1858716 * 2
def baseEnd_1858716 : Nat := 954414708202454998801927

theorem tailTrace_1858716 : CollatzResearch.WordTrace tailWord_1858716 prefixEnd_1858716 954414708202454998801927 := by
  unfold tailWord_1858716
  simp only [CollatzResearch.WordTrace]
  refine ⟨33896470967098425132474001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45195294622797900176632001 33896470967098425132474001)
  ·
    refine ⟨25422353225323818849355501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33896470967098425132474001 25422353225323818849355501)
    ·
      refine ⟨9533382459496432068508313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25422353225323818849355501 9533382459496432068508313)
      ·
        refine ⟨7150036844622324051381235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9533382459496432068508313 7150036844622324051381235)
        ·
          refine ⟨10725055266933486077071853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7150036844622324051381235 10725055266933486077071853)
          ·
            refine ⟨4021895725100057278901945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10725055266933486077071853 4021895725100057278901945)
            ·
              refine ⟨3016421793825042959176459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021895725100057278901945 3016421793825042959176459)
              ·
                refine ⟨4524632690737564438764689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016421793825042959176459 4524632690737564438764689)
                ·
                  refine ⟨3393474518053173329073517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4524632690737564438764689 3393474518053173329073517)
                  ·
                    refine ⟨1272552944269939998402569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393474518053173329073517 1272552944269939998402569)
                    ·
                      refine ⟨954414708202454998801927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272552944269939998402569 954414708202454998801927)
                      ·
                        rfl

theorem cell23_1858716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_1858716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858716 prefixEnd_1858716 := by exact prefixLift 1858716
  have htrace : WordTrace (prefixWord ++ tailWord_1858716) baseStart_1858716 baseEnd_1858716 := by
    simpa [prefixWord, tailWord_1858716, baseEnd_1858716] using wordTrace_append hprefix tailTrace_1858716
  have hstable : (prefixWord ++ tailWord_1858716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858716).length < 2 ^ (prefixWord ++ tailWord_1858716).sum := by decide
  have hdescent : baseEnd_1858716 < baseStart_1858716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858796 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_1858796 : Nat := 118140960795 + 1858796 * 2 ^ 59
def prefixEnd_1858796 : Nat := 4983230072969 + 3 ^ 40 * 1858796 * 2
def baseEnd_1858796 : Nat := 954455786654814685801559

theorem tailTrace_1858796 : CollatzResearch.WordTrace tailWord_1858796 prefixEnd_1858796 954455786654814685801559 := by
  unfold tailWord_1858796
  simp only [CollatzResearch.WordTrace]
  refine ⟨33897929886953511963930121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45197239849271349285240161 33897929886953511963930121)
  ·
    refine ⟨25423447415215133972947591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33897929886953511963930121 25423447415215133972947591)
    ·
      refine ⟨38135171122822700959421387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25423447415215133972947591 38135171122822700959421387)
      ·
        refine ⟨57202756684234051439132081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38135171122822700959421387 57202756684234051439132081)
        ·
          refine ⟨42902067513175538579349061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57202756684234051439132081 42902067513175538579349061)
          ·
            refine ⟨8044137658720413483627949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42902067513175538579349061 8044137658720413483627949)
            ·
              refine ⟨3016551622020155056360481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8044137658720413483627949 3016551622020155056360481)
              ·
                refine ⟨2262413716515116292270361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016551622020155056360481 2262413716515116292270361)
                ·
                  refine ⟨1696810287386337219202771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262413716515116292270361 1696810287386337219202771)
                  ·
                    refine ⟨2545215431079505828804157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1696810287386337219202771 2545215431079505828804157)
                    ·
                      refine ⟨954455786654814685801559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2545215431079505828804157 954455786654814685801559)
                      ·
                        rfl

theorem cell23_1858796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_1858796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858796 prefixEnd_1858796 := by exact prefixLift 1858796
  have htrace : WordTrace (prefixWord ++ tailWord_1858796) baseStart_1858796 baseEnd_1858796 := by
    simpa [prefixWord, tailWord_1858796, baseEnd_1858796] using wordTrace_append hprefix tailTrace_1858796
  have hstable : (prefixWord ++ tailWord_1858796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858796).length < 2 ^ (prefixWord ++ tailWord_1858796).sum := by decide
  have hdescent : baseEnd_1858796 < baseStart_1858796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858852 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1858852 : Nat := 118140960795 + 1858852 * 2 ^ 59
def prefixEnd_1858852 : Nat := 4983230072969 + 3 ^ 40 * 1858852 * 2
def baseEnd_1858852 : Nat := 954484541571466466701301

theorem tailTrace_1858852 : CollatzResearch.WordTrace tailWord_1858852 prefixEnd_1858852 954484541571466466701301 := by
  unfold tailWord_1858852
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898951130852072745949405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45198601507802763661265873 33898951130852072745949405)
  ·
    refine ⟨12712106674069527279731027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33898951130852072745949405 12712106674069527279731027)
    ·
      refine ⟨19068160011104290919596541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12712106674069527279731027 19068160011104290919596541)
      ·
        refine ⟨7150560004164109094848703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19068160011104290919596541 7150560004164109094848703)
        ·
          refine ⟨10725840006246163642273055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7150560004164109094848703 10725840006246163642273055)
          ·
            refine ⟨16088760009369245463409583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10725840006246163642273055 16088760009369245463409583)
            ·
              refine ⟨24133140014053868195114375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16088760009369245463409583 24133140014053868195114375)
              ·
                refine ⟨36199710021080802292671563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24133140014053868195114375 36199710021080802292671563)
                ·
                  refine ⟨54299565031621203439007345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36199710021080802292671563 54299565031621203439007345)
                  ·
                    refine ⟨40724673773715902579255509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54299565031621203439007345 40724673773715902579255509)
                    ·
                      refine ⟨954484541571466466701301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40724673773715902579255509 954484541571466466701301)
                      ·
                        rfl

theorem cell23_1858852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1858852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858852 prefixEnd_1858852 := by exact prefixLift 1858852
  have htrace : WordTrace (prefixWord ++ tailWord_1858852) baseStart_1858852 baseEnd_1858852 := by
    simpa [prefixWord, tailWord_1858852, baseEnd_1858852] using wordTrace_append hprefix tailTrace_1858852
  have hstable : (prefixWord ++ tailWord_1858852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858852).length < 2 ^ (prefixWord ++ tailWord_1858852).sum := by decide
  have hdescent : baseEnd_1858852 < baseStart_1858852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858872 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 6, 5]
def baseStart_1858872 : Nat := 118140960795 + 1858872 * 2 ^ 59
def prefixEnd_1858872 : Nat := 4983230072969 + 3 ^ 40 * 1858872 * 2
def baseEnd_1858872 : Nat := 318164937061518796150403

theorem tailTrace_1858872 : CollatzResearch.WordTrace tailWord_1858872 prefixEnd_1858872 318164937061518796150403 := by
  unfold tailWord_1858872
  simp only [CollatzResearch.WordTrace]
  refine ⟨33899315860815844453813435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45199087814421125938417913 33899315860815844453813435)
  ·
    refine ⟨50848973791223766680720153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33899315860815844453813435 50848973791223766680720153)
    ·
      refine ⟨38136730343417825010540115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50848973791223766680720153 38136730343417825010540115)
      ·
        refine ⟨57205095515126737515810173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38136730343417825010540115 57205095515126737515810173)
        ·
          refine ⟨21451910818172526568428815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57205095515126737515810173 21451910818172526568428815)
          ·
            refine ⟨32177866227258789852643223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21451910818172526568428815 32177866227258789852643223)
            ·
              refine ⟨48266799340888184778964835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32177866227258789852643223 48266799340888184778964835)
              ·
                refine ⟨72400199011332277168447253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48266799340888184778964835 72400199011332277168447253)
                ·
                  refine ⟨3393759328656200492270965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72400199011332277168447253 3393759328656200492270965)
                  ·
                    refine ⟨318164937061518796150403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3393759328656200492270965 318164937061518796150403)
                    ·
                      rfl

theorem cell23_1858872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_1858872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858872 prefixEnd_1858872 := by exact prefixLift 1858872
  have htrace : WordTrace (prefixWord ++ tailWord_1858872) baseStart_1858872 baseEnd_1858872 := by
    simpa [prefixWord, tailWord_1858872, baseEnd_1858872] using wordTrace_append hprefix tailTrace_1858872
  have hstable : (prefixWord ++ tailWord_1858872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858872).length < 2 ^ (prefixWord ++ tailWord_1858872).sum := by decide
  have hdescent : baseEnd_1858872 < baseStart_1858872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858929 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_1858929 : Nat := 118140960795 + 1858929 * 2 ^ 59
def prefixEnd_1858929 : Nat := 4983230072969 + 3 ^ 40 * 1858929 * 2
def baseEnd_1858929 : Nat := 954524079581862665438447

theorem tailTrace_1858929 : CollatzResearch.WordTrace tailWord_1858929 prefixEnd_1858929 954524079581862665438447 := by
  unfold tailWord_1858929
  simp only [CollatzResearch.WordTrace]
  refine ⟨67800710682425187642451841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45200473788283458428301227 67800710682425187642451841)
  ·
    refine ⟨50850533011818890731838881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67800710682425187642451841 50850533011818890731838881)
    ·
      refine ⟨38137899758864168048879161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50850533011818890731838881 38137899758864168048879161)
      ·
        refine ⟨28603424819148126036659371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38137899758864168048879161 28603424819148126036659371)
        ·
          refine ⟨42905137228722189054989057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28603424819148126036659371 42905137228722189054989057)
          ·
            refine ⟨32178852921541641791241793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42905137228722189054989057 32178852921541641791241793)
            ·
              refine ⟨24134139691156231343431345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32178852921541641791241793 24134139691156231343431345)
              ·
                refine ⟨18100604768367173507573509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24134139691156231343431345 18100604768367173507573509)
                ·
                  refine ⟨3393863394068845032670033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18100604768367173507573509 3393863394068845032670033)
                  ·
                    refine ⟨2545397545551633774502525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3393863394068845032670033 2545397545551633774502525)
                    ·
                      refine ⟨954524079581862665438447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2545397545551633774502525 954524079581862665438447)
                      ·
                        rfl

theorem cell23_1858929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_1858929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1858929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1858929 prefixEnd_1858929 := by exact prefixLift 1858929
  have htrace : WordTrace (prefixWord ++ tailWord_1858929) baseStart_1858929 baseEnd_1858929 := by
    simpa [prefixWord, tailWord_1858929, baseEnd_1858929] using wordTrace_append hprefix tailTrace_1858929
  have hstable : (prefixWord ++ tailWord_1858929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858929).length < 2 ^ (prefixWord ++ tailWord_1858929).sum := by decide
  have hdescent : baseEnd_1858929 < baseStart_1858929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859016 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_1859016 : Nat := 118140960795 + 1859016 * 2 ^ 59
def prefixEnd_1859016 : Nat := 4983230072969 + 3 ^ 40 * 1859016 * 2
def baseEnd_1859016 : Nat := 954568752398803825050547

theorem tailTrace_1859016 : CollatzResearch.WordTrace tailWord_1859016 prefixEnd_1859016 954568752398803825050547 := by
  unfold tailWord_1859016
  simp only [CollatzResearch.WordTrace]
  refine ⟨33901941916555000750434451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45202589222073334333912601 33901941916555000750434451)
  ·
    refine ⟨50852912874832501125651677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33901941916555000750434451 50852912874832501125651677)
    ·
      refine ⟨19069842328062187922119379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50852912874832501125651677 19069842328062187922119379)
      ·
        refine ⟨28604763492093281883179069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19069842328062187922119379 28604763492093281883179069)
        ·
          refine ⟨10726786309534980706192151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28604763492093281883179069 10726786309534980706192151)
          ·
            refine ⟨16090179464302471059288227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10726786309534980706192151 16090179464302471059288227)
            ·
              refine ⟨24135269196453706588932341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16090179464302471059288227 24135269196453706588932341)
              ·
                refine ⟨2262681487167534992712407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24135269196453706588932341 2262681487167534992712407)
                ·
                  refine ⟨3394022230751302489068611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262681487167534992712407 3394022230751302489068611)
                  ·
                    refine ⟨5091033346126953733602917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3394022230751302489068611 5091033346126953733602917)
                    ·
                      refine ⟨954568752398803825050547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5091033346126953733602917 954568752398803825050547)
                      ·
                        rfl

theorem cell23_1859016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_1859016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859016 prefixEnd_1859016 := by exact prefixLift 1859016
  have htrace : WordTrace (prefixWord ++ tailWord_1859016) baseStart_1859016 baseEnd_1859016 := by
    simpa [prefixWord, tailWord_1859016, baseEnd_1859016] using wordTrace_append hprefix tailTrace_1859016
  have hstable : (prefixWord ++ tailWord_1859016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859016).length < 2 ^ (prefixWord ++ tailWord_1859016).sum := by decide
  have hdescent : baseEnd_1859016 < baseStart_1859016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859019 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 5]
def baseStart_1859019 : Nat := 118140960795 + 1859019 * 2 ^ 59
def prefixEnd_1859019 : Nat := 4983230072969 + 3 ^ 40 * 1859019 * 2
def baseEnd_1859019 : Nat := 954570292840767313313033

theorem tailTrace_1859019 : CollatzResearch.WordTrace tailWord_1859019 prefixEnd_1859019 954570292840767313313033 := by
  unfold tailWord_1859019
  simp only [CollatzResearch.WordTrace]
  refine ⟨67803993252099133013228111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45202662168066088675485407 67803993252099133013228111)
  ·
    refine ⟨101705989878148699519842167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67803993252099133013228111 101705989878148699519842167)
    ·
      refine ⟨152558984817223049279763251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101705989878148699519842167 152558984817223049279763251)
      ·
        refine ⟨228838477225834573919644877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152558984817223049279763251 228838477225834573919644877)
        ·
          refine ⟨85814428959687965219866829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228838477225834573919644877 85814428959687965219866829)
          ·
            refine ⟨32180410859882986957450061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85814428959687965219866829 32180410859882986957450061)
            ·
              refine ⟨12067654072456120109043773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32180410859882986957450061 12067654072456120109043773)
              ·
                refine ⟨4525370277171045040891415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12067654072456120109043773 4525370277171045040891415)
                ·
                  refine ⟨6788055415756567561337123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525370277171045040891415 6788055415756567561337123)
                  ·
                    refine ⟨10182083123634851342005685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6788055415756567561337123 10182083123634851342005685)
                    ·
                      refine ⟨954570292840767313313033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10182083123634851342005685 954570292840767313313033)
                      ·
                        rfl

theorem cell23_1859019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 5].length) (baseStart_1859019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859019 prefixEnd_1859019 := by exact prefixLift 1859019
  have htrace : WordTrace (prefixWord ++ tailWord_1859019) baseStart_1859019 baseEnd_1859019 := by
    simpa [prefixWord, tailWord_1859019, baseEnd_1859019] using wordTrace_append hprefix tailTrace_1859019
  have hstable : (prefixWord ++ tailWord_1859019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859019).length < 2 ^ (prefixWord ++ tailWord_1859019).sum := by decide
  have hdescent : baseEnd_1859019 < baseStart_1859019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859029 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1859029 : Nat := 118140960795 + 1859029 * 2 ^ 59
def prefixEnd_1859029 : Nat := 4983230072969 + 3 ^ 40 * 1859029 * 2
def baseEnd_1859029 : Nat := 954575427647312274187987

theorem tailTrace_1859029 : CollatzResearch.WordTrace tailWord_1859029 prefixEnd_1859029 954575427647312274187987 := by
  unfold tailWord_1859029
  simp only [CollatzResearch.WordTrace]
  refine ⟨67804357982062904721092141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45202905321375269814061427 67804357982062904721092141)
  ·
    refine ⟨25426634243273589270409553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67804357982062904721092141 25426634243273589270409553)
    ·
      refine ⟨19069975682455191952807165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25426634243273589270409553 19069975682455191952807165)
      ·
        refine ⟨7151240880920696982302687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19069975682455191952807165 7151240880920696982302687)
        ·
          refine ⟨10726861321381045473454031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7151240880920696982302687 10726861321381045473454031)
          ·
            refine ⟨16090291982071568210181047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10726861321381045473454031 16090291982071568210181047)
            ·
              refine ⟨24135437973107352315271571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16090291982071568210181047 24135437973107352315271571)
              ·
                refine ⟨36203156959661028472907357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24135437973107352315271571 36203156959661028472907357)
                ·
                  refine ⟨13576183859872885677340259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36203156959661028472907357 13576183859872885677340259)
                  ·
                    refine ⟨20364275789809328516010389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13576183859872885677340259 20364275789809328516010389)
                    ·
                      refine ⟨954575427647312274187987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20364275789809328516010389 954575427647312274187987)
                      ·
                        rfl

theorem cell23_1859029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1859029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859029 prefixEnd_1859029 := by exact prefixLift 1859029
  have htrace : WordTrace (prefixWord ++ tailWord_1859029) baseStart_1859029 baseEnd_1859029 := by
    simpa [prefixWord, tailWord_1859029, baseEnd_1859029] using wordTrace_append hprefix tailTrace_1859029
  have hstable : (prefixWord ++ tailWord_1859029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859029).length < 2 ^ (prefixWord ++ tailWord_1859029).sum := by decide
  have hdescent : baseEnd_1859029 < baseStart_1859029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859039 : List Nat := [1, 1, 2, 3, 3, 1, 4, 8]
def baseStart_1859039 : Nat := 118140960795 + 1859039 * 2 ^ 59
def prefixEnd_1859039 : Nat := 4983230072969 + 3 ^ 40 * 1859039 * 2
def baseEnd_1859039 : Nat := 35354835646439156854183

theorem tailTrace_1859039 : CollatzResearch.WordTrace tailWord_1859039 prefixEnd_1859039 35354835646439156854183 := by
  unfold tailWord_1859039
  simp only [CollatzResearch.WordTrace]
  refine ⟨67804722712026676428956171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45203148474684450952637447 67804722712026676428956171)
  ·
    refine ⟨101707084068040014643434257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67804722712026676428956171 101707084068040014643434257)
    ·
      refine ⟨76280313051030010982575693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101707084068040014643434257 76280313051030010982575693)
      ·
        refine ⟨28605117394136254118465885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76280313051030010982575693 28605117394136254118465885)
        ·
          refine ⟨10726919022801095294424707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28605117394136254118465885 10726919022801095294424707)
          ·
            refine ⟨16090378534201642941637061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10726919022801095294424707 16090378534201642941637061)
            ·
              refine ⟨3016945975162808051556949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16090378534201642941637061 3016945975162808051556949)
              ·
                refine ⟨35354835646439156854183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3016945975162808051556949 35354835646439156854183)
                ·
                  rfl

theorem cell23_1859039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 8].length) (baseStart_1859039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859039 prefixEnd_1859039 := by exact prefixLift 1859039
  have htrace : WordTrace (prefixWord ++ tailWord_1859039) baseStart_1859039 baseEnd_1859039 := by
    simpa [prefixWord, tailWord_1859039, baseEnd_1859039] using wordTrace_append hprefix tailTrace_1859039
  have hstable : (prefixWord ++ tailWord_1859039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859039).length < 2 ^ (prefixWord ++ tailWord_1859039).sum := by decide
  have hdescent : baseEnd_1859039 < baseStart_1859039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859043 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 2, 4]
def baseStart_1859043 : Nat := 118140960795 + 1859043 * 2 ^ 59
def prefixEnd_1859043 : Nat := 4983230072969 + 3 ^ 40 * 1859043 * 2
def baseEnd_1859043 : Nat := 318194205458825073137641

theorem tailTrace_1859043 : CollatzResearch.WordTrace tailWord_1859043 prefixEnd_1859043 318194205458825073137641 := by
  unfold tailWord_1859043
  simp only [CollatzResearch.WordTrace]
  refine ⟨67804868604012185112101783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45203245736008123408067855 67804868604012185112101783)
  ·
    refine ⟨101707302906018277668152675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67804868604012185112101783 101707302906018277668152675)
    ·
      refine ⟨152560954359027416502229013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101707302906018277668152675 152560954359027416502229013)
      ·
        refine ⟨7151294735579410148541985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152560954359027416502229013 7151294735579410148541985)
        ·
          refine ⟨5363471051684557611406489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7151294735579410148541985 5363471051684557611406489)
          ·
            refine ⟨4022603288763418208554867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5363471051684557611406489 4022603288763418208554867)
            ·
              refine ⟨6033904933145127312832301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022603288763418208554867 6033904933145127312832301)
              ·
                refine ⟨2262714349929422742312113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6033904933145127312832301 2262714349929422742312113)
                ·
                  refine ⟨1697035762447067056734085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262714349929422742312113 1697035762447067056734085)
                  ·
                    refine ⟨318194205458825073137641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1697035762447067056734085 318194205458825073137641)
                    ·
                      rfl

theorem cell23_1859043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 4].length) (baseStart_1859043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859043 prefixEnd_1859043 := by exact prefixLift 1859043
  have htrace : WordTrace (prefixWord ++ tailWord_1859043) baseStart_1859043 baseEnd_1859043 := by
    simpa [prefixWord, tailWord_1859043, baseEnd_1859043] using wordTrace_append hprefix tailTrace_1859043
  have hstable : (prefixWord ++ tailWord_1859043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859043).length < 2 ^ (prefixWord ++ tailWord_1859043).sum := by decide
  have hdescent : baseEnd_1859043 < baseStart_1859043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859050 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_1859050 : Nat := 118140960795 + 1859050 * 2 ^ 59
def prefixEnd_1859050 : Nat := 4983230072969 + 3 ^ 40 * 1859050 * 2
def baseEnd_1859050 : Nat := 954586210741056692025391

theorem tailTrace_1859050 : CollatzResearch.WordTrace tailWord_1859050 prefixEnd_1859050 954586210741056692025391 := by
  unfold tailWord_1859050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16951280978746706326901651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45203415943324550205071069 16951280978746706326901651)
  ·
    refine ⟨25426921468120059490352477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16951280978746706326901651 25426921468120059490352477)
    ·
      refine ⟨9535095550545022308882179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25426921468120059490352477 9535095550545022308882179)
      ·
        refine ⟨14302643325817533463323269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535095550545022308882179 14302643325817533463323269)
        ·
          refine ⟨2681745623590787524373113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14302643325817533463323269 2681745623590787524373113)
          ·
            refine ⟨2011309217693090643279835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2681745623590787524373113 2011309217693090643279835)
            ·
              refine ⟨3016963826539635964919753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011309217693090643279835 3016963826539635964919753)
              ·
                refine ⟨2262722869904726973689815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016963826539635964919753 2262722869904726973689815)
                ·
                  refine ⟨3394084304857090460534723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262722869904726973689815 3394084304857090460534723)
                  ·
                    refine ⟨5091126457285635690802085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3394084304857090460534723 5091126457285635690802085)
                    ·
                      refine ⟨954586210741056692025391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5091126457285635690802085 954586210741056692025391)
                      ·
                        rfl

theorem cell23_1859050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_1859050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859050 prefixEnd_1859050 := by exact prefixLift 1859050
  have htrace : WordTrace (prefixWord ++ tailWord_1859050) baseStart_1859050 baseEnd_1859050 := by
    simpa [prefixWord, tailWord_1859050, baseEnd_1859050] using wordTrace_append hprefix tailTrace_1859050
  have hstable : (prefixWord ++ tailWord_1859050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859050).length < 2 ^ (prefixWord ++ tailWord_1859050).sum := by decide
  have hdescent : baseEnd_1859050 < baseStart_1859050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859066 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_1859066 : Nat := 118140960795 + 1859066 * 2 ^ 59
def prefixEnd_1859066 : Nat := 4983230072969 + 3 ^ 40 * 1859066 * 2
def baseEnd_1859066 : Nat := 954594426431528629425317

theorem tailTrace_1859066 : CollatzResearch.WordTrace tailWord_1859066 prefixEnd_1859066 954594426431528629425317 := by
  unfold tailWord_1859066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16951426870732215010047263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45203804988619240026792701 16951426870732215010047263)
  ·
    refine ⟨25427140306098322515070895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16951426870732215010047263 25427140306098322515070895)
    ·
      refine ⟨38140710459147483772606343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25427140306098322515070895 38140710459147483772606343)
      ·
        refine ⟨57211065688721225658909515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38140710459147483772606343 57211065688721225658909515)
        ·
          refine ⟨85816598533081838488364273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57211065688721225658909515 85816598533081838488364273)
          ·
            refine ⟨64362448899811378866273205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85816598533081838488364273 64362448899811378866273205)
            ·
              refine ⟨6033979584357316768713113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64362448899811378866273205 6033979584357316768713113)
              ·
                refine ⟨4525484688267987576534835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6033979584357316768713113 4525484688267987576534835)
                ·
                  refine ⟨6788227032401981364802253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525484688267987576534835 6788227032401981364802253)
                  ·
                    refine ⟨2545585137150743011800845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6788227032401981364802253 2545585137150743011800845)
                    ·
                      refine ⟨954594426431528629425317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2545585137150743011800845 954594426431528629425317)
                      ·
                        rfl

theorem cell23_1859066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_1859066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859066 prefixEnd_1859066 := by exact prefixLift 1859066
  have htrace : WordTrace (prefixWord ++ tailWord_1859066) baseStart_1859066 baseEnd_1859066 := by
    simpa [prefixWord, tailWord_1859066, baseEnd_1859066] using wordTrace_append hprefix tailTrace_1859066
  have hstable : (prefixWord ++ tailWord_1859066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859066).length < 2 ^ (prefixWord ++ tailWord_1859066).sum := by decide
  have hdescent : baseEnd_1859066 < baseStart_1859066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859089 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_1859089 : Nat := 118140960795 + 1859089 * 2 ^ 59
def prefixEnd_1859089 : Nat := 4983230072969 + 3 ^ 40 * 1859089 * 2
def baseEnd_1859089 : Nat := 954606236486582039437711

theorem tailTrace_1859089 : CollatzResearch.WordTrace tailWord_1859089 prefixEnd_1859089 954606236486582039437711 := by
  unfold tailWord_1859089
  simp only [CollatzResearch.WordTrace]
  refine ⟨67806546361845534968276321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45204364241230356645517547 67806546361845534968276321)
  ·
    refine ⟨50854909771384151226207241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67806546361845534968276321 50854909771384151226207241)
    ·
      refine ⟨38141182328538113419655431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50854909771384151226207241 38141182328538113419655431)
      ·
        refine ⟨57211773492807170129483147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38141182328538113419655431 57211773492807170129483147)
        ·
          refine ⟨85817660239210755194224721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57211773492807170129483147 85817660239210755194224721)
          ·
            refine ⟨64363245179408066395668541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85817660239210755194224721 64363245179408066395668541)
            ·
              refine ⟨24136216942278024898375703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64363245179408066395668541 24136216942278024898375703)
              ·
                refine ⟨36204325413417037347563555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24136216942278024898375703 36204325413417037347563555)
                ·
                  refine ⟨54306488120125556021345333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36204325413417037347563555 54306488120125556021345333)
                  ·
                    refine ⟨5091233261261770877001125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54306488120125556021345333 5091233261261770877001125)
                    ·
                      refine ⟨954606236486582039437711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5091233261261770877001125 954606236486582039437711)
                      ·
                        rfl

theorem cell23_1859089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_1859089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859089 prefixEnd_1859089 := by exact prefixLift 1859089
  have htrace : WordTrace (prefixWord ++ tailWord_1859089) baseStart_1859089 baseEnd_1859089 := by
    simpa [prefixWord, tailWord_1859089, baseEnd_1859089] using wordTrace_append hprefix tailTrace_1859089
  have hstable : (prefixWord ++ tailWord_1859089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859089).length < 2 ^ (prefixWord ++ tailWord_1859089).sum := by decide
  have hdescent : baseEnd_1859089 < baseStart_1859089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859093 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_1859093 : Nat := 118140960795 + 1859093 * 2 ^ 59
def prefixEnd_1859093 : Nat := 4983230072969 + 3 ^ 40 * 1859093 * 2
def baseEnd_1859093 : Nat := 954608290409200023787693

theorem tailTrace_1859093 : CollatzResearch.WordTrace tailWord_1859093 prefixEnd_1859093 954608290409200023787693 := by
  unfold tailWord_1859093
  simp only [CollatzResearch.WordTrace]
  refine ⟨67806692253831043651421933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45204461502554029100947955 67806692253831043651421933)
  ·
    refine ⟨25427509595186641369283225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67806692253831043651421933 25427509595186641369283225)
    ·
      refine ⟨19070632196389981026962419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25427509595186641369283225 19070632196389981026962419)
      ·
        refine ⟨28605948294584971540443629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19070632196389981026962419 28605948294584971540443629)
        ·
          refine ⟨10727230610469364327666361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28605948294584971540443629 10727230610469364327666361)
          ·
            refine ⟨8045422957852023245749771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10727230610469364327666361 8045422957852023245749771)
            ·
              refine ⟨12068134436778034868624657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045422957852023245749771 12068134436778034868624657)
              ·
                refine ⟨9051100827583526151468493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12068134436778034868624657 9051100827583526151468493)
                ·
                  refine ⟨3394162810343822306800685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9051100827583526151468493 3394162810343822306800685)
                  ·
                    refine ⟨1272811053878933365050257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394162810343822306800685 1272811053878933365050257)
                    ·
                      refine ⟨954608290409200023787693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272811053878933365050257 954608290409200023787693)
                      ·
                        rfl

theorem cell23_1859093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_1859093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859093 prefixEnd_1859093 := by exact prefixLift 1859093
  have htrace : WordTrace (prefixWord ++ tailWord_1859093) baseStart_1859093 baseEnd_1859093 := by
    simpa [prefixWord, tailWord_1859093, baseEnd_1859093] using wordTrace_append hprefix tailTrace_1859093
  have hstable : (prefixWord ++ tailWord_1859093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859093).length < 2 ^ (prefixWord ++ tailWord_1859093).sum := by decide
  have hdescent : baseEnd_1859093 < baseStart_1859093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859123 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 1, 4, 2]
def baseStart_1859123 : Nat := 118140960795 + 1859123 * 2 ^ 59
def prefixEnd_1859123 : Nat := 4983230072969 + 3 ^ 40 * 1859123 * 2
def baseEnd_1859123 : Nat := 954623694828834906412555

theorem tailTrace_1859123 : CollatzResearch.WordTrace tailWord_1859123 prefixEnd_1859123 954623694828834906412555 := by
  unfold tailWord_1859123
  simp only [CollatzResearch.WordTrace]
  refine ⟨67807786443722358775014023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45205190962481572516676015 67807786443722358775014023)
  ·
    refine ⟨101711679665583538162521035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67807786443722358775014023 101711679665583538162521035)
    ·
      refine ⟨152567519498375307243781553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101711679665583538162521035 152567519498375307243781553)
      ·
        refine ⟨114425639623781480432836165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152567519498375307243781553 114425639623781480432836165)
        ·
          refine ⟨21454807429459027581156781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114425639623781480432836165 21454807429459027581156781)
          ·
            refine ⟨8045552786047135342933793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21454807429459027581156781 8045552786047135342933793)
            ·
              refine ⟨6034164589535351507200345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8045552786047135342933793 6034164589535351507200345)
              ·
                refine ⟨4525623442151513630400259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6034164589535351507200345 4525623442151513630400259)
                ·
                  refine ⟨6788435163227270445600389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525623442151513630400259 6788435163227270445600389)
                  ·
                    refine ⟨1272831593105113208550073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788435163227270445600389 1272831593105113208550073)
                    ·
                      refine ⟨954623694828834906412555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272831593105113208550073 954623694828834906412555)
                      ·
                        rfl

theorem cell23_1859123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 4, 2].length) (baseStart_1859123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859123 prefixEnd_1859123 := by exact prefixLift 1859123
  have htrace : WordTrace (prefixWord ++ tailWord_1859123) baseStart_1859123 baseEnd_1859123 := by
    simpa [prefixWord, tailWord_1859123, baseEnd_1859123] using wordTrace_append hprefix tailTrace_1859123
  have hstable : (prefixWord ++ tailWord_1859123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859123).length < 2 ^ (prefixWord ++ tailWord_1859123).sum := by decide
  have hdescent : baseEnd_1859123 < baseStart_1859123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859127 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 1, 3, 2]
def baseStart_1859127 : Nat := 118140960795 + 1859127 * 2 ^ 59
def prefixEnd_1859127 : Nat := 4983230072969 + 3 ^ 40 * 1859127 * 2
def baseEnd_1859127 : Nat := 954625748751452890762537

theorem tailTrace_1859127 : CollatzResearch.WordTrace tailWord_1859127 prefixEnd_1859127 954625748751452890762537 := by
  unfold tailWord_1859127
  simp only [CollatzResearch.WordTrace]
  refine ⟨67807932335707867458159635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45205288223805244972106423 67807932335707867458159635)
  ·
    refine ⟨101711898503561801187239453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67807932335707867458159635 101711898503561801187239453)
    ·
      refine ⟨38141961938835675445214795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101711898503561801187239453 38141961938835675445214795)
      ·
        refine ⟨57212942908253513167822193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38141961938835675445214795 57212942908253513167822193)
        ·
          refine ⟨42909707181190134875866645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57212942908253513167822193 42909707181190134875866645)
          ·
            refine ⟨2011392524118287572306249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42909707181190134875866645 2011392524118287572306249)
            ·
              refine ⟨1508544393088715679229687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011392524118287572306249 1508544393088715679229687)
              ·
                refine ⟨2262816589633073518844531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508544393088715679229687 2262816589633073518844531)
                ·
                  refine ⟨3394224884449610278266797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262816589633073518844531 3394224884449610278266797)
                  ·
                    refine ⟨1272834331668603854350049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394224884449610278266797 1272834331668603854350049)
                    ·
                      refine ⟨954625748751452890762537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272834331668603854350049 954625748751452890762537)
                      ·
                        rfl

theorem cell23_1859127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_1859127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859127 prefixEnd_1859127 := by exact prefixLift 1859127
  have htrace : WordTrace (prefixWord ++ tailWord_1859127) baseStart_1859127 baseEnd_1859127 := by
    simpa [prefixWord, tailWord_1859127, baseEnd_1859127] using wordTrace_append hprefix tailTrace_1859127
  have hstable : (prefixWord ++ tailWord_1859127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859127).length < 2 ^ (prefixWord ++ tailWord_1859127).sum := by decide
  have hdescent : baseEnd_1859127 < baseStart_1859127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859146 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 7]
def baseStart_1859146 : Nat := 118140960795 + 1859146 * 2 ^ 59
def prefixEnd_1859146 : Nat := 4983230072969 + 3 ^ 40 * 1859146 * 2
def baseEnd_1859146 : Nat := 106070611653765368491661

theorem tailTrace_1859146 : CollatzResearch.WordTrace tailWord_1859146 prefixEnd_1859146 106070611653765368491661 := by
  unfold tailWord_1859146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16952156330659758425775323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45205750215092689135400861 16952156330659758425775323)
  ·
    refine ⟨25428234495989637638662985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16952156330659758425775323 25428234495989637638662985)
    ·
      refine ⟨19071175871992228228997239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25428234495989637638662985 19071175871992228228997239)
      ·
        refine ⟨28606763807988342343495859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19071175871992228228997239 28606763807988342343495859)
        ·
          refine ⟨42910145711982513515243789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28606763807988342343495859 42910145711982513515243789)
          ·
            refine ⟨16091304641993442568216421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42910145711982513515243789 16091304641993442568216421)
            ·
              refine ⟨3017119620373770481540579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16091304641993442568216421 3017119620373770481540579)
              ·
                refine ⟨4525679430560655722310869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3017119620373770481540579 4525679430560655722310869)
                ·
                  refine ⟨106070611653765368491661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4525679430560655722310869 106070611653765368491661)
                  ·
                    rfl

theorem cell23_1859146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_1859146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859146 prefixEnd_1859146 := by exact prefixLift 1859146
  have htrace : WordTrace (prefixWord ++ tailWord_1859146) baseStart_1859146 baseEnd_1859146 := by
    simpa [prefixWord, tailWord_1859146, baseEnd_1859146] using wordTrace_append hprefix tailTrace_1859146
  have hstable : (prefixWord ++ tailWord_1859146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859146).length < 2 ^ (prefixWord ++ tailWord_1859146).sum := by decide
  have hdescent : baseEnd_1859146 < baseStart_1859146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859179 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 8]
def baseStart_1859179 : Nat := 118140960795 + 1859179 * 2 ^ 59
def prefixEnd_1859179 : Nat := 4983230072969 + 3 ^ 40 * 1859179 * 2
def baseEnd_1859179 : Nat := 954652449745486687312297

theorem tailTrace_1859179 : CollatzResearch.WordTrace tailWord_1859179 prefixEnd_1859179 954652449745486687312297 := by
  unfold tailWord_1859179
  simp only [CollatzResearch.WordTrace]
  refine ⟨67809828931519480339052591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45206552621012986892701727 67809828931519480339052591)
  ·
    refine ⟨101714743397279220508578887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67809828931519480339052591 101714743397279220508578887)
    ·
      refine ⟨152572115095918830762868331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101714743397279220508578887 152572115095918830762868331)
      ·
        refine ⟨228858172643878246144302497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152572115095918830762868331 228858172643878246144302497)
        ·
          refine ⟨171643629482908684608226873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228858172643878246144302497 171643629482908684608226873)
          ·
            refine ⟨128732722112181513456170155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171643629482908684608226873 128732722112181513456170155)
            ·
              refine ⟨193099083168272270184255233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128732722112181513456170155 193099083168272270184255233)
              ·
                refine ⟨144824312376204202638191425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193099083168272270184255233 144824312376204202638191425)
                ·
                  refine ⟨108618234282153151978643569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144824312376204202638191425 108618234282153151978643569)
                  ·
                    refine ⟨81463675711614863983982677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108618234282153151978643569 81463675711614863983982677)
                    ·
                      refine ⟨954652449745486687312297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 81463675711614863983982677 954652449745486687312297)
                      ·
                        rfl

theorem cell23_1859179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_1859179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859179 prefixEnd_1859179 := by exact prefixLift 1859179
  have htrace : WordTrace (prefixWord ++ tailWord_1859179) baseStart_1859179 baseEnd_1859179 := by
    simpa [prefixWord, tailWord_1859179, baseEnd_1859179] using wordTrace_append hprefix tailTrace_1859179
  have hstable : (prefixWord ++ tailWord_1859179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859179).length < 2 ^ (prefixWord ++ tailWord_1859179).sum := by decide
  have hdescent : baseEnd_1859179 < baseStart_1859179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859208 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1859208 : Nat := 118140960795 + 1859208 * 2 ^ 59
def prefixEnd_1859208 : Nat := 4983230072969 + 3 ^ 40 * 1859208 * 2
def baseEnd_1859208 : Nat := 954667340684467073849665

theorem tailTrace_1859208 : CollatzResearch.WordTrace tailWord_1859208 prefixEnd_1859208 954667340684467073849665 := by
  unfold tailWord_1859208
  simp only [CollatzResearch.WordTrace]
  refine ⟨33905443324207209145929139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45207257765609612194572185 33905443324207209145929139)
  ·
    refine ⟨50858164986310813718893709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33905443324207209145929139 50858164986310813718893709)
    ·
      refine ⟨19071811869866555144585141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50858164986310813718893709 19071811869866555144585141)
      ·
        refine ⟨1787982362799989544804857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19071811869866555144585141 1787982362799989544804857)
        ·
          refine ⟨1340986772099992158603643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1787982362799989544804857 1340986772099992158603643)
          ·
            refine ⟨2011480158149988237905465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340986772099992158603643 2011480158149988237905465)
            ·
              refine ⟨1508610118612491178429099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011480158149988237905465 1508610118612491178429099)
              ·
                refine ⟨2262915177918736767643649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508610118612491178429099 2262915177918736767643649)
                ·
                  refine ⟨1697186383439052575732737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262915177918736767643649 1697186383439052575732737)
                  ·
                    refine ⟨1272889787579289431799553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1697186383439052575732737 1272889787579289431799553)
                    ·
                      refine ⟨954667340684467073849665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272889787579289431799553 954667340684467073849665)
                      ·
                        rfl

theorem cell23_1859208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1859208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859208 prefixEnd_1859208 := by exact prefixLift 1859208
  have htrace : WordTrace (prefixWord ++ tailWord_1859208) baseStart_1859208 baseEnd_1859208 := by
    simpa [prefixWord, tailWord_1859208, baseEnd_1859208] using wordTrace_append hprefix tailTrace_1859208
  have hstable : (prefixWord ++ tailWord_1859208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859208).length < 2 ^ (prefixWord ++ tailWord_1859208).sum := by decide
  have hdescent : baseEnd_1859208 < baseStart_1859208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859216 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 3]
def baseStart_1859216 : Nat := 118140960795 + 1859216 * 2 ^ 59
def prefixEnd_1859216 : Nat := 4983230072969 + 3 ^ 40 * 1859216 * 2
def baseEnd_1859216 : Nat := 954671448529703042549627

theorem tailTrace_1859216 : CollatzResearch.WordTrace tailWord_1859216 prefixEnd_1859216 954671448529703042549627 := by
  unfold tailWord_1859216
  simp only [CollatzResearch.WordTrace]
  refine ⟨33905589216192717829074751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45207452288256957105433001 33905589216192717829074751)
  ·
    refine ⟨50858383824289076743612127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33905589216192717829074751 50858383824289076743612127)
    ·
      refine ⟨76287575736433615115418191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50858383824289076743612127 76287575736433615115418191)
      ·
        refine ⟨114431363604650422673127287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76287575736433615115418191 114431363604650422673127287)
        ·
          refine ⟨171647045406975634009690931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114431363604650422673127287 171647045406975634009690931)
          ·
            refine ⟨257470568110463451014536397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171647045406975634009690931 257470568110463451014536397)
            ·
              refine ⟨96551463041423794130451149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257470568110463451014536397 96551463041423794130451149)
              ·
                refine ⟨36206798640533922798919181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96551463041423794130451149 36206798640533922798919181)
                ·
                  refine ⟨13577549490200221049594693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36206798640533922798919181 13577549490200221049594693)
                  ·
                    refine ⟨2545790529412541446799005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13577549490200221049594693 2545790529412541446799005)
                    ·
                      refine ⟨954671448529703042549627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2545790529412541446799005 954671448529703042549627)
                      ·
                        rfl

theorem cell23_1859216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_1859216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859216 prefixEnd_1859216 := by exact prefixLift 1859216
  have htrace : WordTrace (prefixWord ++ tailWord_1859216) baseStart_1859216 baseEnd_1859216 := by
    simpa [prefixWord, tailWord_1859216, baseEnd_1859216] using wordTrace_append hprefix tailTrace_1859216
  have hstable : (prefixWord ++ tailWord_1859216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859216).length < 2 ^ (prefixWord ++ tailWord_1859216).sum := by decide
  have hdescent : baseEnd_1859216 < baseStart_1859216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859230 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1859230 : Nat := 118140960795 + 1859230 * 2 ^ 59
def prefixEnd_1859230 : Nat := 4983230072969 + 3 ^ 40 * 1859230 * 2
def baseEnd_1859230 : Nat := 954678637258865987774563

theorem tailTrace_1859230 : CollatzResearch.WordTrace tailWord_1859230 prefixEnd_1859230 954678637258865987774563 := by
  unfold tailWord_1859230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8476461131791839506144893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45207792702889810699439429 8476461131791839506144893)
  ·
    refine ⟨3178672924421939814804335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8476461131791839506144893 3178672924421939814804335)
    ·
      refine ⟨4768009386632909722206503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3178672924421939814804335 4768009386632909722206503)
      ·
        refine ⟨7152014079949364583309755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4768009386632909722206503 7152014079949364583309755)
        ·
          refine ⟨10728021119924046874964633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7152014079949364583309755 10728021119924046874964633)
          ·
            refine ⟨8046015839943035156223475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10728021119924046874964633 8046015839943035156223475)
            ·
              refine ⟨12069023759914552734335213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8046015839943035156223475 12069023759914552734335213)
              ·
                refine ⟨4525883909967957275375705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12069023759914552734335213 4525883909967957275375705)
                ·
                  refine ⟨3394412932475967956531779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4525883909967957275375705 3394412932475967956531779)
                  ·
                    refine ⟨5091619398713951934797669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3394412932475967956531779 5091619398713951934797669)
                    ·
                      refine ⟨954678637258865987774563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5091619398713951934797669 954678637258865987774563)
                      ·
                        rfl

theorem cell23_1859230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1859230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859230 prefixEnd_1859230 := by exact prefixLift 1859230
  have htrace : WordTrace (prefixWord ++ tailWord_1859230) baseStart_1859230 baseEnd_1859230 := by
    simpa [prefixWord, tailWord_1859230, baseEnd_1859230] using wordTrace_append hprefix tailTrace_1859230
  have hstable : (prefixWord ++ tailWord_1859230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859230).length < 2 ^ (prefixWord ++ tailWord_1859230).sum := by decide
  have hdescent : baseEnd_1859230 < baseStart_1859230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859257 : List Nat := [1, 2, 1, 4, 1, 1, 6, 2, 1, 4]
def baseStart_1859257 : Nat := 118140960795 + 1859257 * 2 ^ 59
def prefixEnd_1859257 : Nat := 4983230072969 + 3 ^ 40 * 1859257 * 2
def baseEnd_1859257 : Nat := 318230833745512460712313

theorem tailTrace_1859257 : CollatzResearch.WordTrace tailWord_1859257 prefixEnd_1859257 318230833745512460712313 := by
  unfold tailWord_1859257
  simp only [CollatzResearch.WordTrace]
  refine ⟨67812673825236899660392025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45208449216824599773594683 67812673825236899660392025)
  ·
    refine ⟨50859505368927674745294019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67812673825236899660392025 50859505368927674745294019)
    ·
      refine ⟨76289258053391512117941029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50859505368927674745294019 76289258053391512117941029)
      ·
        refine ⟨14304235885010908522113943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76289258053391512117941029 14304235885010908522113943)
        ·
          refine ⟨21456353827516362783170915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14304235885010908522113943 21456353827516362783170915)
          ·
            refine ⟨32184530741274544174756373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21456353827516362783170915 32184530741274544174756373)
            ·
              refine ⟨1508649878497244258191705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32184530741274544174756373 1508649878497244258191705)
              ·
                refine ⟨1131487408872933193643779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1508649878497244258191705 1131487408872933193643779)
                ·
                  refine ⟨1697231113309399790465669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131487408872933193643779 1697231113309399790465669)
                  ·
                    refine ⟨318230833745512460712313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1697231113309399790465669 318230833745512460712313)
                    ·
                      rfl

theorem cell23_1859257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 4].length) (baseStart_1859257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859257 prefixEnd_1859257 := by exact prefixLift 1859257
  have htrace : WordTrace (prefixWord ++ tailWord_1859257) baseStart_1859257 baseEnd_1859257 := by
    simpa [prefixWord, tailWord_1859257, baseEnd_1859257] using wordTrace_append hprefix tailTrace_1859257
  have hstable : (prefixWord ++ tailWord_1859257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859257).length < 2 ^ (prefixWord ++ tailWord_1859257).sum := by decide
  have hdescent : baseEnd_1859257 < baseStart_1859257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859290 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2]
def baseStart_1859290 : Nat := 118140960795 + 1859290 * 2 ^ 59
def prefixEnd_1859290 : Nat := 4983230072969 + 3 ^ 40 * 1859290 * 2
def baseEnd_1859290 : Nat := 954709446098135753024287

theorem tailTrace_1859290 : CollatzResearch.WordTrace tailWord_1859290 prefixEnd_1859290 954709446098135753024287 := by
  unfold tailWord_1859290
  simp only [CollatzResearch.WordTrace]
  refine ⟨16953469358529336574085831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45209251622744897530895549 16953469358529336574085831)
  ·
    refine ⟨25430204037794004861128747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16953469358529336574085831 25430204037794004861128747)
    ·
      refine ⟨38145306056691007291693121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25430204037794004861128747 38145306056691007291693121)
      ·
        refine ⟨28608979542518255468769841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38145306056691007291693121 28608979542518255468769841)
        ·
          refine ⟨21456734656888691601577381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28608979542518255468769841 21456734656888691601577381)
          ·
            refine ⟨4023137748166629675295759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21456734656888691601577381 4023137748166629675295759)
            ·
              refine ⟨6034706622249944512943639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4023137748166629675295759 6034706622249944512943639)
              ·
                refine ⟨9052059933374916769415459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6034706622249944512943639 9052059933374916769415459)
                ·
                  refine ⟨13578089900062375154123189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9052059933374916769415459 13578089900062375154123189)
                  ·
                    refine ⟨1272945928130847670699049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13578089900062375154123189 1272945928130847670699049)
                    ·
                      refine ⟨954709446098135753024287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1272945928130847670699049 954709446098135753024287)
                      ·
                        rfl

theorem cell23_1859290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_1859290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859290 prefixEnd_1859290 := by exact prefixLift 1859290
  have htrace : WordTrace (prefixWord ++ tailWord_1859290) baseStart_1859290 baseEnd_1859290 := by
    simpa [prefixWord, tailWord_1859290, baseEnd_1859290] using wordTrace_append hprefix tailTrace_1859290
  have hstable : (prefixWord ++ tailWord_1859290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859290).length < 2 ^ (prefixWord ++ tailWord_1859290).sum := by decide
  have hdescent : baseEnd_1859290 < baseStart_1859290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859323 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 3]
def baseStart_1859323 : Nat := 118140960795 + 1859323 * 2 ^ 59
def prefixEnd_1859323 : Nat := 4983230072969 + 3 ^ 40 * 1859323 * 2
def baseEnd_1859323 : Nat := 954726390959734123911635

theorem tailTrace_1859323 : CollatzResearch.WordTrace tailWord_1859323 prefixEnd_1859323 954726390959734123911635 := by
  unfold tailWord_1859323
  simp only [CollatzResearch.WordTrace]
  refine ⟨67815081042997792932294623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45210054028665195288196415 67815081042997792932294623)
  ·
    refine ⟨101722621564496689398441935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67815081042997792932294623 101722621564496689398441935)
    ·
      refine ⟨152583932346745034097662903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101722621564496689398441935 152583932346745034097662903)
      ·
        refine ⟨228875898520117551146494355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152583932346745034097662903 228875898520117551146494355)
        ·
          refine ⟨343313847780176326719741533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228875898520117551146494355 343313847780176326719741533)
          ·
            refine ⟨128742692917566122519903075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343313847780176326719741533 128742692917566122519903075)
            ·
              refine ⟨193114039376349183779854613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128742692917566122519903075 193114039376349183779854613)
              ·
                refine ⟨9052220595766367989680685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193114039376349183779854613 9052220595766367989680685)
                ·
                  refine ⟨3394582723412387996130257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9052220595766367989680685 3394582723412387996130257)
                  ·
                    refine ⟨2545937042559290997097693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3394582723412387996130257 2545937042559290997097693)
                    ·
                      refine ⟨954726390959734123911635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2545937042559290997097693 954726390959734123911635)
                      ·
                        rfl

theorem cell23_1859323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 3].length) (baseStart_1859323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859323 prefixEnd_1859323 := by exact prefixLift 1859323
  have htrace : WordTrace (prefixWord ++ tailWord_1859323) baseStart_1859323 baseEnd_1859323 := by
    simpa [prefixWord, tailWord_1859323, baseEnd_1859323] using wordTrace_append hprefix tailTrace_1859323
  have hstable : (prefixWord ++ tailWord_1859323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859323).length < 2 ^ (prefixWord ++ tailWord_1859323).sum := by decide
  have hdescent : baseEnd_1859323 < baseStart_1859323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859340 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_1859340 : Nat := 118140960795 + 1859340 * 2 ^ 59
def prefixEnd_1859340 : Nat := 4983230072969 + 3 ^ 40 * 1859340 * 2
def baseEnd_1859340 : Nat := 954735120130860557399057

theorem tailTrace_1859340 : CollatzResearch.WordTrace tailWord_1859340 prefixEnd_1859340 954735120130860557399057 := by
  unfold tailWord_1859340
  simp only [CollatzResearch.WordTrace]
  refine ⟨33907850541968102417831737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45210467389290803223775649 33907850541968102417831737)
  ·
    refine ⟨25430887906476076813373803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33907850541968102417831737 25430887906476076813373803)
    ·
      refine ⟨38146331859714115220060705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25430887906476076813373803 38146331859714115220060705)
      ·
        refine ⟨28609748894785586415045529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38146331859714115220060705 28609748894785586415045529)
        ·
          refine ⟨21457311671089189811284147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28609748894785586415045529 21457311671089189811284147)
          ·
            refine ⟨32185967506633784716926221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21457311671089189811284147 32185967506633784716926221)
            ·
              refine ⟨12069737814987669268847333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32185967506633784716926221 12069737814987669268847333)
              ·
                refine ⟨2263075840310187987908875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12069737814987669268847333 2263075840310187987908875)
                ·
                  refine ⟨3394613760465281981863313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263075840310187987908875 3394613760465281981863313)
                  ·
                    refine ⟨2545960320348961486397485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3394613760465281981863313 2545960320348961486397485)
                    ·
                      refine ⟨954735120130860557399057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2545960320348961486397485 954735120130860557399057)
                      ·
                        rfl

theorem cell23_1859340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_1859340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859340 prefixEnd_1859340 := by exact prefixLift 1859340
  have htrace : WordTrace (prefixWord ++ tailWord_1859340) baseStart_1859340 baseEnd_1859340 := by
    simpa [prefixWord, tailWord_1859340, baseEnd_1859340] using wordTrace_append hprefix tailTrace_1859340
  have hstable : (prefixWord ++ tailWord_1859340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859340).length < 2 ^ (prefixWord ++ tailWord_1859340).sum := by decide
  have hdescent : baseEnd_1859340 < baseStart_1859340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859381 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1859381 : Nat := 118140960795 + 1859381 * 2 ^ 59
def prefixEnd_1859381 : Nat := 4983230072969 + 3 ^ 40 * 1859381 * 2
def baseEnd_1859381 : Nat := 318252057612564965662123

theorem tailTrace_1859381 : CollatzResearch.WordTrace tailWord_1859381 prefixEnd_1859381 318252057612564965662123 := by
  unfold tailWord_1859381
  simp only [CollatzResearch.WordTrace]
  refine ⟨67817196476787668837905997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45211464317858445891937331 67817196476787668837905997)
  ·
    refine ⟨25431448678795375814214749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67817196476787668837905997 25431448678795375814214749)
    ·
      refine ⟨9536793254548265930330531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25431448678795375814214749 9536793254548265930330531)
      ·
        refine ⟨14305189881822398895495797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536793254548265930330531 14305189881822398895495797)
        ·
          refine ⟨1341111551420849896452731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14305189881822398895495797 1341111551420849896452731)
          ·
            refine ⟨2011667327131274844679097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341111551420849896452731 2011667327131274844679097)
            ·
              refine ⟨1508750495348456133509323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011667327131274844679097 1508750495348456133509323)
              ·
                refine ⟨2263125743022684200263985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508750495348456133509323 2263125743022684200263985)
                ·
                  refine ⟨1697344307267013150197989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2263125743022684200263985 1697344307267013150197989)
                  ·
                    refine ⟨318252057612564965662123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1697344307267013150197989 318252057612564965662123)
                    ·
                      rfl

theorem cell23_1859381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1859381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859381 prefixEnd_1859381 := by exact prefixLift 1859381
  have htrace : WordTrace (prefixWord ++ tailWord_1859381) baseStart_1859381 baseEnd_1859381 := by
    simpa [prefixWord, tailWord_1859381, baseEnd_1859381] using wordTrace_append hprefix tailTrace_1859381
  have hstable : (prefixWord ++ tailWord_1859381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859381).length < 2 ^ (prefixWord ++ tailWord_1859381).sum := by decide
  have hdescent : baseEnd_1859381 < baseStart_1859381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859473 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_1859473 : Nat := 118140960795 + 1859473 * 2 ^ 59
def prefixEnd_1859473 : Nat := 4983230072969 + 3 ^ 40 * 1859473 * 2
def baseEnd_1859473 : Nat := 954803413057908537035945

theorem tailTrace_1859473 : CollatzResearch.WordTrace tailWord_1859473 prefixEnd_1859473 954803413057908537035945 := by
  unfold tailWord_1859473
  simp only [CollatzResearch.WordTrace]
  refine ⟨67820551992454368550255073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45213701328302912366836715 67820551992454368550255073)
  ·
    refine ⟨50865413994340776412691305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67820551992454368550255073 50865413994340776412691305)
    ·
      refine ⟨38149060495755582309518479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50865413994340776412691305 38149060495755582309518479)
      ·
        refine ⟨57223590743633373464277719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38149060495755582309518479 57223590743633373464277719)
        ·
          refine ⟨85835386115450060196416579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57223590743633373464277719 85835386115450060196416579)
          ·
            refine ⟨128753079173175090294624869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85835386115450060196416579 128753079173175090294624869)
            ·
              refine ⟨24141202344970329430242163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128753079173175090294624869 24141202344970329430242163)
              ·
                refine ⟨36211803517455494145363245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24141202344970329430242163 36211803517455494145363245)
                ·
                  refine ⟨13579426319045810304511217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36211803517455494145363245 13579426319045810304511217)
                  ·
                    refine ⟨10184569739284357728383413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13579426319045810304511217 10184569739284357728383413)
                    ·
                      refine ⟨954803413057908537035945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10184569739284357728383413 954803413057908537035945)
                      ·
                        rfl

theorem cell23_1859473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_1859473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859473 prefixEnd_1859473 := by exact prefixLift 1859473
  have htrace : WordTrace (prefixWord ++ tailWord_1859473) baseStart_1859473 baseEnd_1859473 := by
    simpa [prefixWord, tailWord_1859473, baseEnd_1859473] using wordTrace_append hprefix tailTrace_1859473
  have hstable : (prefixWord ++ tailWord_1859473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859473).length < 2 ^ (prefixWord ++ tailWord_1859473).sum := by decide
  have hdescent : baseEnd_1859473 < baseStart_1859473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859520 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 3]
def baseStart_1859520 : Nat := 118140960795 + 1859520 * 2 ^ 59
def prefixEnd_1859520 : Nat := 4983230072969 + 3 ^ 40 * 1859520 * 2
def baseEnd_1859520 : Nat := 954827546648669853148229

theorem tailTrace_1859520 : CollatzResearch.WordTrace tailWord_1859520 prefixEnd_1859520 954827546648669853148229 := by
  unfold tailWord_1859520
  simp only [CollatzResearch.WordTrace]
  refine ⟨33911133111642047788608007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45214844148856063718144009 33911133111642047788608007)
  ·
    refine ⟨50866699667463071682912011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33911133111642047788608007 50866699667463071682912011)
    ·
      refine ⟨76300049501194607524368017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50866699667463071682912011 76300049501194607524368017)
      ·
        refine ⟨57225037125895955643276013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76300049501194607524368017 57225037125895955643276013)
        ·
          refine ⟨21459388922210983366228505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57225037125895955643276013 21459388922210983366228505)
          ·
            refine ⟨16094541691658237524671379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21459388922210983366228505 16094541691658237524671379)
            ·
              refine ⟨24141812537487356287007069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16094541691658237524671379 24141812537487356287007069)
              ·
                refine ⟨9053179701557758607627651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24141812537487356287007069 9053179701557758607627651)
                ·
                  refine ⟨13579769552336637911441477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9053179701557758607627651 13579769552336637911441477)
                  ·
                    refine ⟨2546206791063119608395277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13579769552336637911441477 2546206791063119608395277)
                    ·
                      refine ⟨954827546648669853148229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2546206791063119608395277 954827546648669853148229)
                      ·
                        rfl

theorem cell23_1859520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_1859520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859520 prefixEnd_1859520 := by exact prefixLift 1859520
  have htrace : WordTrace (prefixWord ++ tailWord_1859520) baseStart_1859520 baseEnd_1859520 := by
    simpa [prefixWord, tailWord_1859520, baseEnd_1859520] using wordTrace_append hprefix tailTrace_1859520
  have hstable : (prefixWord ++ tailWord_1859520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859520).length < 2 ^ (prefixWord ++ tailWord_1859520).sum := by decide
  have hdescent : baseEnd_1859520 < baseStart_1859520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859540 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 8]
def baseStart_1859540 : Nat := 118140960795 + 1859540 * 2 ^ 59
def prefixEnd_1859540 : Nat := 4983230072969 + 3 ^ 40 * 1859540 * 2
def baseEnd_1859540 : Nat := 106093090695751086099793

theorem tailTrace_1859540 : CollatzResearch.WordTrace tailWord_1859540 prefixEnd_1859540 106093090695751086099793 := by
  unfold tailWord_1859540
  simp only [CollatzResearch.WordTrace]
  refine ⟨33911497841605819496472037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45215330455474425995296049 33911497841605819496472037)
  ·
    refine ⟨6358405845301091155588507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33911497841605819496472037 6358405845301091155588507)
    ·
      refine ⟨9537608767951636733382761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6358405845301091155588507 9537608767951636733382761)
      ·
        refine ⟨7153206575963727550037071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9537608767951636733382761 7153206575963727550037071)
        ·
          refine ⟨10729809863945591325055607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7153206575963727550037071 10729809863945591325055607)
          ·
            refine ⟨16094714795918386987583411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10729809863945591325055607 16094714795918386987583411)
            ·
              refine ⟨24142072193877580481375117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16094714795918386987583411 24142072193877580481375117)
              ·
                refine ⟨9053277072704092680515669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24142072193877580481375117 9053277072704092680515669)
                ·
                  refine ⟨106093090695751086099793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9053277072704092680515669 106093090695751086099793)
                  ·
                    rfl

theorem cell23_1859540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_1859540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859540 prefixEnd_1859540 := by exact prefixLift 1859540
  have htrace : WordTrace (prefixWord ++ tailWord_1859540) baseStart_1859540 baseEnd_1859540 := by
    simpa [prefixWord, tailWord_1859540, baseEnd_1859540] using wordTrace_append hprefix tailTrace_1859540
  have hstable : (prefixWord ++ tailWord_1859540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859540).length < 2 ^ (prefixWord ++ tailWord_1859540).sum := by decide
  have hdescent : baseEnd_1859540 < baseStart_1859540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859567 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 3]
def baseStart_1859567 : Nat := 118140960795 + 1859567 * 2 ^ 59
def prefixEnd_1859567 : Nat := 4983230072969 + 3 ^ 40 * 1859567 * 2
def baseEnd_1859567 : Nat := 954851680239431169260513

theorem tailTrace_1859567 : CollatzResearch.WordTrace tailWord_1859567 prefixEnd_1859567 954851680239431169260513 := by
  unfold tailWord_1859567
  simp only [CollatzResearch.WordTrace]
  refine ⟨67823980454113822604176955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45215986969409215069451303 67823980454113822604176955)
  ·
    refine ⟨101735970681170733906265433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67823980454113822604176955 101735970681170733906265433)
    ·
      refine ⟨76301978010878050429699075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101735970681170733906265433 76301978010878050429699075)
      ·
        refine ⟨114452967016317075644548613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76301978010878050429699075 114452967016317075644548613)
        ·
          refine ⟨21459931315559451683352865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114452967016317075644548613 21459931315559451683352865)
          ·
            refine ⟨16094948486669588762514649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21459931315559451683352865 16094948486669588762514649)
            ·
              refine ⟨12071211365002191571885987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16094948486669588762514649 12071211365002191571885987)
              ·
                refine ⟨18106817047503287357828981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12071211365002191571885987 18106817047503287357828981)
                ·
                  refine ⟨1697514098203433189796467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18106817047503287357828981 1697514098203433189796467)
                  ·
                    refine ⟨2546271147305149784694701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1697514098203433189796467 2546271147305149784694701)
                    ·
                      refine ⟨954851680239431169260513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2546271147305149784694701 954851680239431169260513)
                      ·
                        rfl

theorem cell23_1859567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 3].length) (baseStart_1859567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859567 prefixEnd_1859567 := by exact prefixLift 1859567
  have htrace : WordTrace (prefixWord ++ tailWord_1859567) baseStart_1859567 baseEnd_1859567 := by
    simpa [prefixWord, tailWord_1859567, baseEnd_1859567] using wordTrace_append hprefix tailTrace_1859567
  have hstable : (prefixWord ++ tailWord_1859567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859567).length < 2 ^ (prefixWord ++ tailWord_1859567).sum := by decide
  have hdescent : baseEnd_1859567 < baseStart_1859567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859637 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1859637 : Nat := 118140960795 + 1859637 * 2 ^ 59
def prefixEnd_1859637 : Nat := 4983230072969 + 3 ^ 40 * 1859637 * 2
def baseEnd_1859637 : Nat := 954887623885245895385191

theorem tailTrace_1859637 : CollatzResearch.WordTrace tailWord_1859637 prefixEnd_1859637 954887623885245895385191 := by
  unfold tailWord_1859637
  simp only [CollatzResearch.WordTrace]
  refine ⟨67826533563860224559225165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45217689042573483039483443 67826533563860224559225165)
  ·
    refine ⟨25434950086447584209709437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67826533563860224559225165 25434950086447584209709437)
    ·
      refine ⟨9538106282417844078641039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25434950086447584209709437 9538106282417844078641039)
      ·
        refine ⟨14307159423626766117961559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9538106282417844078641039 14307159423626766117961559)
        ·
          refine ⟨21460739135440149176942339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14307159423626766117961559 21460739135440149176942339)
          ·
            refine ⟨32191108703160223765413509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21460739135440149176942339 32191108703160223765413509)
            ·
              refine ⟨6035832881842541956015033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32191108703160223765413509 6035832881842541956015033)
              ·
                refine ⟨4526874661381906467011275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6035832881842541956015033 4526874661381906467011275)
                ·
                  refine ⟨6790311992072859700516913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526874661381906467011275 6790311992072859700516913)
                  ·
                    refine ⟨5092733994054644775387685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6790311992072859700516913 5092733994054644775387685)
                    ·
                      refine ⟨954887623885245895385191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5092733994054644775387685 954887623885245895385191)
                      ·
                        rfl

theorem cell23_1859637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1859637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859637 prefixEnd_1859637 := by exact prefixLift 1859637
  have htrace : WordTrace (prefixWord ++ tailWord_1859637) baseStart_1859637 baseEnd_1859637 := by
    simpa [prefixWord, tailWord_1859637, baseEnd_1859637] using wordTrace_append hprefix tailTrace_1859637
  have hstable : (prefixWord ++ tailWord_1859637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859637).length < 2 ^ (prefixWord ++ tailWord_1859637).sum := by decide
  have hdescent : baseEnd_1859637 < baseStart_1859637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859644 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_1859644 : Nat := 118140960795 + 1859644 * 2 ^ 59
def prefixEnd_1859644 : Nat := 4983230072969 + 3 ^ 40 * 1859644 * 2
def baseEnd_1859644 : Nat := 954891218249827367997659

theorem tailTrace_1859644 : CollatzResearch.WordTrace tailWord_1859644 prefixEnd_1859644 954891218249827367997659 := by
  unfold tailWord_1859644
  simp only [CollatzResearch.WordTrace]
  refine ⟨33913394437417432377364993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45217859249889909836486657 33913394437417432377364993)
  ·
    refine ⟨25435045828063074283023745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33913394437417432377364993 25435045828063074283023745)
    ·
      refine ⟨19076284371047305712267809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25435045828063074283023745 19076284371047305712267809)
      ·
        refine ⟨14307213278285479284200857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19076284371047305712267809 14307213278285479284200857)
        ·
          refine ⟨10730409958714109463150643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14307213278285479284200857 10730409958714109463150643)
          ·
            refine ⟨16095614938071164194725965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10730409958714109463150643 16095614938071164194725965)
            ·
              refine ⟨6035855601776686573022237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16095614938071164194725965 6035855601776686573022237)
              ·
                refine ⟨2263445850666257464883339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6035855601776686573022237 2263445850666257464883339)
                ·
                  refine ⟨3395168775999386197325009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263445850666257464883339 3395168775999386197325009)
                  ·
                    refine ⟨2546376581999539647993757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3395168775999386197325009 2546376581999539647993757)
                    ·
                      refine ⟨954891218249827367997659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2546376581999539647993757 954891218249827367997659)
                      ·
                        rfl

theorem cell23_1859644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_1859644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859644 prefixEnd_1859644 := by exact prefixLift 1859644
  have htrace : WordTrace (prefixWord ++ tailWord_1859644) baseStart_1859644 baseEnd_1859644 := by
    simpa [prefixWord, tailWord_1859644, baseEnd_1859644] using wordTrace_append hprefix tailTrace_1859644
  have hstable : (prefixWord ++ tailWord_1859644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859644).length < 2 ^ (prefixWord ++ tailWord_1859644).sum := by decide
  have hdescent : baseEnd_1859644 < baseStart_1859644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859654 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1859654 : Nat := 118140960795 + 1859654 * 2 ^ 59
def prefixEnd_1859654 : Nat := 4983230072969 + 3 ^ 40 * 1859654 * 2
def baseEnd_1859654 : Nat := 954896353056372328872613

theorem tailTrace_1859654 : CollatzResearch.WordTrace tailWord_1859654 prefixEnd_1859654 954896353056372328872613 := by
  unfold tailWord_1859654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119598550149957389456063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45218102403199090975062677 2119598550149957389456063)
  ·
    refine ⟨3179397825224936084184095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119598550149957389456063 3179397825224936084184095)
    ·
      refine ⟨4769096737837404126276143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3179397825224936084184095 4769096737837404126276143)
      ·
        refine ⟨7153645106756106189414215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4769096737837404126276143 7153645106756106189414215)
        ·
          refine ⟨10730467660134159284121323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7153645106756106189414215 10730467660134159284121323)
          ·
            refine ⟨16095701490201238926181985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10730467660134159284121323 16095701490201238926181985)
            ·
              refine ⟨12071776117650929194636489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16095701490201238926181985 12071776117650929194636489)
              ·
                refine ⟨9053832088238196895977367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12071776117650929194636489 9053832088238196895977367)
                ·
                  refine ⟨13580748132357295343966051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9053832088238196895977367 13580748132357295343966051)
                  ·
                    refine ⟨20371122198535943015949077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13580748132357295343966051 20371122198535943015949077)
                    ·
                      refine ⟨954896353056372328872613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20371122198535943015949077 954896353056372328872613)
                      ·
                        rfl

theorem cell23_1859654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1859654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859654 prefixEnd_1859654 := by exact prefixLift 1859654
  have htrace : WordTrace (prefixWord ++ tailWord_1859654) baseStart_1859654 baseEnd_1859654 := by
    simpa [prefixWord, tailWord_1859654, baseEnd_1859654] using wordTrace_append hprefix tailTrace_1859654
  have hstable : (prefixWord ++ tailWord_1859654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859654).length < 2 ^ (prefixWord ++ tailWord_1859654).sum := by decide
  have hdescent : baseEnd_1859654 < baseStart_1859654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859660 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_1859660 : Nat := 118140960795 + 1859660 * 2 ^ 59
def prefixEnd_1859660 : Nat := 4983230072969 + 3 ^ 40 * 1859660 * 2
def baseEnd_1859660 : Nat := 318299811313433101799195

theorem tailTrace_1859660 : CollatzResearch.WordTrace tailWord_1859660 prefixEnd_1859660 318299811313433101799195 := by
  unfold tailWord_1859660
  simp only [CollatzResearch.WordTrace]
  refine ⟨33913686221388449743656217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45218248295184599658208289 33913686221388449743656217)
  ·
    refine ⟨25435264666041337307742163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33913686221388449743656217 25435264666041337307742163)
    ·
      refine ⟨38152896999062005961613245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25435264666041337307742163 38152896999062005961613245)
      ·
        refine ⟨14307336374648252235604967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38152896999062005961613245 14307336374648252235604967)
        ·
          refine ⟨21461004561972378353407451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14307336374648252235604967 21461004561972378353407451)
          ·
            refine ⟨32191506842958567530111177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21461004561972378353407451 32191506842958567530111177)
            ·
              refine ⟨24143630132218925647583383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32191506842958567530111177 24143630132218925647583383)
              ·
                refine ⟨36215445198328388471375075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24143630132218925647583383 36215445198328388471375075)
                ·
                  refine ⟨54323167797492582707062613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36215445198328388471375075 54323167797492582707062613)
                  ·
                    refine ⟨318299811313433101799195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 54323167797492582707062613 318299811313433101799195)
                    ·
                      rfl

theorem cell23_1859660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_1859660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859660 prefixEnd_1859660 := by exact prefixLift 1859660
  have htrace : WordTrace (prefixWord ++ tailWord_1859660) baseStart_1859660 baseEnd_1859660 := by
    simpa [prefixWord, tailWord_1859660, baseEnd_1859660] using wordTrace_append hprefix tailTrace_1859660
  have hstable : (prefixWord ++ tailWord_1859660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859660).length < 2 ^ (prefixWord ++ tailWord_1859660).sum := by decide
  have hdescent : baseEnd_1859660 < baseStart_1859660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859684 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_1859684 : Nat := 118140960795 + 1859684 * 2 ^ 59
def prefixEnd_1859684 : Nat := 4983230072969 + 3 ^ 40 * 1859684 * 2
def baseEnd_1859684 : Nat := 954911757476007211497475

theorem tailTrace_1859684 : CollatzResearch.WordTrace tailWord_1859684 prefixEnd_1859684 954911757476007211497475 := by
  unfold tailWord_1859684
  simp only [CollatzResearch.WordTrace]
  refine ⟨33914123897344975793093053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45218831863126634390790737 33914123897344975793093053)
  ·
    refine ⟨12717796461504365922409895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33914123897344975793093053 12717796461504365922409895)
    ·
      refine ⟨19076694692256548883614843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12717796461504365922409895 19076694692256548883614843)
      ·
        refine ⟨28615042038384823325422265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19076694692256548883614843 28615042038384823325422265)
        ·
          refine ⟨21461281528788617494066699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28615042038384823325422265 21461281528788617494066699)
          ·
            refine ⟨32191922293182926241100049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21461281528788617494066699 32191922293182926241100049)
            ·
              refine ⟨24143941719887194680825037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32191922293182926241100049 24143941719887194680825037)
              ·
                refine ⟨9053978144957698005309389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24143941719887194680825037 9053978144957698005309389)
                ·
                  refine ⟨3395241804359136751991021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9053978144957698005309389 3395241804359136751991021)
                  ·
                    refine ⟨1273215676634676281996633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3395241804359136751991021 1273215676634676281996633)
                    ·
                      refine ⟨954911757476007211497475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273215676634676281996633 954911757476007211497475)
                      ·
                        rfl

theorem cell23_1859684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_1859684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859684 prefixEnd_1859684 := by exact prefixLift 1859684
  have htrace : WordTrace (prefixWord ++ tailWord_1859684) baseStart_1859684 baseEnd_1859684 := by
    simpa [prefixWord, tailWord_1859684, baseEnd_1859684] using wordTrace_append hprefix tailTrace_1859684
  have hstable : (prefixWord ++ tailWord_1859684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859684).length < 2 ^ (prefixWord ++ tailWord_1859684).sum := by decide
  have hdescent : baseEnd_1859684 < baseStart_1859684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859735 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 1, 3, 2]
def baseStart_1859735 : Nat := 118140960795 + 1859735 * 2 ^ 59
def prefixEnd_1859735 : Nat := 4983230072969 + 3 ^ 40 * 1859735 * 2
def baseEnd_1859735 : Nat := 954937944989386511959741

theorem tailTrace_1859735 : CollatzResearch.WordTrace tailWord_1859735 prefixEnd_1859735 954937944989386511959741 := by
  unfold tailWord_1859735
  simp only [CollatzResearch.WordTrace]
  refine ⟨67830107917505187296292659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45220071945003458197528439 67830107917505187296292659)
  ·
    refine ⟨101745161876257780944438989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67830107917505187296292659 101745161876257780944438989)
    ·
      refine ⟨38154435703596667854164621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101745161876257780944438989 38154435703596667854164621)
      ·
        refine ⟨14307913388848750445311733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38154435703596667854164621 14307913388848750445311733)
        ·
          refine ⟨1341366880204570354247975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14307913388848750445311733 1341366880204570354247975)
          ·
            refine ⟨2012050320306855531371963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341366880204570354247975 2012050320306855531371963)
            ·
              refine ⟨3018075480460283297057945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012050320306855531371963 3018075480460283297057945)
              ·
                refine ⟨2263556610345212472793459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018075480460283297057945 2263556610345212472793459)
                ·
                  refine ⟨3395334915517818709190189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263556610345212472793459 3395334915517818709190189)
                  ·
                    refine ⟨1273250593319182015946321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3395334915517818709190189 1273250593319182015946321)
                    ·
                      refine ⟨954937944989386511959741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273250593319182015946321 954937944989386511959741)
                      ·
                        rfl

theorem cell23_1859735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_1859735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859735 prefixEnd_1859735 := by exact prefixLift 1859735
  have htrace : WordTrace (prefixWord ++ tailWord_1859735) baseStart_1859735 baseEnd_1859735 := by
    simpa [prefixWord, tailWord_1859735, baseEnd_1859735] using wordTrace_append hprefix tailTrace_1859735
  have hstable : (prefixWord ++ tailWord_1859735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859735).length < 2 ^ (prefixWord ++ tailWord_1859735).sum := by decide
  have hdescent : baseEnd_1859735 < baseStart_1859735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859747 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 3]
def baseStart_1859747 : Nat := 118140960795 + 1859747 * 2 ^ 59
def prefixEnd_1859747 : Nat := 4983230072969 + 3 ^ 40 * 1859747 * 2
def baseEnd_1859747 : Nat := 954944106757240465009685

theorem tailTrace_1859747 : CollatzResearch.WordTrace tailWord_1859747 prefixEnd_1859747 954944106757240465009685 := by
  unfold tailWord_1859747
  simp only [CollatzResearch.WordTrace]
  refine ⟨67830545593461713345729495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45220363728974475563819663 67830545593461713345729495)
  ·
    refine ⟨101745818390192570018594243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67830545593461713345729495 101745818390192570018594243)
    ·
      refine ⟨152618727585288855027891365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101745818390192570018594243 152618727585288855027891365)
      ·
        refine ⟨28616011422241660317729631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152618727585288855027891365 28616011422241660317729631)
        ·
          refine ⟨42924017133362490476594447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28616011422241660317729631 42924017133362490476594447)
          ·
            refine ⟨64386025700043735714891671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42924017133362490476594447 64386025700043735714891671)
            ·
              refine ⟨96579038550065603572337507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64386025700043735714891671 96579038550065603572337507)
              ·
                refine ⟨144868557825098405358506261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96579038550065603572337507 144868557825098405358506261)
                ·
                  refine ⟨6790713648051487751179981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144868557825098405358506261 6790713648051487751179981)
                  ·
                    refine ⟨2546517618019307906692493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6790713648051487751179981 2546517618019307906692493)
                    ·
                      refine ⟨954944106757240465009685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2546517618019307906692493 954944106757240465009685)
                      ·
                        rfl

theorem cell23_1859747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_1859747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859747 prefixEnd_1859747 := by exact prefixLift 1859747
  have htrace : WordTrace (prefixWord ++ tailWord_1859747) baseStart_1859747 baseEnd_1859747 := by
    simpa [prefixWord, tailWord_1859747, baseEnd_1859747] using wordTrace_append hprefix tailTrace_1859747
  have hstable : (prefixWord ++ tailWord_1859747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859747).length < 2 ^ (prefixWord ++ tailWord_1859747).sum := by decide
  have hdescent : baseEnd_1859747 < baseStart_1859747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859778 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1859778 : Nat := 118140960795 + 1859778 * 2 ^ 59
def prefixEnd_1859778 : Nat := 4983230072969 + 3 ^ 40 * 1859778 * 2
def baseEnd_1859778 : Nat := 954960024657529843722043

theorem tailTrace_1859778 : CollatzResearch.WordTrace tailWord_1859778 prefixEnd_1859778 954960024657529843722043 := by
  unfold tailWord_1859778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16957919064087351410026997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45221117504232937093405325 16957919064087351410026997)
  ·
    refine ⟨1589804912258189194690031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16957919064087351410026997 1589804912258189194690031)
    ·
      refine ⟨2384707368387283792035047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589804912258189194690031 2384707368387283792035047)
      ·
        refine ⟨3577061052580925688052571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384707368387283792035047 3577061052580925688052571)
        ·
          refine ⟨5365591578871388532078857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577061052580925688052571 5365591578871388532078857)
          ·
            refine ⟨4024193684153541399059143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5365591578871388532078857 4024193684153541399059143)
            ·
              refine ⟨6036290526230312098588715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024193684153541399059143 6036290526230312098588715)
              ·
                refine ⟨9054435789345468147883073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036290526230312098588715 9054435789345468147883073)
                ·
                  refine ⟨6790826842009101110912305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9054435789345468147883073 6790826842009101110912305)
                  ·
                    refine ⟨5093120131506825833184229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6790826842009101110912305 5093120131506825833184229)
                    ·
                      refine ⟨954960024657529843722043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5093120131506825833184229 954960024657529843722043)
                      ·
                        rfl

theorem cell23_1859778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1859778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859778 prefixEnd_1859778 := by exact prefixLift 1859778
  have htrace : WordTrace (prefixWord ++ tailWord_1859778) baseStart_1859778 baseEnd_1859778 := by
    simpa [prefixWord, tailWord_1859778, baseEnd_1859778] using wordTrace_append hprefix tailTrace_1859778
  have hstable : (prefixWord ++ tailWord_1859778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859778).length < 2 ^ (prefixWord ++ tailWord_1859778).sum := by decide
  have hdescent : baseEnd_1859778 < baseStart_1859778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859787 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 4]
def baseStart_1859787 : Nat := 118140960795 + 1859787 * 2 ^ 59
def prefixEnd_1859787 : Nat := 4983230072969 + 3 ^ 40 * 1859787 * 2
def baseEnd_1859787 : Nat := 954964645983420308509501

theorem tailTrace_1859787 : CollatzResearch.WordTrace tailWord_1859787 prefixEnd_1859787 954964645983420308509501 := by
  unfold tailWord_1859787
  simp only [CollatzResearch.WordTrace]
  refine ⟨67832004513316800177185615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45221336342211200118123743 67832004513316800177185615)
  ·
    refine ⟨101748006769975200265778423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67832004513316800177185615 101748006769975200265778423)
    ·
      refine ⟨152622010154962800398667635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101748006769975200265778423 152622010154962800398667635)
      ·
        refine ⟨228933015232444200598001453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152622010154962800398667635 228933015232444200598001453)
        ·
          refine ⟨85849880712166575224250545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228933015232444200598001453 85849880712166575224250545)
          ·
            refine ⟨64387410534124931418187909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85849880712166575224250545 64387410534124931418187909)
            ·
              refine ⟨12072639475148424640910233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64387410534124931418187909 12072639475148424640910233)
              ·
                refine ⟨9054479606361318480682675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12072639475148424640910233 9054479606361318480682675)
                ·
                  refine ⟨13581719409541977721024013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9054479606361318480682675 13581719409541977721024013)
                  ·
                    refine ⟨5093144778578241645384005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13581719409541977721024013 5093144778578241645384005)
                    ·
                      refine ⟨954964645983420308509501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5093144778578241645384005 954964645983420308509501)
                      ·
                        rfl

theorem cell23_1859787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 4].length) (baseStart_1859787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859787 prefixEnd_1859787 := by exact prefixLift 1859787
  have htrace : WordTrace (prefixWord ++ tailWord_1859787) baseStart_1859787 baseEnd_1859787 := by
    simpa [prefixWord, tailWord_1859787, baseEnd_1859787] using wordTrace_append hprefix tailTrace_1859787
  have hstable : (prefixWord ++ tailWord_1859787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859787).length < 2 ^ (prefixWord ++ tailWord_1859787).sum := by decide
  have hdescent : baseEnd_1859787 < baseStart_1859787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859824 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 3]
def baseStart_1859824 : Nat := 118140960795 + 1859824 * 2 ^ 59
def prefixEnd_1859824 : Nat := 4983230072969 + 3 ^ 40 * 1859824 * 2
def baseEnd_1859824 : Nat := 954983644767636663746831

theorem tailTrace_1859824 : CollatzResearch.WordTrace tailWord_1859824 prefixEnd_1859824 954983644767636663746831 := by
  unfold tailWord_1859824
  simp only [CollatzResearch.WordTrace]
  refine ⟨33916677007091377748141263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45222236009455170330855017 33916677007091377748141263)
  ·
    refine ⟨50875015510637066622211895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33916677007091377748141263 50875015510637066622211895)
    ·
      refine ⟨76312523265955599933317843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50875015510637066622211895 76312523265955599933317843)
      ·
        refine ⟨114468784898933399899976765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76312523265955599933317843 114468784898933399899976765)
        ·
          refine ⟨42925794337100024962491287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114468784898933399899976765 42925794337100024962491287)
          ·
            refine ⟨64388691505650037443736931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42925794337100024962491287 64388691505650037443736931)
            ·
              refine ⟨96583037258475056165605397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64388691505650037443736931 96583037258475056165605397)
              ·
                refine ⟨4527329871491018257762753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96583037258475056165605397 4527329871491018257762753)
                ·
                  refine ⟨3395497403618263693322065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4527329871491018257762753 3395497403618263693322065)
                  ·
                    refine ⟨2546623052713697769991549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3395497403618263693322065 2546623052713697769991549)
                    ·
                      refine ⟨954983644767636663746831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2546623052713697769991549 954983644767636663746831)
                      ·
                        rfl

theorem cell23_1859824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_1859824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859824 prefixEnd_1859824 := by exact prefixLift 1859824
  have htrace : WordTrace (prefixWord ++ tailWord_1859824) baseStart_1859824 baseEnd_1859824 := by
    simpa [prefixWord, tailWord_1859824, baseEnd_1859824] using wordTrace_append hprefix tailTrace_1859824
  have hstable : (prefixWord ++ tailWord_1859824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859824).length < 2 ^ (prefixWord ++ tailWord_1859824).sum := by decide
  have hdescent : baseEnd_1859824 < baseStart_1859824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859827 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 8]
def baseStart_1859827 : Nat := 118140960795 + 1859827 * 2 ^ 59
def prefixEnd_1859827 : Nat := 4983230072969 + 3 ^ 40 * 1859827 * 2
def baseEnd_1859827 : Nat := 106109465023288905778813

theorem tailTrace_1859827 : CollatzResearch.WordTrace tailWord_1859827 prefixEnd_1859827 106109465023288905778813 := by
  unfold tailWord_1859827
  simp only [CollatzResearch.WordTrace]
  refine ⟨67833463433171887008641735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45222308955447924672427823 67833463433171887008641735)
  ·
    refine ⟨101750195149757830512962603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67833463433171887008641735 101750195149757830512962603)
    ·
      refine ⟨152625292724636745769443905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101750195149757830512962603 152625292724636745769443905)
      ·
        refine ⟨114468969543477559327082929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152625292724636745769443905 114468969543477559327082929)
        ·
          refine ⟨85851727157608169495312197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114468969543477559327082929 85851727157608169495312197)
          ·
            refine ⟨16097198842051531780371037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85851727157608169495312197 16097198842051531780371037)
            ·
              refine ⟨6036449565769324417639139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16097198842051531780371037 6036449565769324417639139)
              ·
                refine ⟨9054674348653986626458709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036449565769324417639139 9054674348653986626458709)
                ·
                  refine ⟨106109465023288905778813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9054674348653986626458709 106109465023288905778813)
                  ·
                    rfl

theorem cell23_1859827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 8].length) (baseStart_1859827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859827 prefixEnd_1859827 := by exact prefixLift 1859827
  have htrace : WordTrace (prefixWord ++ tailWord_1859827) baseStart_1859827 baseEnd_1859827 := by
    simpa [prefixWord, tailWord_1859827, baseEnd_1859827] using wordTrace_append hprefix tailTrace_1859827
  have hstable : (prefixWord ++ tailWord_1859827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859827).length < 2 ^ (prefixWord ++ tailWord_1859827).sum := by decide
  have hdescent : baseEnd_1859827 < baseStart_1859827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859854 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1859854 : Nat := 118140960795 + 1859854 * 2 ^ 59
def prefixEnd_1859854 : Nat := 4983230072969 + 3 ^ 40 * 1859854 * 2
def baseEnd_1859854 : Nat := 954999049187271546371693

theorem tailTrace_1859854 : CollatzResearch.WordTrace tailWord_1859854 prefixEnd_1859854 954999049187271546371693 := by
  unfold tailWord_1859854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8479306025509258827484327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45222965469382713746583077 8479306025509258827484327)
  ·
    refine ⟨12718959038263888241226491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8479306025509258827484327 12718959038263888241226491)
    ·
      refine ⟨19078438557395832361839737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12718959038263888241226491 19078438557395832361839737)
      ·
        refine ⟨14308828918046874271379803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19078438557395832361839737 14308828918046874271379803)
        ·
          refine ⟨21463243377070311407069705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14308828918046874271379803 21463243377070311407069705)
          ·
            refine ⟨16097432532802733555302279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21463243377070311407069705 16097432532802733555302279)
            ·
              refine ⟨24146148799204100332953419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16097432532802733555302279 24146148799204100332953419)
              ·
                refine ⟨36219223198806150499430129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24146148799204100332953419 36219223198806150499430129)
                ·
                  refine ⟨27164417399104612874572597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36219223198806150499430129 27164417399104612874572597)
                  ·
                    refine ⟨2546664131166057456991181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27164417399104612874572597 2546664131166057456991181)
                    ·
                      refine ⟨954999049187271546371693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2546664131166057456991181 954999049187271546371693)
                      ·
                        rfl

theorem cell23_1859854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1859854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859854 prefixEnd_1859854 := by exact prefixLift 1859854
  have htrace : WordTrace (prefixWord ++ tailWord_1859854) baseStart_1859854 baseEnd_1859854 := by
    simpa [prefixWord, tailWord_1859854, baseEnd_1859854] using wordTrace_append hprefix tailTrace_1859854
  have hstable : (prefixWord ++ tailWord_1859854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859854).length < 2 ^ (prefixWord ++ tailWord_1859854).sum := by decide
  have hdescent : baseEnd_1859854 < baseStart_1859854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859882 : List Nat := [3, 1, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1859882 : Nat := 118140960795 + 1859882 * 2 ^ 59
def prefixEnd_1859882 : Nat := 4983230072969 + 3 ^ 40 * 1859882 * 2
def baseEnd_1859882 : Nat := 318337808881865812273855

theorem tailTrace_1859882 : CollatzResearch.WordTrace tailWord_1859882 prefixEnd_1859882 318337808881865812273855 := by
  unfold tailWord_1859882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16958867361993157850473475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45223646298648420934595933 16958867361993157850473475)
  ·
    refine ⟨25438301042989736775710213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16958867361993157850473475 25438301042989736775710213)
    ·
      refine ⟨4769681445560575645445665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25438301042989736775710213 4769681445560575645445665)
      ·
        refine ⟨3577261084170431734084249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4769681445560575645445665 3577261084170431734084249)
        ·
          refine ⟨2682945813127823800563187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3577261084170431734084249 2682945813127823800563187)
          ·
            refine ⟨4024418719691735700844781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682945813127823800563187 4024418719691735700844781)
            ·
              refine ⟨1509157019884400887816793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4024418719691735700844781 1509157019884400887816793)
              ·
                refine ⟨1131867764913300665862595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509157019884400887816793 1131867764913300665862595)
                ·
                  refine ⟨1697801647369950998793893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131867764913300665862595 1697801647369950998793893)
                  ·
                    refine ⟨318337808881865812273855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1697801647369950998793893 318337808881865812273855)
                    ·
                      rfl

theorem cell23_1859882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1859882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859882 prefixEnd_1859882 := by exact prefixLift 1859882
  have htrace : WordTrace (prefixWord ++ tailWord_1859882) baseStart_1859882 baseEnd_1859882 := by
    simpa [prefixWord, tailWord_1859882, baseEnd_1859882] using wordTrace_append hprefix tailTrace_1859882
  have hstable : (prefixWord ++ tailWord_1859882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859882).length < 2 ^ (prefixWord ++ tailWord_1859882).sum := by decide
  have hdescent : baseEnd_1859882 < baseStart_1859882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859904 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 6, 4]
def baseStart_1859904 : Nat := 118140960795 + 1859904 * 2 ^ 59
def prefixEnd_1859904 : Nat := 4983230072969 + 3 ^ 40 * 1859904 * 2
def baseEnd_1859904 : Nat := 318341574406665450248821

theorem tailTrace_1859904 : CollatzResearch.WordTrace tailWord_1859904 prefixEnd_1859904 318341574406665450248821 := by
  unfold tailWord_1859904
  simp only [CollatzResearch.WordTrace]
  refine ⟨33918135926946464579597383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45224181235928619439463177 33918135926946464579597383)
  ·
    refine ⟨50877203890419696869396075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33918135926946464579597383 50877203890419696869396075)
    ·
      refine ⟨76315805835629545304094113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50877203890419696869396075 76315805835629545304094113)
      ·
        refine ⟨57236854376722158978070585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76315805835629545304094113 57236854376722158978070585)
        ·
          refine ⟨42927640782541619233552939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57236854376722158978070585 42927640782541619233552939)
          ·
            refine ⟨64391461173812428850329409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42927640782541619233552939 64391461173812428850329409)
            ·
              refine ⟨48293595880359321637747057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64391461173812428850329409 48293595880359321637747057)
              ·
                refine ⟨36220196910269491228310293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48293595880359321637747057 36220196910269491228310293)
                ·
                  refine ⟨1697821730168882401327045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36220196910269491228310293 1697821730168882401327045)
                  ·
                    refine ⟨318341574406665450248821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1697821730168882401327045 318341574406665450248821)
                    ·
                      rfl

theorem cell23_1859904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 4].length) (baseStart_1859904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859904 prefixEnd_1859904 := by exact prefixLift 1859904
  have htrace : WordTrace (prefixWord ++ tailWord_1859904) baseStart_1859904 baseEnd_1859904 := by
    simpa [prefixWord, tailWord_1859904, baseEnd_1859904] using wordTrace_append hprefix tailTrace_1859904
  have hstable : (prefixWord ++ tailWord_1859904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859904).length < 2 ^ (prefixWord ++ tailWord_1859904).sum := by decide
  have hdescent : baseEnd_1859904 < baseStart_1859904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859908 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1859908 : Nat := 118140960795 + 1859908 * 2 ^ 59
def prefixEnd_1859908 : Nat := 4983230072969 + 3 ^ 40 * 1859908 * 2
def baseEnd_1859908 : Nat := 318342259047538111698815

theorem tailTrace_1859908 : CollatzResearch.WordTrace tailWord_1859908 prefixEnd_1859908 318342259047538111698815 := by
  unfold tailWord_1859908
  simp only [CollatzResearch.WordTrace]
  refine ⟨33918208872939218921170189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45224278497252291894893585 33918208872939218921170189)
  ·
    refine ⟨12719328327352207095438821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33918208872939218921170189 12719328327352207095438821)
    ·
      refine ⟨2384874061378538830394779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12719328327352207095438821 2384874061378538830394779)
      ·
        refine ⟨3577311092067808245592169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384874061378538830394779 3577311092067808245592169)
        ·
          refine ⟨2682983319050856184194127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3577311092067808245592169 2682983319050856184194127)
          ·
            refine ⟨4024474978576284276291191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682983319050856184194127 4024474978576284276291191)
            ·
              refine ⟨6036712467864426414436787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024474978576284276291191 6036712467864426414436787)
              ·
                refine ⟨9055068701796639621655181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036712467864426414436787 9055068701796639621655181)
                ·
                  refine ⟨3395650763173739858120693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9055068701796639621655181 3395650763173739858120693)
                  ·
                    refine ⟨318342259047538111698815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3395650763173739858120693 318342259047538111698815)
                    ·
                      rfl

theorem cell23_1859908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1859908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859908 prefixEnd_1859908 := by exact prefixLift 1859908
  have htrace : WordTrace (prefixWord ++ tailWord_1859908) baseStart_1859908 baseEnd_1859908 := by
    simpa [prefixWord, tailWord_1859908, baseEnd_1859908] using wordTrace_append hprefix tailTrace_1859908
  have hstable : (prefixWord ++ tailWord_1859908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859908).length < 2 ^ (prefixWord ++ tailWord_1859908).sum := by decide
  have hdescent : baseEnd_1859908 < baseStart_1859908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859938 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1859938 : Nat := 118140960795 + 1859938 * 2 ^ 59
def prefixEnd_1859938 : Nat := 4983230072969 + 3 ^ 40 * 1859938 * 2
def baseEnd_1859938 : Nat := 318347393854083072573769

theorem tailTrace_1859938 : CollatzResearch.WordTrace tailWord_1859938 prefixEnd_1859938 318347393854083072573769 := by
  unfold tailWord_1859938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16959377983942438241483117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45225007957179835310621645 16959377983942438241483117)
  ·
    refine ⟨6359766743978414340556169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16959377983942438241483117 6359766743978414340556169)
    ·
      refine ⟨4769825057983810755417127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6359766743978414340556169 4769825057983810755417127)
      ·
        refine ⟨7154737586975716133125691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4769825057983810755417127 7154737586975716133125691)
        ·
          refine ⟨10732106380463574199688537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154737586975716133125691 10732106380463574199688537)
          ·
            refine ⟨8049079785347680649766403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10732106380463574199688537 8049079785347680649766403)
            ·
              refine ⟨12073619678021520974649605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049079785347680649766403 12073619678021520974649605)
              ·
                refine ⟨2263803689629035182746801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12073619678021520974649605 2263803689629035182746801)
                ·
                  refine ⟨1697852767221776387060101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2263803689629035182746801 1697852767221776387060101)
                  ·
                    refine ⟨318347393854083072573769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1697852767221776387060101 318347393854083072573769)
                    ·
                      rfl

theorem cell23_1859938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1859938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859938 prefixEnd_1859938 := by exact prefixLift 1859938
  have htrace : WordTrace (prefixWord ++ tailWord_1859938) baseStart_1859938 baseEnd_1859938 := by
    simpa [prefixWord, tailWord_1859938, baseEnd_1859938] using wordTrace_append hprefix tailTrace_1859938
  have hstable : (prefixWord ++ tailWord_1859938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859938).length < 2 ^ (prefixWord ++ tailWord_1859938).sum := by decide
  have hdescent : baseEnd_1859938 < baseStart_1859938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859945 : List Nat := [1, 2, 1, 1, 1, 3, 5, 4, 1, 2, 2]
def baseStart_1859945 : Nat := 118140960795 + 1859945 * 2 ^ 59
def prefixEnd_1859945 : Nat := 4983230072969 + 3 ^ 40 * 1859945 * 2
def baseEnd_1859945 : Nat := 955045775926830690333775

theorem tailTrace_1859945 : CollatzResearch.WordTrace tailWord_1859945 prefixEnd_1859945 955045775926830690333775 := by
  unfold tailWord_1859945
  simp only [CollatzResearch.WordTrace]
  refine ⟨67837767246744393161437289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45225178164496262107624859 67837767246744393161437289)
  ·
    refine ⟨50878325435058294871077967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67837767246744393161437289 50878325435058294871077967)
    ·
      refine ⟨76317488152587442306616951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50878325435058294871077967 76317488152587442306616951)
      ·
        refine ⟨114476232228881163459925427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76317488152587442306616951 114476232228881163459925427)
        ·
          refine ⟨171714348343321745189888141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114476232228881163459925427 171714348343321745189888141)
          ·
            refine ⟨64392880628745654446208053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171714348343321745189888141 64392880628745654446208053)
            ·
              refine ⟨6036832558944905104332005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64392880628745654446208053 6036832558944905104332005)
              ·
                refine ⟨1131906104802169707062251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6036832558944905104332005 1131906104802169707062251)
                ·
                  refine ⟨1697859157203254560593377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131906104802169707062251 1697859157203254560593377)
                  ·
                    refine ⟨1273394367902440920445033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1697859157203254560593377 1273394367902440920445033)
                    ·
                      refine ⟨955045775926830690333775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273394367902440920445033 955045775926830690333775)
                      ·
                        rfl

theorem cell23_1859945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 2, 2].length) (baseStart_1859945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859945 prefixEnd_1859945 := by exact prefixLift 1859945
  have htrace : WordTrace (prefixWord ++ tailWord_1859945) baseStart_1859945 baseEnd_1859945 := by
    simpa [prefixWord, tailWord_1859945, baseEnd_1859945] using wordTrace_append hprefix tailTrace_1859945
  have hstable : (prefixWord ++ tailWord_1859945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859945).length < 2 ^ (prefixWord ++ tailWord_1859945).sum := by decide
  have hdescent : baseEnd_1859945 < baseStart_1859945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859961 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 3]
def baseStart_1859961 : Nat := 118140960795 + 1859961 * 2 ^ 59
def prefixEnd_1859961 : Nat := 4983230072969 + 3 ^ 40 * 1859961 * 2
def baseEnd_1859961 : Nat := 955053991617302627733701

theorem tailTrace_1859961 : CollatzResearch.WordTrace tailWord_1859961 prefixEnd_1859961 955053991617302627733701 := by
  unfold tailWord_1859961
  simp only [CollatzResearch.WordTrace]
  refine ⟨67838350814686427894019737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45225567209790951929346491 67838350814686427894019737)
  ·
    refine ⟨50878763111014820920514803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67838350814686427894019737 50878763111014820920514803)
    ·
      refine ⟨76318144666522231380772205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50878763111014820920514803 76318144666522231380772205)
      ·
        refine ⟨28619304249945836767789577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76318144666522231380772205 28619304249945836767789577)
        ·
          refine ⟨21464478187459377575842183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28619304249945836767789577 21464478187459377575842183)
          ·
            refine ⟨32196717281189066363763275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21464478187459377575842183 32196717281189066363763275)
            ·
              refine ⟨48295075921783599545644913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32196717281189066363763275 48295075921783599545644913)
              ·
                refine ⟨36221306941337699659233685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48295075921783599545644913 36221306941337699659233685)
                ·
                  refine ⟨1697873762875204671526579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36221306941337699659233685 1697873762875204671526579)
                  ·
                    refine ⟨2546810644312807007289869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1697873762875204671526579 2546810644312807007289869)
                    ·
                      refine ⟨955053991617302627733701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2546810644312807007289869 955053991617302627733701)
                      ·
                        rfl

theorem cell23_1859961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_1859961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859961 prefixEnd_1859961 := by exact prefixLift 1859961
  have htrace : WordTrace (prefixWord ++ tailWord_1859961) baseStart_1859961 baseEnd_1859961 := by
    simpa [prefixWord, tailWord_1859961, baseEnd_1859961] using wordTrace_append hprefix tailTrace_1859961
  have hstable : (prefixWord ++ tailWord_1859961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859961).length < 2 ^ (prefixWord ++ tailWord_1859961).sum := by decide
  have hdescent : baseEnd_1859961 < baseStart_1859961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859982 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1859982 : Nat := 118140960795 + 1859982 * 2 ^ 59
def prefixEnd_1859982 : Nat := 4983230072969 + 3 ^ 40 * 1859982 * 2
def baseEnd_1859982 : Nat := 955064774711047045571105

theorem tailTrace_1859982 : CollatzResearch.WordTrace tailWord_1859982 prefixEnd_1859982 955064774711047045571105 := by
  unfold tailWord_1859982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8479889593451293560066775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45226077831740232320356133 8479889593451293560066775)
  ·
    refine ⟨12719834390176940340100163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8479889593451293560066775 12719834390176940340100163)
    ·
      refine ⟨19079751585265410510150245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12719834390176940340100163 19079751585265410510150245)
      ·
        refine ⟨3577453422237264470653171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19079751585265410510150245 3577453422237264470653171)
        ·
          refine ⟨5366180133355896705979757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577453422237264470653171 5366180133355896705979757)
          ·
            refine ⟨2012317550008461264742409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5366180133355896705979757 2012317550008461264742409)
            ·
              refine ⟨1509238162506345948556807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012317550008461264742409 1509238162506345948556807)
              ·
                refine ⟨2263857243759518922835211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509238162506345948556807 2263857243759518922835211)
                ·
                  refine ⟨3395785865639278384252817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263857243759518922835211 3395785865639278384252817)
                  ·
                    refine ⟨2546839399229458788189613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3395785865639278384252817 2546839399229458788189613)
                    ·
                      refine ⟨955064774711047045571105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2546839399229458788189613 955064774711047045571105)
                      ·
                        rfl

theorem cell23_1859982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1859982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1859982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1859982 prefixEnd_1859982 := by exact prefixLift 1859982
  have htrace : WordTrace (prefixWord ++ tailWord_1859982) baseStart_1859982 baseEnd_1859982 := by
    simpa [prefixWord, tailWord_1859982, baseEnd_1859982] using wordTrace_append hprefix tailTrace_1859982
  have hstable : (prefixWord ++ tailWord_1859982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859982).length < 2 ^ (prefixWord ++ tailWord_1859982).sum := by decide
  have hdescent : baseEnd_1859982 < baseStart_1859982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860071 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 4, 5]
def baseStart_1860071 : Nat := 118140960795 + 1860071 * 2 ^ 59
def prefixEnd_1860071 : Nat := 4983230072969 + 3 ^ 40 * 1860071 * 2
def baseEnd_1860071 : Nat := 318370158163099065786065

theorem tailTrace_1860071 : CollatzResearch.WordTrace tailWord_1860071 prefixEnd_1860071 318370158163099065786065 := by
  unfold tailWord_1860071
  simp only [CollatzResearch.WordTrace]
  refine ⟨67842362844287916680524067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45228241896191944453682711 67842362844287916680524067)
  ·
    refine ⟨101763544266431875020786101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67842362844287916680524067 101763544266431875020786101)
    ·
      refine ⟨9540332274977988283198697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101763544266431875020786101 9540332274977988283198697)
      ·
        refine ⟨7155249206233491212399023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9540332274977988283198697 7155249206233491212399023)
        ·
          refine ⟨10732873809350236818598535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155249206233491212399023 10732873809350236818598535)
          ·
            refine ⟨16099310714025355227897803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732873809350236818598535 16099310714025355227897803)
            ·
              refine ⟨24148966071038032841846705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16099310714025355227897803 24148966071038032841846705)
              ·
                refine ⟨18111724553278524631385029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24148966071038032841846705 18111724553278524631385029)
                ·
                  refine ⟨3395948353739723368384693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18111724553278524631385029 3395948353739723368384693)
                  ·
                    refine ⟨318370158163099065786065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3395948353739723368384693 318370158163099065786065)
                    ·
                      rfl

theorem cell23_1860071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_1860071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860071 prefixEnd_1860071 := by exact prefixLift 1860071
  have htrace : WordTrace (prefixWord ++ tailWord_1860071) baseStart_1860071 baseEnd_1860071 := by
    simpa [prefixWord, tailWord_1860071, baseEnd_1860071] using wordTrace_append hprefix tailTrace_1860071
  have hstable : (prefixWord ++ tailWord_1860071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860071).length < 2 ^ (prefixWord ++ tailWord_1860071).sum := by decide
  have hdescent : baseEnd_1860071 < baseStart_1860071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860108 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1860108 : Nat := 118140960795 + 1860108 * 2 ^ 59
def prefixEnd_1860108 : Nat := 4983230072969 + 3 ^ 40 * 1860108 * 2
def baseEnd_1860108 : Nat := 955129473273513552595525

theorem tailTrace_1860108 : CollatzResearch.WordTrace tailWord_1860108 prefixEnd_1860108 955129473273513552595525 := by
  unfold tailWord_1860108
  simp only [CollatzResearch.WordTrace]
  refine ⟨33921856172576935999810489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45229141563435914666413985 33921856172576935999810489)
  ·
    refine ⟨25441392129432701999857867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33921856172576935999810489 25441392129432701999857867)
    ·
      refine ⟨38162088194149052999786801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25441392129432701999857867 38162088194149052999786801)
      ·
        refine ⟨28621566145611789749840101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38162088194149052999786801 28621566145611789749840101)
        ·
          refine ⟨5366543652302210578095019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28621566145611789749840101 5366543652302210578095019)
          ·
            refine ⟨8049815478453315867142529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366543652302210578095019 8049815478453315867142529)
            ·
              refine ⟨6037361608839986900356897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8049815478453315867142529 6037361608839986900356897)
              ·
                refine ⟨4528021206629990175267673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6037361608839986900356897 4528021206629990175267673)
                ·
                  refine ⟨3396015904972492631450755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4528021206629990175267673 3396015904972492631450755)
                  ·
                    refine ⟨5094023857458738947176133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3396015904972492631450755 5094023857458738947176133)
                    ·
                      refine ⟨955129473273513552595525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5094023857458738947176133 955129473273513552595525)
                      ·
                        rfl

theorem cell23_1860108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1860108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860108 prefixEnd_1860108 := by exact prefixLift 1860108
  have htrace : WordTrace (prefixWord ++ tailWord_1860108) baseStart_1860108 baseEnd_1860108 := by
    simpa [prefixWord, tailWord_1860108, baseEnd_1860108] using wordTrace_append hprefix tailTrace_1860108
  have hstable : (prefixWord ++ tailWord_1860108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860108).length < 2 ^ (prefixWord ++ tailWord_1860108).sum := by decide
  have hdescent : baseEnd_1860108 < baseStart_1860108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860109 : List Nat := [1, 7, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1860109 : Nat := 118140960795 + 1860109 * 2 ^ 59
def prefixEnd_1860109 : Nat := 4983230072969 + 3 ^ 40 * 1860109 * 2
def baseEnd_1860109 : Nat := 106125554083796449853669

theorem tailTrace_1860109 : CollatzResearch.WordTrace tailWord_1860109 prefixEnd_1860109 106125554083796449853669 := by
  unfold tailWord_1860109
  simp only [CollatzResearch.WordTrace]
  refine ⟨67843748818150249170407381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45229165878766832780271587 67843748818150249170407381)
  ·
    refine ⟨1590087862925396464931423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 67843748818150249170407381 1590087862925396464931423)
    ·
      refine ⟨2385131794388094697397135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1590087862925396464931423 2385131794388094697397135)
      ·
        refine ⟨3577697691582142046095703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385131794388094697397135 3577697691582142046095703)
        ·
          refine ⟨5366546537373213069143555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577697691582142046095703 5366546537373213069143555)
          ·
            refine ⟨8049819806059819603715333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366546537373213069143555 8049819806059819603715333)
            ·
              refine ⟨1509341213636216175696625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8049819806059819603715333 1509341213636216175696625)
              ·
                refine ⟨1132005910227162131772469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509341213636216175696625 1132005910227162131772469)
                ·
                  refine ⟨106125554083796449853669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1132005910227162131772469 106125554083796449853669)
                  ·
                    rfl

theorem cell23_1860109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1860109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860109 prefixEnd_1860109 := by exact prefixLift 1860109
  have htrace : WordTrace (prefixWord ++ tailWord_1860109) baseStart_1860109 baseEnd_1860109 := by
    simpa [prefixWord, tailWord_1860109, baseEnd_1860109] using wordTrace_append hprefix tailTrace_1860109
  have hstable : (prefixWord ++ tailWord_1860109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860109).length < 2 ^ (prefixWord ++ tailWord_1860109).sum := by decide
  have hdescent : baseEnd_1860109 < baseStart_1860109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860125 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_1860125 : Nat := 118140960795 + 1860125 * 2 ^ 59
def prefixEnd_1860125 : Nat := 4983230072969 + 3 ^ 40 * 1860125 * 2
def baseEnd_1860125 : Nat := 955138202444639986082947

theorem tailTrace_1860125 : CollatzResearch.WordTrace tailWord_1860125 prefixEnd_1860125 955138202444639986082947 := by
  unfold tailWord_1860125
  simp only [CollatzResearch.WordTrace]
  refine ⟨67844332386092283902989829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45229554924061522601993219 67844332386092283902989829)
  ·
    refine ⟨12720812322392303231810593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67844332386092283902989829 12720812322392303231810593)
    ·
      refine ⟨9540609241794227423857945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12720812322392303231810593 9540609241794227423857945)
      ·
        refine ⟨7155456931345670567893459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9540609241794227423857945 7155456931345670567893459)
        ·
          refine ⟨10733185397018505851840189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155456931345670567893459 10733185397018505851840189)
          ·
            refine ⟨4024944523881939694440071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10733185397018505851840189 4024944523881939694440071)
            ·
              refine ⟨6037416785822909541660107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024944523881939694440071 6037416785822909541660107)
              ·
                refine ⟨9056125178734364312490161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037416785822909541660107 9056125178734364312490161)
                ·
                  refine ⟨6792093884050773234367621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9056125178734364312490161 6792093884050773234367621)
                  ·
                    refine ⟨1273517603259519981443929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6792093884050773234367621 1273517603259519981443929)
                    ·
                      refine ⟨955138202444639986082947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273517603259519981443929 955138202444639986082947)
                      ·
                        rfl

theorem cell23_1860125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_1860125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860125 prefixEnd_1860125 := by exact prefixLift 1860125
  have htrace : WordTrace (prefixWord ++ tailWord_1860125) baseStart_1860125 baseEnd_1860125 := by
    simpa [prefixWord, tailWord_1860125, baseEnd_1860125] using wordTrace_append hprefix tailTrace_1860125
  have hstable : (prefixWord ++ tailWord_1860125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860125).length < 2 ^ (prefixWord ++ tailWord_1860125).sum := by decide
  have hdescent : baseEnd_1860125 < baseStart_1860125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860142 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1860142 : Nat := 118140960795 + 1860142 * 2 ^ 59
def prefixEnd_1860142 : Nat := 4983230072969 + 3 ^ 40 * 1860142 * 2
def baseEnd_1860142 : Nat := 955146931615766419570369

theorem tailTrace_1860142 : CollatzResearch.WordTrace tailWord_1860142 prefixEnd_1860142 955146931615766419570369 := by
  unfold tailWord_1860142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8480619053378836975794835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45229968284687130537572453 8480619053378836975794835)
  ·
    refine ⟨12720928580068255463692253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8480619053378836975794835 12720928580068255463692253)
    ·
      refine ⟨4770348217525595798884595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12720928580068255463692253 4770348217525595798884595)
      ·
        refine ⟨7155522326288393698326893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770348217525595798884595 7155522326288393698326893)
        ·
          refine ⟨2683320872358147636872585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7155522326288393698326893 2683320872358147636872585)
          ·
            refine ⟨2012490654268610727654439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683320872358147636872585 2012490654268610727654439)
            ·
              refine ⟨3018735981402916091481659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012490654268610727654439 3018735981402916091481659)
              ·
                refine ⟨4528103972104374137222489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018735981402916091481659 4528103972104374137222489)
                ·
                  refine ⟨3396077979078280602916867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4528103972104374137222489 3396077979078280602916867)
                  ·
                    refine ⟨5094116968617420904375301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3396077979078280602916867 5094116968617420904375301)
                    ·
                      refine ⟨955146931615766419570369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5094116968617420904375301 955146931615766419570369)
                      ·
                        rfl

theorem cell23_1860142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1860142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860142 prefixEnd_1860142 := by exact prefixLift 1860142
  have htrace : WordTrace (prefixWord ++ tailWord_1860142) baseStart_1860142 baseEnd_1860142 := by
    simpa [prefixWord, tailWord_1860142, baseEnd_1860142] using wordTrace_append hprefix tailTrace_1860142
  have hstable : (prefixWord ++ tailWord_1860142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860142).length < 2 ^ (prefixWord ++ tailWord_1860142).sum := by decide
  have hdescent : baseEnd_1860142 < baseStart_1860142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860201 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_1860201 : Nat := 118140960795 + 1860201 * 2 ^ 59
def prefixEnd_1860201 : Nat := 4983230072969 + 3 ^ 40 * 1860201 * 2
def baseEnd_1860201 : Nat := 955177226974381688732597

theorem tailTrace_1860201 : CollatzResearch.WordTrace tailWord_1860201 prefixEnd_1860201 955177226974381688732597 := by
  unfold tailWord_1860201
  simp only [CollatzResearch.WordTrace]
  refine ⟨67847104333816948882756457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45231402889211299255170971 67847104333816948882756457)
  ·
    refine ⟨50885328250362711662067343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67847104333816948882756457 50885328250362711662067343)
    ·
      refine ⟨76327992375544067493101015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50885328250362711662067343 76327992375544067493101015)
      ·
        refine ⟨114491988563316101239651523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76327992375544067493101015 114491988563316101239651523)
        ·
          refine ⟨171737982844974151859477285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114491988563316101239651523 171737982844974151859477285)
          ·
            refine ⟨32200871783432653473651991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171737982844974151859477285 32200871783432653473651991)
            ·
              refine ⟨48301307675148980210477987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32200871783432653473651991 48301307675148980210477987)
              ·
                refine ⟨72451961512723470315716981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48301307675148980210477987 72451961512723470315716981)
                ·
                  refine ⟨6792371391817825342098467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72451961512723470315716981 6792371391817825342098467)
                  ·
                    refine ⟨10188557087726738013147701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6792371391817825342098467 10188557087726738013147701)
                    ·
                      refine ⟨955177226974381688732597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10188557087726738013147701 955177226974381688732597)
                      ·
                        rfl

theorem cell23_1860201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_1860201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860201 prefixEnd_1860201 := by exact prefixLift 1860201
  have htrace : WordTrace (prefixWord ++ tailWord_1860201) baseStart_1860201 baseEnd_1860201 := by
    simpa [prefixWord, tailWord_1860201, baseEnd_1860201] using wordTrace_append hprefix tailTrace_1860201
  have hstable : (prefixWord ++ tailWord_1860201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860201).length < 2 ^ (prefixWord ++ tailWord_1860201).sum := by decide
  have hdescent : baseEnd_1860201 < baseStart_1860201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860215 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 5, 2, 2]
def baseStart_1860215 : Nat := 118140960795 + 1860215 * 2 ^ 59
def prefixEnd_1860215 : Nat := 4983230072969 + 3 ^ 40 * 1860215 * 2
def baseEnd_1860215 : Nat := 955184415703544633957533

theorem tailTrace_1860215 : CollatzResearch.WordTrace tailWord_1860215 prefixEnd_1860215 955184415703544633957533 := by
  unfold tailWord_1860215
  simp only [CollatzResearch.WordTrace]
  refine ⟨67847614955766229273766099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45231743303844152849177399 67847614955766229273766099)
  ·
    refine ⟨101771422433649343910649149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67847614955766229273766099 101771422433649343910649149)
    ·
      refine ⟨38164283412618503966493431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101771422433649343910649149 38164283412618503966493431)
      ·
        refine ⟨57246425118927755949740147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38164283412618503966493431 57246425118927755949740147)
        ·
          refine ⟨85869637678391633924610221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57246425118927755949740147 85869637678391633924610221)
          ·
            refine ⟨32201114129396862721728833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85869637678391633924610221 32201114129396862721728833)
            ·
              refine ⟨24150835597047647041296625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32201114129396862721728833 24150835597047647041296625)
              ·
                refine ⟨18113126697785735280972469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24150835597047647041296625 18113126697785735280972469)
                ·
                  refine ⟨1698105627917412682591169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18113126697785735280972469 1698105627917412682591169)
                  ·
                    refine ⟨1273579220938059511943377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1698105627917412682591169 1273579220938059511943377)
                    ·
                      refine ⟨955184415703544633957533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273579220938059511943377 955184415703544633957533)
                      ·
                        rfl

theorem cell23_1860215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_1860215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860215 prefixEnd_1860215 := by exact prefixLift 1860215
  have htrace : WordTrace (prefixWord ++ tailWord_1860215) baseStart_1860215 baseEnd_1860215 := by
    simpa [prefixWord, tailWord_1860215, baseEnd_1860215] using wordTrace_append hprefix tailTrace_1860215
  have hstable : (prefixWord ++ tailWord_1860215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860215).length < 2 ^ (prefixWord ++ tailWord_1860215).sum := by decide
  have hdescent : baseEnd_1860215 < baseStart_1860215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860225 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1860225 : Nat := 118140960795 + 1860225 * 2 ^ 59
def prefixEnd_1860225 : Nat := 4983230072969 + 3 ^ 40 * 1860225 * 2
def baseEnd_1860225 : Nat := 318396516836696531610829

theorem tailTrace_1860225 : CollatzResearch.WordTrace tailWord_1860225 prefixEnd_1860225 318396516836696531610829 := by
  unfold tailWord_1860225
  simp only [CollatzResearch.WordTrace]
  refine ⟨67847979685730000981630129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45231986457153333987753419 67847979685730000981630129)
  ·
    refine ⟨50885984764297500736222597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67847979685730000981630129 50885984764297500736222597)
    ·
      refine ⟨9541122143305781388041737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50885984764297500736222597 9541122143305781388041737)
      ·
        refine ⟨7155841607479336041031303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9541122143305781388041737 7155841607479336041031303)
        ·
          refine ⟨10733762411219004061546955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155841607479336041031303 10733762411219004061546955)
          ·
            refine ⟨16100643616828506092320433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10733762411219004061546955 16100643616828506092320433)
            ·
              refine ⟨12075482712621379569240325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16100643616828506092320433 12075482712621379569240325)
              ·
                refine ⟨2264153008616508669232561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12075482712621379569240325 2264153008616508669232561)
                ·
                  refine ⟨1698114756462381501924421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2264153008616508669232561 1698114756462381501924421)
                  ·
                    refine ⟨318396516836696531610829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698114756462381501924421 318396516836696531610829)
                    ·
                      rfl

theorem cell23_1860225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1860225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860225 prefixEnd_1860225 := by exact prefixLift 1860225
  have htrace : WordTrace (prefixWord ++ tailWord_1860225) baseStart_1860225 baseEnd_1860225 := by
    simpa [prefixWord, tailWord_1860225, baseEnd_1860225] using wordTrace_append hprefix tailTrace_1860225
  have hstable : (prefixWord ++ tailWord_1860225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860225).length < 2 ^ (prefixWord ++ tailWord_1860225).sum := by decide
  have hdescent : baseEnd_1860225 < baseStart_1860225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860228 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1860228 : Nat := 118140960795 + 1860228 * 2 ^ 59
def prefixEnd_1860228 : Nat := 4983230072969 + 3 ^ 40 * 1860228 * 2
def baseEnd_1860228 : Nat := 955191090952053083094973

theorem tailTrace_1860228 : CollatzResearch.WordTrace tailWord_1860228 prefixEnd_1860228 955191090952053083094973 := by
  unfold tailWord_1860228
  simp only [CollatzResearch.WordTrace]
  refine ⟨33924044552359566246994669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45232059403146088329326225 33924044552359566246994669)
  ·
    refine ⟨12721516707134837342623001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33924044552359566246994669 12721516707134837342623001)
    ·
      refine ⟨9541137530351128006967251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12721516707134837342623001 9541137530351128006967251)
      ·
        refine ⟨14311706295526692010450877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9541137530351128006967251 14311706295526692010450877)
        ·
          refine ⟨5366889860822509503919079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14311706295526692010450877 5366889860822509503919079)
          ·
            refine ⟨8050334791233764255878619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366889860822509503919079 8050334791233764255878619)
            ·
              refine ⟨12075502186850646383817929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8050334791233764255878619 12075502186850646383817929)
              ·
                refine ⟨9056626640137984787863447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12075502186850646383817929 9056626640137984787863447)
                ·
                  refine ⟨13584939960206977181795171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056626640137984787863447 13584939960206977181795171)
                  ·
                    refine ⟨20377409940310465772692757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13584939960206977181795171 20377409940310465772692757)
                    ·
                      refine ⟨955191090952053083094973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20377409940310465772692757 955191090952053083094973)
                      ·
                        rfl

theorem cell23_1860228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1860228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860228 prefixEnd_1860228 := by exact prefixLift 1860228
  have htrace : WordTrace (prefixWord ++ tailWord_1860228) baseStart_1860228 baseEnd_1860228 := by
    simpa [prefixWord, tailWord_1860228, baseEnd_1860228] using wordTrace_append hprefix tailTrace_1860228
  have hstable : (prefixWord ++ tailWord_1860228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860228).length < 2 ^ (prefixWord ++ tailWord_1860228).sum := by decide
  have hdescent : baseEnd_1860228 < baseStart_1860228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860238 : List Nat := [4, 1, 1, 3, 1, 1, 4, 8]
def baseStart_1860238 : Nat := 118140960795 + 1860238 * 2 ^ 59
def prefixEnd_1860238 : Nat := 4983230072969 + 3 ^ 40 * 1860238 * 2
def baseEnd_1860238 : Nat := 35377637991059186813701

theorem tailTrace_1860238 : CollatzResearch.WordTrace tailWord_1860238 prefixEnd_1860238 35377637991059186813701 := by
  unfold tailWord_1860238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8481056729335363025231671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45232302556455269467902245 8481056729335363025231671)
  ·
    refine ⟨12721585094003044537847507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8481056729335363025231671 12721585094003044537847507)
    ·
      refine ⟨19082377641004566806771261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12721585094003044537847507 19082377641004566806771261)
      ·
        refine ⟨7155891615376712552539223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19082377641004566806771261 7155891615376712552539223)
        ·
          refine ⟨10733837423065068828808835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155891615376712552539223 10733837423065068828808835)
          ·
            refine ⟨16100756134597603243213253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10733837423065068828808835 16100756134597603243213253)
            ·
              refine ⟨3018891775237050608102485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16100756134597603243213253 3018891775237050608102485)
              ·
                refine ⟨35377637991059186813701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3018891775237050608102485 35377637991059186813701)
                ·
                  rfl

theorem cell23_1860238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_1860238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860238 prefixEnd_1860238 := by exact prefixLift 1860238
  have htrace : WordTrace (prefixWord ++ tailWord_1860238) baseStart_1860238 baseEnd_1860238 := by
    simpa [prefixWord, tailWord_1860238, baseEnd_1860238] using wordTrace_append hprefix tailTrace_1860238
  have hstable : (prefixWord ++ tailWord_1860238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860238).length < 2 ^ (prefixWord ++ tailWord_1860238).sum := by decide
  have hdescent : baseEnd_1860238 < baseStart_1860238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860242 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1860242 : Nat := 118140960795 + 1860242 * 2 ^ 59
def prefixEnd_1860242 : Nat := 4983230072969 + 3 ^ 40 * 1860242 * 2
def baseEnd_1860242 : Nat := 318399426560405342773303

theorem tailTrace_1860242 : CollatzResearch.WordTrace tailWord_1860242 prefixEnd_1860242 318399426560405342773303 := by
  unfold tailWord_1860242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16962149931667103221249745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45232399817778941923332653 16962149931667103221249745)
  ·
    refine ⟨12721612448750327415937309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16962149931667103221249745 12721612448750327415937309)
    ·
      refine ⟨4770604668281372780976491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12721612448750327415937309 4770604668281372780976491)
      ·
        refine ⟨7155907002422059171464737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770604668281372780976491 7155907002422059171464737)
        ·
          refine ⟨5366930251816544378598553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7155907002422059171464737 5366930251816544378598553)
          ·
            refine ⟨4025197688862408283948915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5366930251816544378598553 4025197688862408283948915)
            ·
              refine ⟨6037796533293612425923373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4025197688862408283948915 6037796533293612425923373)
              ·
                refine ⟨2264173699985104659721265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6037796533293612425923373 2264173699985104659721265)
                ·
                  refine ⟨1698130274988828494790949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2264173699985104659721265 1698130274988828494790949)
                  ·
                    refine ⟨318399426560405342773303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698130274988828494790949 318399426560405342773303)
                    ·
                      rfl

theorem cell23_1860242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1860242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860242 prefixEnd_1860242 := by exact prefixLift 1860242
  have htrace : WordTrace (prefixWord ++ tailWord_1860242) baseStart_1860242 baseEnd_1860242 := by
    simpa [prefixWord, tailWord_1860242, baseEnd_1860242] using wordTrace_append hprefix tailTrace_1860242
  have hstable : (prefixWord ++ tailWord_1860242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860242).length < 2 ^ (prefixWord ++ tailWord_1860242).sum := by decide
  have hdescent : baseEnd_1860242 < baseStart_1860242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860252 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1860252 : Nat := 118140960795 + 1860252 * 2 ^ 59
def prefixEnd_1860252 : Nat := 4983230072969 + 3 ^ 40 * 1860252 * 2
def baseEnd_1860252 : Nat := 955203414487760989194863

theorem tailTrace_1860252 : CollatzResearch.WordTrace tailWord_1860252 prefixEnd_1860252 955203414487760989194863 := by
  unfold tailWord_1860252
  simp only [CollatzResearch.WordTrace]
  refine ⟨33924482228316092296431505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45232642971088123061908673 33924482228316092296431505)
  ·
    refine ⟨25443361671237069222323629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33924482228316092296431505 25443361671237069222323629)
    ·
      refine ⟨9541260626713900958371361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25443361671237069222323629 9541260626713900958371361)
      ·
        refine ⟨7155945470035425718778521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9541260626713900958371361 7155945470035425718778521)
        ·
          refine ⟨5366959102526569289083891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7155945470035425718778521 5366959102526569289083891)
          ·
            refine ⟨8050438653789853933625837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366959102526569289083891 8050438653789853933625837)
            ·
              refine ⟨3018914495171195225109689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8050438653789853933625837 3018914495171195225109689)
              ·
                refine ⟨2264185871378396418832267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018914495171195225109689 2264185871378396418832267)
                ·
                  refine ⟨3396278807067594628248401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264185871378396418832267 3396278807067594628248401)
                  ·
                    refine ⟨2547209105300695971186301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3396278807067594628248401 2547209105300695971186301)
                    ·
                      refine ⟨955203414487760989194863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2547209105300695971186301 955203414487760989194863)
                      ·
                        rfl

theorem cell23_1860252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1860252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860252 prefixEnd_1860252 := by exact prefixLift 1860252
  have htrace : WordTrace (prefixWord ++ tailWord_1860252) baseStart_1860252 baseEnd_1860252 := by
    simpa [prefixWord, tailWord_1860252, baseEnd_1860252] using wordTrace_append hprefix tailTrace_1860252
  have hstable : (prefixWord ++ tailWord_1860252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860252).length < 2 ^ (prefixWord ++ tailWord_1860252).sum := by decide
  have hdescent : baseEnd_1860252 < baseStart_1860252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860266 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1860266 : Nat := 118140960795 + 1860266 * 2 ^ 59
def prefixEnd_1860266 : Nat := 4983230072969 + 3 ^ 40 * 1860266 * 2
def baseEnd_1860266 : Nat := 955210603216923934419799

theorem tailTrace_1860266 : CollatzResearch.WordTrace tailWord_1860266 prefixEnd_1860266 955210603216923934419799 := by
  unfold tailWord_1860266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16962368769645366245968163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45232983385720976655915101 16962368769645366245968163)
  ·
    refine ⟨25443553154468049368952245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16962368769645366245968163 25443553154468049368952245)
    ·
      refine ⟨2385333108231379628339273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25443553154468049368952245 2385333108231379628339273)
      ·
        refine ⟨1788999831173534721254455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2385333108231379628339273 1788999831173534721254455)
        ·
          refine ⟨2683499746760302081881683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788999831173534721254455 2683499746760302081881683)
          ·
            refine ⟨4025249620140453122822525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683499746760302081881683 4025249620140453122822525)
            ·
              refine ⟨1509468607552669921058447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4025249620140453122822525 1509468607552669921058447)
              ·
                refine ⟨2264202911329004881587671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509468607552669921058447 2264202911329004881587671)
                ·
                  refine ⟨3396304366993507322381507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264202911329004881587671 3396304366993507322381507)
                  ·
                    refine ⟨5094456550490260983572261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3396304366993507322381507 5094456550490260983572261)
                    ·
                      refine ⟨955210603216923934419799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5094456550490260983572261 955210603216923934419799)
                      ·
                        rfl

theorem cell23_1860266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1860266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860266 prefixEnd_1860266 := by exact prefixLift 1860266
  have htrace : WordTrace (prefixWord ++ tailWord_1860266) baseStart_1860266 baseEnd_1860266 := by
    simpa [prefixWord, tailWord_1860266, baseEnd_1860266] using wordTrace_append hprefix tailTrace_1860266
  have hstable : (prefixWord ++ tailWord_1860266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860266).length < 2 ^ (prefixWord ++ tailWord_1860266).sum := by decide
  have hdescent : baseEnd_1860266 < baseStart_1860266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860269 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_1860269 : Nat := 118140960795 + 1860269 * 2 ^ 59
def prefixEnd_1860269 : Nat := 4983230072969 + 3 ^ 40 * 1860269 * 2
def baseEnd_1860269 : Nat := 955212143658887422682285

theorem tailTrace_1860269 : CollatzResearch.WordTrace tailWord_1860269 prefixEnd_1860269 955212143658887422682285 := by
  unfold tailWord_1860269
  simp only [CollatzResearch.WordTrace]
  refine ⟨67849584497570596496231861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45233056331713730997487907 67849584497570596496231861)
  ·
    refine ⟨6360898546647243421521737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67849584497570596496231861 6360898546647243421521737)
    ·
      refine ⟨4770673909985432566141303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6360898546647243421521737 4770673909985432566141303)
      ·
        refine ⟨7156010864978148849211955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770673909985432566141303 7156010864978148849211955)
        ·
          refine ⟨10734016297467223273817933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156010864978148849211955 10734016297467223273817933)
          ·
            refine ⟨4025256111550208727681725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10734016297467223273817933 4025256111550208727681725)
            ·
              refine ⟨1509471041831328272880647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4025256111550208727681725 1509471041831328272880647)
              ·
                refine ⟨2264206562746992409320971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509471041831328272880647 2264206562746992409320971)
                ·
                  refine ⟨3396309844120488613981457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264206562746992409320971 3396309844120488613981457)
                  ·
                    refine ⟨2547232383090366460486093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3396309844120488613981457 2547232383090366460486093)
                    ·
                      refine ⟨955212143658887422682285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2547232383090366460486093 955212143658887422682285)
                      ·
                        rfl

theorem cell23_1860269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_1860269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860269 prefixEnd_1860269 := by exact prefixLift 1860269
  have htrace : WordTrace (prefixWord ++ tailWord_1860269) baseStart_1860269 baseEnd_1860269 := by
    simpa [prefixWord, tailWord_1860269, baseEnd_1860269] using wordTrace_append hprefix tailTrace_1860269
  have hstable : (prefixWord ++ tailWord_1860269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860269).length < 2 ^ (prefixWord ++ tailWord_1860269).sum := by decide
  have hdescent : baseEnd_1860269 < baseStart_1860269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860282 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_1860282 : Nat := 118140960795 + 1860282 * 2 ^ 59
def prefixEnd_1860282 : Nat := 4983230072969 + 3 ^ 40 * 1860282 * 2
def baseEnd_1860282 : Nat := 955218818907395871819725

theorem tailTrace_1860282 : CollatzResearch.WordTrace tailWord_1860282 prefixEnd_1860282 955218818907395871819725 := by
  unfold tailWord_1860282
  simp only [CollatzResearch.WordTrace]
  refine ⟨16962514661630874929113775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45233372431015666477636733 16962514661630874929113775)
  ·
    refine ⟨25443771992446312393670663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16962514661630874929113775 25443771992446312393670663)
    ·
      refine ⟨38165657988669468590505995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25443771992446312393670663 38165657988669468590505995)
      ·
        refine ⟨57248486983004202885758993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38165657988669468590505995 57248486983004202885758993)
        ·
          refine ⟨42936365237253152164319245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57248486983004202885758993 42936365237253152164319245)
          ·
            refine ⟨16101136963969932061619717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42936365237253152164319245 16101136963969932061619717)
            ·
              refine ⟨3018963180744362261553697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16101136963969932061619717 3018963180744362261553697)
              ·
                refine ⟨2264222385558271696165273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018963180744362261553697 2264222385558271696165273)
                ·
                  refine ⟨1698166789168703772123955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2264222385558271696165273 1698166789168703772123955)
                  ·
                    refine ⟨2547250183753055658185933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1698166789168703772123955 2547250183753055658185933)
                    ·
                      refine ⟨955218818907395871819725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2547250183753055658185933 955218818907395871819725)
                      ·
                        rfl

theorem cell23_1860282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_1860282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860282 prefixEnd_1860282 := by exact prefixLift 1860282
  have htrace : WordTrace (prefixWord ++ tailWord_1860282) baseStart_1860282 baseEnd_1860282 := by
    simpa [prefixWord, tailWord_1860282, baseEnd_1860282] using wordTrace_append hprefix tailTrace_1860282
  have hstable : (prefixWord ++ tailWord_1860282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860282).length < 2 ^ (prefixWord ++ tailWord_1860282).sum := by decide
  have hdescent : baseEnd_1860282 < baseStart_1860282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860288 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1860288 : Nat := 118140960795 + 1860288 * 2 ^ 59
def prefixEnd_1860288 : Nat := 4983230072969 + 3 ^ 40 * 1860288 * 2
def baseEnd_1860288 : Nat := 955221899791322848344697

theorem tailTrace_1860288 : CollatzResearch.WordTrace tailWord_1860288 prefixEnd_1860288 955221899791322848344697 := by
  unfold tailWord_1860288
  simp only [CollatzResearch.WordTrace]
  refine ⟨33925138742250881370586759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45233518323001175160782345 33925138742250881370586759)
  ·
    refine ⟨50887708113376322055880139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33925138742250881370586759 50887708113376322055880139)
    ·
      refine ⟨76331562170064483083820209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50887708113376322055880139 76331562170064483083820209)
      ·
        refine ⟨57248671627548362312865157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76331562170064483083820209 57248671627548362312865157)
        ·
          refine ⟨10734125930165317933662217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57248671627548362312865157 10734125930165317933662217)
          ·
            refine ⟨8050594447623988450246663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10734125930165317933662217 8050594447623988450246663)
            ·
              refine ⟨12075891671435982675369995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8050594447623988450246663 12075891671435982675369995)
              ·
                refine ⟨18113837507153974013054993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12075891671435982675369995 18113837507153974013054993)
                ·
                  refine ⟨13585378130365480509791245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18113837507153974013054993 13585378130365480509791245)
                  ·
                    refine ⟨5094516798887055191171717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13585378130365480509791245 5094516798887055191171717)
                    ·
                      refine ⟨955221899791322848344697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5094516798887055191171717 955221899791322848344697)
                      ·
                        rfl

theorem cell23_1860288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1860288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860288 prefixEnd_1860288 := by exact prefixLift 1860288
  have htrace : WordTrace (prefixWord ++ tailWord_1860288) baseStart_1860288 baseEnd_1860288 := by
    simpa [prefixWord, tailWord_1860288, baseEnd_1860288] using wordTrace_append hprefix tailTrace_1860288
  have hstable : (prefixWord ++ tailWord_1860288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860288).length < 2 ^ (prefixWord ++ tailWord_1860288).sum := by decide
  have hdescent : baseEnd_1860288 < baseStart_1860288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860289 : List Nat := [1, 2, 6, 2, 2, 1, 1, 8]
def baseStart_1860289 : Nat := 118140960795 + 1860289 * 2 ^ 59
def prefixEnd_1860289 : Nat := 4983230072969 + 3 ^ 40 * 1860289 * 2
def baseEnd_1860289 : Nat := 35378607898962123867859

theorem tailTrace_1860289 : CollatzResearch.WordTrace tailWord_1860289 prefixEnd_1860289 35378607898962123867859 := by
  unfold tailWord_1860289
  simp only [CollatzResearch.WordTrace]
  refine ⟨67850313957498139911959921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45233542638332093274639947 67850313957498139911959921)
  ·
    refine ⟨50887735468123604933969941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67850313957498139911959921 50887735468123604933969941)
    ·
      refine ⟨2385362600068293981279841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50887735468123604933969941 2385362600068293981279841)
      ·
        refine ⟨1789021950051220485959881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2385362600068293981279841 1789021950051220485959881)
        ·
          refine ⟨1341766462538415364469911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789021950051220485959881 1341766462538415364469911)
          ·
            refine ⟨2012649693807623046704867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341766462538415364469911 2012649693807623046704867)
            ·
              refine ⟨3018974540711434570057301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012649693807623046704867 3018974540711434570057301)
              ·
                refine ⟨35378607898962123867859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3018974540711434570057301 35378607898962123867859)
                ·
                  rfl

theorem cell23_1860289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 8].length) (baseStart_1860289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860289 prefixEnd_1860289 := by exact prefixLift 1860289
  have htrace : WordTrace (prefixWord ++ tailWord_1860289) baseStart_1860289 baseEnd_1860289 := by
    simpa [prefixWord, tailWord_1860289, baseEnd_1860289] using wordTrace_append hprefix tailTrace_1860289
  have hstable : (prefixWord ++ tailWord_1860289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860289).length < 2 ^ (prefixWord ++ tailWord_1860289).sum := by decide
  have hdescent : baseEnd_1860289 < baseStart_1860289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860292 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_1860292 : Nat := 118140960795 + 1860292 * 2 ^ 59
def prefixEnd_1860292 : Nat := 4983230072969 + 3 ^ 40 * 1860292 * 2
def baseEnd_1860292 : Nat := 955223953713940832694679

theorem tailTrace_1860292 : CollatzResearch.WordTrace tailWord_1860292 prefixEnd_1860292 955223953713940832694679 := by
  unfold tailWord_1860292
  simp only [CollatzResearch.WordTrace]
  refine ⟨33925211688243635712159565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45233615584324847616212753 33925211688243635712159565)
  ·
    refine ⟨12721954383091363392059837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33925211688243635712159565 12721954383091363392059837)
    ·
      refine ⟨4770732893659261272022439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12721954383091363392059837 4770732893659261272022439)
      ·
        refine ⟨7156099340488891908033659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770732893659261272022439 7156099340488891908033659)
        ·
          refine ⟨10734149010733337862050489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156099340488891908033659 10734149010733337862050489)
          ·
            refine ⟨8050611758050003396537867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10734149010733337862050489 8050611758050003396537867)
            ·
              refine ⟨12075917637075005094806801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8050611758050003396537867 12075917637075005094806801)
              ·
                refine ⟨9056938227806253821105101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12075917637075005094806801 9056938227806253821105101)
                ·
                  refine ⟨3396351835427345182914413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9056938227806253821105101 3396351835427345182914413)
                  ·
                    refine ⟨1273631938285254443592905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396351835427345182914413 1273631938285254443592905)
                    ·
                      refine ⟨955223953713940832694679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273631938285254443592905 955223953713940832694679)
                      ·
                        rfl

theorem cell23_1860292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_1860292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860292 prefixEnd_1860292 := by exact prefixLift 1860292
  have htrace : WordTrace (prefixWord ++ tailWord_1860292) baseStart_1860292 baseEnd_1860292 := by
    simpa [prefixWord, tailWord_1860292, baseEnd_1860292] using wordTrace_append hprefix tailTrace_1860292
  have hstable : (prefixWord ++ tailWord_1860292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860292).length < 2 ^ (prefixWord ++ tailWord_1860292).sum := by decide
  have hdescent : baseEnd_1860292 < baseStart_1860292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860298 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_1860298 : Nat := 118140960795 + 1860298 * 2 ^ 59
def prefixEnd_1860298 : Nat := 4983230072969 + 3 ^ 40 * 1860298 * 2
def baseEnd_1860298 : Nat := 318409011532622603073217

theorem tailTrace_1860298 : CollatzResearch.WordTrace tailWord_1860298 prefixEnd_1860298 318409011532622603073217 := by
  unfold tailWord_1860298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16962660553616383612259387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45233761476310356299358365 16962660553616383612259387)
  ·
    refine ⟨25443990830424575418389081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16962660553616383612259387 25443990830424575418389081)
    ·
      refine ⟨19082993122818431563791811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25443990830424575418389081 19082993122818431563791811)
      ·
        refine ⟨28624489684227647345687717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19082993122818431563791811 28624489684227647345687717)
        ·
          refine ⟨5367091815792683877316447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28624489684227647345687717 5367091815792683877316447)
          ·
            refine ⟨8050637723689025815974671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367091815792683877316447 8050637723689025815974671)
            ·
              refine ⟨12075956585533538723962007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8050637723689025815974671 12075956585533538723962007)
              ·
                refine ⟨18113934878300308085943011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12075956585533538723962007 18113934878300308085943011)
                ·
                  refine ⟨27170902317450462128914517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18113934878300308085943011 27170902317450462128914517)
                  ·
                    refine ⟨318409011532622603073217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27170902317450462128914517 318409011532622603073217)
                    ·
                      rfl

theorem cell23_1860298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_1860298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860298 prefixEnd_1860298 := by exact prefixLift 1860298
  have htrace : WordTrace (prefixWord ++ tailWord_1860298) baseStart_1860298 baseEnd_1860298 := by
    simpa [prefixWord, tailWord_1860298, baseEnd_1860298] using wordTrace_append hprefix tailTrace_1860298
  have hstable : (prefixWord ++ tailWord_1860298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860298).length < 2 ^ (prefixWord ++ tailWord_1860298).sum := by decide
  have hdescent : baseEnd_1860298 < baseStart_1860298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860356 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_1860356 : Nat := 118140960795 + 1860356 * 2 ^ 59
def prefixEnd_1860356 : Nat := 4983230072969 + 3 ^ 40 * 1860356 * 2
def baseEnd_1860356 : Nat := 955256816475828582294385

theorem tailTrace_1860356 : CollatzResearch.WordTrace tailWord_1860356 prefixEnd_1860356 955256816475828582294385 := by
  unfold tailWord_1860356
  simp only [CollatzResearch.WordTrace]
  refine ⟨33926378824127705177324461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45235171765503606903099281 33926378824127705177324461)
  ·
    refine ⟨12722392059047889441496673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33926378824127705177324461 12722392059047889441496673)
    ·
      refine ⟨9541794044285917081122505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12722392059047889441496673 9541794044285917081122505)
      ·
        refine ⟨7156345533214437810841879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9541794044285917081122505 7156345533214437810841879)
        ·
          refine ⟨10734518299821656716262819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156345533214437810841879 10734518299821656716262819)
          ·
            refine ⟨16101777449732485074394229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10734518299821656716262819 16101777449732485074394229)
            ·
              refine ⟨1509541635912420475724459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16101777449732485074394229 1509541635912420475724459)
              ·
                refine ⟨2264312453868630713586689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509541635912420475724459 2264312453868630713586689)
                ·
                  refine ⟨1698234340401473035190017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2264312453868630713586689 1698234340401473035190017)
                  ·
                    refine ⟨1273675755301104776392513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1698234340401473035190017 1273675755301104776392513)
                    ·
                      refine ⟨955256816475828582294385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273675755301104776392513 955256816475828582294385)
                      ·
                        rfl

theorem cell23_1860356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_1860356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860356 prefixEnd_1860356 := by exact prefixLift 1860356
  have htrace : WordTrace (prefixWord ++ tailWord_1860356) baseStart_1860356 baseEnd_1860356 := by
    simpa [prefixWord, tailWord_1860356, baseEnd_1860356] using wordTrace_append hprefix tailTrace_1860356
  have hstable : (prefixWord ++ tailWord_1860356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860356).length < 2 ^ (prefixWord ++ tailWord_1860356).sum := by decide
  have hdescent : baseEnd_1860356 < baseStart_1860356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860452 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 6]
def baseStart_1860452 : Nat := 118140960795 + 1860452 * 2 ^ 59
def prefixEnd_1860452 : Nat := 4983230072969 + 3 ^ 40 * 1860452 * 2
def baseEnd_1860452 : Nat := 106145123402073356299327

theorem tailTrace_1860452 : CollatzResearch.WordTrace tailWord_1860452 prefixEnd_1860452 106145123402073356299327 := by
  unfold tailWord_1860452
  simp only [CollatzResearch.WordTrace]
  refine ⟨33928129527953809375071805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45237506037271745833429073 33928129527953809375071805)
  ·
    refine ⟨12723048572982678515651927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33928129527953809375071805 12723048572982678515651927)
    ·
      refine ⟨19084572859474017773477891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12723048572982678515651927 19084572859474017773477891)
      ·
        refine ⟨28626859289211026660216837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19084572859474017773477891 28626859289211026660216837)
        ·
          refine ⟨5367536116727067498790657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28626859289211026660216837 5367536116727067498790657)
          ·
            refine ⟨4025652087545300624092993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5367536116727067498790657 4025652087545300624092993)
            ·
              refine ⟨3019239065658975468069745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4025652087545300624092993 3019239065658975468069745)
              ·
                refine ⟨2264429299244231601052309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019239065658975468069745 2264429299244231601052309)
                ·
                  refine ⟨106145123402073356299327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2264429299244231601052309 106145123402073356299327)
                  ·
                    rfl

theorem cell23_1860452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_1860452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860452 prefixEnd_1860452 := by exact prefixLift 1860452
  have htrace : WordTrace (prefixWord ++ tailWord_1860452) baseStart_1860452 baseEnd_1860452 := by
    simpa [prefixWord, tailWord_1860452, baseEnd_1860452] using wordTrace_append hprefix tailTrace_1860452
  have hstable : (prefixWord ++ tailWord_1860452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860452).length < 2 ^ (prefixWord ++ tailWord_1860452).sum := by decide
  have hdescent : baseEnd_1860452 < baseStart_1860452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860456 : List Nat := [2, 1, 4, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1860456 : Nat := 118140960795 + 1860456 * 2 ^ 59
def prefixEnd_1860456 : Nat := 4983230072969 + 3 ^ 40 * 1860456 * 2
def baseEnd_1860456 : Nat := 318436054847092730347975

theorem tailTrace_1860456 : CollatzResearch.WordTrace tailWord_1860456 prefixEnd_1860456 318436054847092730347975 := by
  unfold tailWord_1860456
  simp only [CollatzResearch.WordTrace]
  refine ⟨33928202473946563716644611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45237603298595418288859481 33928202473946563716644611)
  ·
    refine ⟨50892303710919845574966917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33928202473946563716644611 50892303710919845574966917)
    ·
      refine ⟨9542306945797471045306297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50892303710919845574966917 9542306945797471045306297)
      ·
        refine ⟨7156730209348103283979723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9542306945797471045306297 7156730209348103283979723)
        ·
          refine ⟨10735095314022154925969585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156730209348103283979723 10735095314022154925969585)
          ·
            refine ⟨8051321485516616194477189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10735095314022154925969585 8051321485516616194477189)
            ·
              refine ⟨1509622778534365536464473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8051321485516616194477189 1509622778534365536464473)
              ·
                refine ⟨1132217083900774152348355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509622778534365536464473 1132217083900774152348355)
                ·
                  refine ⟨1698325625851161228522533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132217083900774152348355 1698325625851161228522533)
                  ·
                    refine ⟨318436054847092730347975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698325625851161228522533 318436054847092730347975)
                    ·
                      rfl

theorem cell23_1860456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1860456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860456 prefixEnd_1860456 := by exact prefixLift 1860456
  have htrace : WordTrace (prefixWord ++ tailWord_1860456) baseStart_1860456 baseEnd_1860456 := by
    simpa [prefixWord, tailWord_1860456, baseEnd_1860456] using wordTrace_append hprefix tailTrace_1860456
  have hstable : (prefixWord ++ tailWord_1860456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860456).length < 2 ^ (prefixWord ++ tailWord_1860456).sum := by decide
  have hdescent : baseEnd_1860456 < baseStart_1860456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860465 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 3, 5]
def baseStart_1860465 : Nat := 118140960795 + 1860465 * 2 ^ 59
def prefixEnd_1860465 : Nat := 4983230072969 + 3 ^ 40 * 1860465 * 2
def baseEnd_1860465 : Nat := 318437595289056218610461

theorem tailTrace_1860465 : CollatzResearch.WordTrace tailWord_1860465 prefixEnd_1860465 318437595289056218610461 := by
  unfold tailWord_1860465
  simp only [CollatzResearch.WordTrace]
  refine ⟨67856733204860521970366849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45237822136573681313577899 67856733204860521970366849)
  ·
    refine ⟨50892549903645391477775137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67856733204860521970366849 50892549903645391477775137)
    ·
      refine ⟨38169412427734043608331353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50892549903645391477775137 38169412427734043608331353)
      ·
        refine ⟨28627059320800532706248515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38169412427734043608331353 28627059320800532706248515)
        ·
          refine ⟨42940588981200799059372773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28627059320800532706248515 42940588981200799059372773)
          ·
            refine ⟨8051360433975149823632395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42940588981200799059372773 8051360433975149823632395)
            ·
              refine ⟨12077040650962724735448593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051360433975149823632395 12077040650962724735448593)
              ·
                refine ⟨9057780488222043551586445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12077040650962724735448593 9057780488222043551586445)
                ·
                  refine ⟨3396667683083266331844917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9057780488222043551586445 3396667683083266331844917)
                  ·
                    refine ⟨318437595289056218610461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3396667683083266331844917 318437595289056218610461)
                    ·
                      rfl

theorem cell23_1860465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_1860465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860465 prefixEnd_1860465 := by exact prefixLift 1860465
  have htrace : WordTrace (prefixWord ++ tailWord_1860465) baseStart_1860465 baseEnd_1860465 := by
    simpa [prefixWord, tailWord_1860465, baseEnd_1860465] using wordTrace_append hprefix tailTrace_1860465
  have hstable : (prefixWord ++ tailWord_1860465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860465).length < 2 ^ (prefixWord ++ tailWord_1860465).sum := by decide
  have hdescent : baseEnd_1860465 < baseStart_1860465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860489 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 2, 3, 2]
def baseStart_1860489 : Nat := 118140960795 + 1860489 * 2 ^ 59
def prefixEnd_1860489 : Nat := 4983230072969 + 3 ^ 40 * 1860489 * 2
def baseEnd_1860489 : Nat := 955325109402876561931273

theorem tailTrace_1860489 : CollatzResearch.WordTrace tailWord_1860489 prefixEnd_1860489 955325109402876561931273 := by
  unfold tailWord_1860489
  simp only [CollatzResearch.WordTrace]
  refine ⟨67857608556773574069240521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45238405704515716046160347 67857608556773574069240521)
  ·
    refine ⟨50893206417580180551930391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67857608556773574069240521 50893206417580180551930391)
    ·
      refine ⟨76339809626370270827895587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50893206417580180551930391 76339809626370270827895587)
      ·
        refine ⟨114509714439555406241843381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76339809626370270827895587 114509714439555406241843381)
        ·
          refine ⟨10735285728708319335172817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114509714439555406241843381 10735285728708319335172817)
          ·
            refine ⟨8051464296531239501379613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10735285728708319335172817 8051464296531239501379613)
            ·
              refine ⟨3019299111199214813017355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8051464296531239501379613 3019299111199214813017355)
              ·
                refine ⟨4528948666798822219526033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019299111199214813017355 4528948666798822219526033)
                ·
                  refine ⟨3396711500099116664644525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4528948666798822219526033 3396711500099116664644525)
                  ·
                    refine ⟨1273766812537168749241697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396711500099116664644525 1273766812537168749241697)
                    ·
                      refine ⟨955325109402876561931273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273766812537168749241697 955325109402876561931273)
                      ·
                        rfl

theorem cell23_1860489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 3, 2].length) (baseStart_1860489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860489 prefixEnd_1860489 := by exact prefixLift 1860489
  have htrace : WordTrace (prefixWord ++ tailWord_1860489) baseStart_1860489 baseEnd_1860489 := by
    simpa [prefixWord, tailWord_1860489, baseEnd_1860489] using wordTrace_append hprefix tailTrace_1860489
  have hstable : (prefixWord ++ tailWord_1860489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860489).length < 2 ^ (prefixWord ++ tailWord_1860489).sum := by decide
  have hdescent : baseEnd_1860489 < baseStart_1860489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860505 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_1860505 : Nat := 118140960795 + 1860505 * 2 ^ 59
def prefixEnd_1860505 : Nat := 4983230072969 + 3 ^ 40 * 1860505 * 2
def baseEnd_1860505 : Nat := 955333325093348499331199

theorem tailTrace_1860505 : CollatzResearch.WordTrace tailWord_1860505 prefixEnd_1860505 955333325093348499331199 := by
  unfold tailWord_1860505
  simp only [CollatzResearch.WordTrace]
  refine ⟨67858192124715608801822969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45238794749810405867881979 67858192124715608801822969)
  ·
    refine ⟨50893644093536706601367227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67858192124715608801822969 50893644093536706601367227)
    ·
      refine ⟨76340466140305059902050841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50893644093536706601367227 76340466140305059902050841)
      ·
        refine ⟨57255349605228794926538131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76340466140305059902050841 57255349605228794926538131)
        ·
          refine ⟨85883024407843192389807197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57255349605228794926538131 85883024407843192389807197)
          ·
            refine ⟨32206134152941197146177699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85883024407843192389807197 32206134152941197146177699)
            ·
              refine ⟨48309201229411795719266549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32206134152941197146177699 48309201229411795719266549)
              ·
                refine ⟨4528987615257355848681239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48309201229411795719266549 4528987615257355848681239)
                ·
                  refine ⟨6793481422886033773021859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528987615257355848681239 6793481422886033773021859)
                  ·
                    refine ⟨10190222134329050659532789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6793481422886033773021859 10190222134329050659532789)
                    ·
                      refine ⟨955333325093348499331199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10190222134329050659532789 955333325093348499331199)
                      ·
                        rfl

theorem cell23_1860505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_1860505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860505 prefixEnd_1860505 := by exact prefixLift 1860505
  have htrace : WordTrace (prefixWord ++ tailWord_1860505) baseStart_1860505 baseEnd_1860505 := by
    simpa [prefixWord, tailWord_1860505, baseEnd_1860505] using wordTrace_append hprefix tailTrace_1860505
  have hstable : (prefixWord ++ tailWord_1860505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860505).length < 2 ^ (prefixWord ++ tailWord_1860505).sum := by decide
  have hdescent : baseEnd_1860505 < baseStart_1860505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860515 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 4]
def baseStart_1860515 : Nat := 118140960795 + 1860515 * 2 ^ 59
def prefixEnd_1860515 : Nat := 4983230072969 + 3 ^ 40 * 1860515 * 2
def baseEnd_1860515 : Nat := 955338459899893460206153

theorem tailTrace_1860515 : CollatzResearch.WordTrace tailWord_1860515 prefixEnd_1860515 955338459899893460206153 := by
  unfold tailWord_1860515
  simp only [CollatzResearch.WordTrace]
  refine ⟨67858556854679380509686999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45239037903119587006457999 67858556854679380509686999)
  ·
    refine ⟨101787835282019070764530499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67858556854679380509686999 101787835282019070764530499)
    ·
      refine ⟨152681752923028606146795749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101787835282019070764530499 152681752923028606146795749)
      ·
        refine ⟨28627828673067863652524203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152681752923028606146795749 28627828673067863652524203)
        ·
          refine ⟨42941743009601795478786305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28627828673067863652524203 42941743009601795478786305)
          ·
            refine ⟨32206307257201346609089729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42941743009601795478786305 32206307257201346609089729)
            ·
              refine ⟨24154730442901009956817297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32206307257201346609089729 24154730442901009956817297)
              ·
                refine ⟨18116047832175757467612973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24154730442901009956817297 18116047832175757467612973)
                ·
                  refine ⟨6793517937065909050354865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18116047832175757467612973 6793517937065909050354865)
                  ·
                    refine ⟨5095138452799431787766149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6793517937065909050354865 5095138452799431787766149)
                    ·
                      refine ⟨955338459899893460206153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5095138452799431787766149 955338459899893460206153)
                      ·
                        rfl

theorem cell23_1860515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_1860515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860515 prefixEnd_1860515 := by exact prefixLift 1860515
  have htrace : WordTrace (prefixWord ++ tailWord_1860515) baseStart_1860515 baseEnd_1860515 := by
    simpa [prefixWord, tailWord_1860515, baseEnd_1860515] using wordTrace_append hprefix tailTrace_1860515
  have hstable : (prefixWord ++ tailWord_1860515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860515).length < 2 ^ (prefixWord ++ tailWord_1860515).sum := by decide
  have hdescent : baseEnd_1860515 < baseStart_1860515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860529 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 1, 6]
def baseStart_1860529 : Nat := 118140960795 + 1860529 * 2 ^ 59
def prefixEnd_1860529 : Nat := 4983230072969 + 3 ^ 40 * 1860529 * 2
def baseEnd_1860529 : Nat := 318448549543018801810363

theorem tailTrace_1860529 : CollatzResearch.WordTrace tailWord_1860529 prefixEnd_1860529 318448549543018801810363 := by
  unfold tailWord_1860529
  simp only [CollatzResearch.WordTrace]
  refine ⟨67859067476628660900696641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45239378317752440600464427 67859067476628660900696641)
  ·
    refine ⟨50894300607471495675522481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67859067476628660900696641 50894300607471495675522481)
    ·
      refine ⟨38170725455603621756641861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50894300607471495675522481 38170725455603621756641861)
      ·
        refine ⟨7157011022925679079370349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38170725455603621756641861 7157011022925679079370349)
        ·
          refine ⟨2683879133597129654763881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7157011022925679079370349 2683879133597129654763881)
          ·
            refine ⟨2012909350197847241072911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683879133597129654763881 2012909350197847241072911)
            ·
              refine ⟨3019364025296770861609367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012909350197847241072911 3019364025296770861609367)
              ·
                refine ⟨4529046037945156292414051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019364025296770861609367 4529046037945156292414051)
                ·
                  refine ⟨6793569056917734438621077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529046037945156292414051 6793569056917734438621077)
                  ·
                    refine ⟨318448549543018801810363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6793569056917734438621077 318448549543018801810363)
                    ·
                      rfl

theorem cell23_1860529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_1860529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860529 prefixEnd_1860529 := by exact prefixLift 1860529
  have htrace : WordTrace (prefixWord ++ tailWord_1860529) baseStart_1860529 baseEnd_1860529 := by
    simpa [prefixWord, tailWord_1860529, baseEnd_1860529] using wordTrace_append hprefix tailTrace_1860529
  have hstable : (prefixWord ++ tailWord_1860529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860529).length < 2 ^ (prefixWord ++ tailWord_1860529).sum := by decide
  have hdescent : baseEnd_1860529 < baseStart_1860529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860569 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 3]
def baseStart_1860569 : Nat := 118140960795 + 1860569 * 2 ^ 59
def prefixEnd_1860569 : Nat := 4983230072969 + 3 ^ 40 * 1860569 * 2
def baseEnd_1860569 : Nat := 955366187855236248930905

theorem tailTrace_1860569 : CollatzResearch.WordTrace tailWord_1860569 prefixEnd_1860569 955366187855236248930905 := by
  unfold tailWord_1860569
  simp only [CollatzResearch.WordTrace]
  refine ⟨67860526396483747732152761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45240350930989165154768507 67860526396483747732152761)
  ·
    refine ⟨50895394797362810799114571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67860526396483747732152761 50895394797362810799114571)
    ·
      refine ⟨76343092196044216198671857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50895394797362810799114571 76343092196044216198671857)
      ·
        refine ⟨57257319147033162149003893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76343092196044216198671857 57257319147033162149003893)
        ·
          refine ⟨5367873670034358951469115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57257319147033162149003893 5367873670034358951469115)
          ·
            refine ⟨8051810505051538427203673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367873670034358951469115 8051810505051538427203673)
            ·
              refine ⟨6038857878788653820402755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051810505051538427203673 6038857878788653820402755)
              ·
                refine ⟨9058286818182980730604133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038857878788653820402755 9058286818182980730604133)
                ·
                  refine ⟨1698428778409308886988275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9058286818182980730604133 1698428778409308886988275)
                  ·
                    refine ⟨2547643167613963330482413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1698428778409308886988275 2547643167613963330482413)
                    ·
                      refine ⟨955366187855236248930905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2547643167613963330482413 955366187855236248930905)
                      ·
                        rfl

theorem cell23_1860569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_1860569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860569 prefixEnd_1860569 := by exact prefixLift 1860569
  have htrace : WordTrace (prefixWord ++ tailWord_1860569) baseStart_1860569 baseEnd_1860569 := by
    simpa [prefixWord, tailWord_1860569, baseEnd_1860569] using wordTrace_append hprefix tailTrace_1860569
  have hstable : (prefixWord ++ tailWord_1860569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860569).length < 2 ^ (prefixWord ++ tailWord_1860569).sum := by decide
  have hdescent : baseEnd_1860569 < baseStart_1860569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860570 : List Nat := [3, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2]
def baseStart_1860570 : Nat := 118140960795 + 1860570 * 2 ^ 59
def prefixEnd_1860570 : Nat := 4983230072969 + 3 ^ 40 * 1860570 * 2
def baseEnd_1860570 : Nat := 955366701335890745018401

theorem tailTrace_1860570 : CollatzResearch.WordTrace tailWord_1860570 prefixEnd_1860570 955366701335890745018401 := by
  unfold tailWord_1860570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16965140717370031225734791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45240375246320083268626109 16965140717370031225734791)
  ·
    refine ⟨25447711076055046838602187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16965140717370031225734791 25447711076055046838602187)
    ·
      refine ⟨38171566614082570257903281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25447711076055046838602187 38171566614082570257903281)
      ·
        refine ⟨28628674960561927693427461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38171566614082570257903281 28628674960561927693427461)
        ·
          refine ⟨5367876555105361442517649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28628674960561927693427461 5367876555105361442517649)
          ·
            refine ⟨4025907416329021081888237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5367876555105361442517649 4025907416329021081888237)
            ·
              refine ⟨1509715281123382905708089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4025907416329021081888237 1509715281123382905708089)
              ·
                refine ⟨1132286460842537179281067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509715281123382905708089 1132286460842537179281067)
                ·
                  refine ⟨1698429691263805768921601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132286460842537179281067 1698429691263805768921601)
                  ·
                    refine ⟨1273822268447854326691201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1698429691263805768921601 1273822268447854326691201)
                    ·
                      refine ⟨955366701335890745018401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273822268447854326691201 955366701335890745018401)
                      ·
                        rfl

theorem cell23_1860570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_1860570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860570 prefixEnd_1860570 := by exact prefixLift 1860570
  have htrace : WordTrace (prefixWord ++ tailWord_1860570) baseStart_1860570 baseEnd_1860570 := by
    simpa [prefixWord, tailWord_1860570, baseEnd_1860570] using wordTrace_append hprefix tailTrace_1860570
  have hstable : (prefixWord ++ tailWord_1860570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860570).length < 2 ^ (prefixWord ++ tailWord_1860570).sum := by decide
  have hdescent : baseEnd_1860570 < baseStart_1860570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860579 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1860579 : Nat := 118140960795 + 1860579 * 2 ^ 59
def prefixEnd_1860579 : Nat := 4983230072969 + 3 ^ 40 * 1860579 * 2
def baseEnd_1860579 : Nat := 955371322661781209805859

theorem tailTrace_1860579 : CollatzResearch.WordTrace tailWord_1860579 prefixEnd_1860579 955371322661781209805859 := by
  unfold tailWord_1860579
  simp only [CollatzResearch.WordTrace]
  refine ⟨67860891126447519440016791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45240594084298346293344527 67860891126447519440016791)
  ·
    refine ⟨101791336689671279160025187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67860891126447519440016791 101791336689671279160025187)
    ·
      refine ⟨152687005034506918740037781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101791336689671279160025187 152687005034506918740037781)
      ·
        refine ⟨7157203360992511815939271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152687005034506918740037781 7157203360992511815939271)
        ·
          refine ⟨10735805041488767723908907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7157203360992511815939271 10735805041488767723908907)
          ·
            refine ⟨16103707562233151585863361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10735805041488767723908907 16103707562233151585863361)
            ·
              refine ⟨12077780671674863689397521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16103707562233151585863361 12077780671674863689397521)
              ·
                refine ⟨9058335503756147767048141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12077780671674863689397521 9058335503756147767048141)
                ·
                  refine ⟨3396875813908555412643053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9058335503756147767048141 3396875813908555412643053)
                  ·
                    refine ⟨1273828430215708279741145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396875813908555412643053 1273828430215708279741145)
                    ·
                      refine ⟨955371322661781209805859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273828430215708279741145 955371322661781209805859)
                      ·
                        rfl

theorem cell23_1860579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1860579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860579 prefixEnd_1860579 := by exact prefixLift 1860579
  have htrace : WordTrace (prefixWord ++ tailWord_1860579) baseStart_1860579 baseEnd_1860579 := by
    simpa [prefixWord, tailWord_1860579, baseEnd_1860579] using wordTrace_append hprefix tailTrace_1860579
  have hstable : (prefixWord ++ tailWord_1860579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860579).length < 2 ^ (prefixWord ++ tailWord_1860579).sum := by decide
  have hdescent : baseEnd_1860579 < baseStart_1860579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860586 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_1860586 : Nat := 118140960795 + 1860586 * 2 ^ 59
def prefixEnd_1860586 : Nat := 4983230072969 + 3 ^ 40 * 1860586 * 2
def baseEnd_1860586 : Nat := 955374917026362682418327

theorem tailTrace_1860586 : CollatzResearch.WordTrace tailWord_1860586 prefixEnd_1860586 955374917026362682418327 := by
  unfold tailWord_1860586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16965286609355539908880403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45240764291614773090347741 16965286609355539908880403)
  ·
    refine ⟨25447929914033309863320605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16965286609355539908880403 25447929914033309863320605)
    ·
      refine ⟨9542973717762491198745227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25447929914033309863320605 9542973717762491198745227)
      ·
        refine ⟨14314460576643736798117841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9542973717762491198745227 14314460576643736798117841)
        ·
          refine ⟨10735845432482802598588381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14314460576643736798117841 10735845432482802598588381)
          ·
            refine ⟨4025942037181050974470643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10735845432482802598588381 4025942037181050974470643)
            ·
              refine ⟨6038913055771576461705965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4025942037181050974470643 6038913055771576461705965)
              ·
                refine ⟨2264592395914341173139737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6038913055771576461705965 2264592395914341173139737)
                ·
                  refine ⟨1698444296935755879854803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2264592395914341173139737 1698444296935755879854803)
                  ·
                    refine ⟨2547666445403633819782205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1698444296935755879854803 2547666445403633819782205)
                    ·
                      refine ⟨955374917026362682418327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2547666445403633819782205 955374917026362682418327)
                      ·
                        rfl

theorem cell23_1860586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_1860586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860586 prefixEnd_1860586 := by exact prefixLift 1860586
  have htrace : WordTrace (prefixWord ++ tailWord_1860586) baseStart_1860586 baseEnd_1860586 := by
    simpa [prefixWord, tailWord_1860586, baseEnd_1860586] using wordTrace_append hprefix tailTrace_1860586
  have hstable : (prefixWord ++ tailWord_1860586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860586).length < 2 ^ (prefixWord ++ tailWord_1860586).sum := by decide
  have hdescent : baseEnd_1860586 < baseStart_1860586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860609 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_1860609 : Nat := 118140960795 + 1860609 * 2 ^ 59
def prefixEnd_1860609 : Nat := 4983230072969 + 3 ^ 40 * 1860609 * 2
def baseEnd_1860609 : Nat := 955386727081416092430721

theorem tailTrace_1860609 : CollatzResearch.WordTrace tailWord_1860609 prefixEnd_1860609 955386727081416092430721 := by
  unfold tailWord_1860609
  simp only [CollatzResearch.WordTrace]
  refine ⟨67861985316338834563608881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45241323544225889709072587 67861985316338834563608881)
  ·
    refine ⟨50896488987254125922706661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67861985316338834563608881 50896488987254125922706661)
    ·
      refine ⟨9543091685110148610507499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50896488987254125922706661 9543091685110148610507499)
      ·
        refine ⟨14314637527665222915761249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9543091685110148610507499 14314637527665222915761249)
        ·
          refine ⟨10735978145748917186820937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14314637527665222915761249 10735978145748917186820937)
          ·
            refine ⟨8051983609311687890115703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10735978145748917186820937 8051983609311687890115703)
            ·
              refine ⟨12077975413967531835173555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051983609311687890115703 12077975413967531835173555)
              ·
                refine ⟨18116963120951297752760333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12077975413967531835173555 18116963120951297752760333)
                ·
                  refine ⟨6793861170356736657285125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18116963120951297752760333 6793861170356736657285125)
                  ·
                    refine ⟨1273848969441888123240961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6793861170356736657285125 1273848969441888123240961)
                    ·
                      refine ⟨955386727081416092430721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273848969441888123240961 955386727081416092430721)
                      ·
                        rfl

theorem cell23_1860609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_1860609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860609 prefixEnd_1860609 := by exact prefixLift 1860609
  have htrace : WordTrace (prefixWord ++ tailWord_1860609) baseStart_1860609 baseEnd_1860609 := by
    simpa [prefixWord, tailWord_1860609, baseEnd_1860609] using wordTrace_append hprefix tailTrace_1860609
  have hstable : (prefixWord ++ tailWord_1860609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860609).length < 2 ^ (prefixWord ++ tailWord_1860609).sum := by decide
  have hdescent : baseEnd_1860609 < baseStart_1860609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860625 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_1860625 : Nat := 118140960795 + 1860625 * 2 ^ 59
def prefixEnd_1860625 : Nat := 4983230072969 + 3 ^ 40 * 1860625 * 2
def baseEnd_1860625 : Nat := 955394942771888029830647

theorem tailTrace_1860625 : CollatzResearch.WordTrace tailWord_1860625 prefixEnd_1860625 955394942771888029830647 := by
  unfold tailWord_1860625
  simp only [CollatzResearch.WordTrace]
  refine ⟨67862568884280869296191329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45241712589520579530794219 67862568884280869296191329)
  ·
    refine ⟨50896926663210651972143497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67862568884280869296191329 50896926663210651972143497)
    ·
      refine ⟨38172694997407988979107623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50896926663210651972143497 38172694997407988979107623)
      ·
        refine ⟨57259042496111983468661435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38172694997407988979107623 57259042496111983468661435)
        ·
          refine ⟨85888563744167975202992153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57259042496111983468661435 85888563744167975202992153)
          ·
            refine ⟨64416422808125981402244115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85888563744167975202992153 64416422808125981402244115)
            ·
              refine ⟨96624634212188972103366173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64416422808125981402244115 96624634212188972103366173)
              ·
                refine ⟨36234237829570864538762315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96624634212188972103366173 36234237829570864538762315)
                ·
                  refine ⟨54351356744356296808143473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36234237829570864538762315 54351356744356296808143473)
                  ·
                    refine ⟨40763517558267222606107605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54351356744356296808143473 40763517558267222606107605)
                    ·
                      refine ⟨955394942771888029830647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40763517558267222606107605 955394942771888029830647)
                      ·
                        rfl

theorem cell23_1860625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_1860625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860625 prefixEnd_1860625 := by exact prefixLift 1860625
  have htrace : WordTrace (prefixWord ++ tailWord_1860625) baseStart_1860625 baseEnd_1860625 := by
    simpa [prefixWord, tailWord_1860625, baseEnd_1860625] using wordTrace_append hprefix tailTrace_1860625
  have hstable : (prefixWord ++ tailWord_1860625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860625).length < 2 ^ (prefixWord ++ tailWord_1860625).sum := by decide
  have hdescent : baseEnd_1860625 < baseStart_1860625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860694 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_1860694 : Nat := 118140960795 + 1860694 * 2 ^ 59
def prefixEnd_1860694 : Nat := 4983230072969 + 3 ^ 40 * 1860694 * 2
def baseEnd_1860694 : Nat := 955430372937048259867831

theorem tailTrace_1860694 : CollatzResearch.WordTrace tailWord_1860694 prefixEnd_1860694 955430372937048259867831 := by
  unfold tailWord_1860694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241567845064430880028321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45243390347353929386968757 4241567845064430880028321)
  ·
    refine ⟨3181175883798323160021241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4241567845064430880028321 3181175883798323160021241)
    ·
      refine ⟨2385881912848742370015931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3181175883798323160021241 2385881912848742370015931)
      ·
        refine ⟨3578822869273113555023897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385881912848742370015931 3578822869273113555023897)
        ·
          refine ⟨2684117151954835166267923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3578822869273113555023897 2684117151954835166267923)
          ·
            refine ⟨4026175727932252749401885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684117151954835166267923 4026175727932252749401885)
            ·
              refine ⟨1509815897974594781025707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4026175727932252749401885 1509815897974594781025707)
              ·
                refine ⟨2264723846961892171538561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509815897974594781025707 2264723846961892171538561)
                ·
                  refine ⟨1698542885221419128653921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2264723846961892171538561 1698542885221419128653921)
                  ·
                    refine ⟨1273907163916064346490441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1698542885221419128653921 1273907163916064346490441)
                    ·
                      refine ⟨955430372937048259867831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1273907163916064346490441 955430372937048259867831)
                      ·
                        rfl

theorem cell23_1860694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_1860694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860694 prefixEnd_1860694 := by exact prefixLift 1860694
  have htrace : WordTrace (prefixWord ++ tailWord_1860694) baseStart_1860694 baseEnd_1860694 := by
    simpa [prefixWord, tailWord_1860694, baseEnd_1860694] using wordTrace_append hprefix tailTrace_1860694
  have hstable : (prefixWord ++ tailWord_1860694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860694).length < 2 ^ (prefixWord ++ tailWord_1860694).sum := by decide
  have hdescent : baseEnd_1860694 < baseStart_1860694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860709 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_1860709 : Nat := 118140960795 + 1860709 * 2 ^ 59
def prefixEnd_1860709 : Nat := 4983230072969 + 3 ^ 40 * 1860709 * 2
def baseEnd_1860709 : Nat := 318479358382288567060087

theorem tailTrace_1860709 : CollatzResearch.WordTrace tailWord_1860709 prefixEnd_1860709 318479358382288567060087 := by
  unfold tailWord_1860709
  simp only [CollatzResearch.WordTrace]
  refine ⟨67865632615976551642249181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45243755077317701094832787 67865632615976551642249181)
  ·
    refine ⟨25449612230991206865843443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67865632615976551642249181 25449612230991206865843443)
    ·
      refine ⟨38174418346486810298765165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25449612230991206865843443 38174418346486810298765165)
      ·
        refine ⟨14315406879932553862036937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38174418346486810298765165 14315406879932553862036937)
        ·
          refine ⟨10736555159949415396527703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14315406879932553862036937 10736555159949415396527703)
          ·
            refine ⟨16104832739924123094791555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10736555159949415396527703 16104832739924123094791555)
            ·
              refine ⟨24157249109886184642187333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16104832739924123094791555 24157249109886184642187333)
              ·
                refine ⟨4529484208103659620410125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24157249109886184642187333 4529484208103659620410125)
                ·
                  refine ⟨1698556578038872357653797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4529484208103659620410125 1698556578038872357653797)
                  ·
                    refine ⟨318479358382288567060087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698556578038872357653797 318479358382288567060087)
                    ·
                      rfl

theorem cell23_1860709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_1860709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860709 prefixEnd_1860709 := by exact prefixLift 1860709
  have htrace : WordTrace (prefixWord ++ tailWord_1860709) baseStart_1860709 baseEnd_1860709 := by
    simpa [prefixWord, tailWord_1860709, baseEnd_1860709] using wordTrace_append hprefix tailTrace_1860709
  have hstable : (prefixWord ++ tailWord_1860709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860709).length < 2 ^ (prefixWord ++ tailWord_1860709).sum := by decide
  have hdescent : baseEnd_1860709 < baseStart_1860709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860719 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 3]
def baseStart_1860719 : Nat := 118140960795 + 1860719 * 2 ^ 59
def prefixEnd_1860719 : Nat := 4983230072969 + 3 ^ 40 * 1860719 * 2
def baseEnd_1860719 : Nat := 955443209953410662055215

theorem tailTrace_1860719 : CollatzResearch.WordTrace tailWord_1860719 prefixEnd_1860719 955443209953410662055215 := by
  unfold tailWord_1860719
  simp only [CollatzResearch.WordTrace]
  refine ⟨67865997345940323350113211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45243998230626882233408807 67865997345940323350113211)
  ·
    refine ⟨101798996018910485025169817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67865997345940323350113211 101798996018910485025169817)
    ·
      refine ⟨76349247014182863768877363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101798996018910485025169817 76349247014182863768877363)
      ·
        refine ⟨114523870521274295653316045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76349247014182863768877363 114523870521274295653316045)
        ·
          refine ⟨42946451445477860869993517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114523870521274295653316045 42946451445477860869993517)
          ·
            refine ⟨16104919292054197826247569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42946451445477860869993517 16104919292054197826247569)
            ·
              refine ⟨12078689469040648369685677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16104919292054197826247569 12078689469040648369685677)
              ·
                refine ⟨4529508550890243138632129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12078689469040648369685677 4529508550890243138632129)
                ·
                  refine ⟨3397131413167682353974097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4529508550890243138632129 3397131413167682353974097)
                  ·
                    refine ⟨2547848559875761765480573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3397131413167682353974097 2547848559875761765480573)
                    ·
                      refine ⟨955443209953410662055215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2547848559875761765480573 955443209953410662055215)
                      ·
                        rfl

theorem cell23_1860719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_1860719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860719 prefixEnd_1860719 := by exact prefixLift 1860719
  have htrace : WordTrace (prefixWord ++ tailWord_1860719) baseStart_1860719 baseEnd_1860719 := by
    simpa [prefixWord, tailWord_1860719, baseEnd_1860719] using wordTrace_append hprefix tailTrace_1860719
  have hstable : (prefixWord ++ tailWord_1860719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860719).length < 2 ^ (prefixWord ++ tailWord_1860719).sum := by decide
  have hdescent : baseEnd_1860719 < baseStart_1860719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860722 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 10]
def baseStart_1860722 : Nat := 118140960795 + 1860722 * 2 ^ 59
def prefixEnd_1860722 : Nat := 4983230072969 + 3 ^ 40 * 1860722 * 2
def baseEnd_1860722 : Nat := 106160527821708238924189

theorem tailTrace_1860722 : CollatzResearch.WordTrace tailWord_1860722 prefixEnd_1860722 106160527821708238924189 := by
  unfold tailWord_1860722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16966526691232363715618105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45244071176619636574981613 16966526691232363715618105)
  ·
    refine ⟨12724895018424272786713579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16966526691232363715618105 12724895018424272786713579)
    ·
      refine ⟨19087342527636409180070369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12724895018424272786713579 19087342527636409180070369)
      ·
        refine ⟨14315506895727306885052777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19087342527636409180070369 14315506895727306885052777)
        ·
          refine ⟨10736630171795480163789583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14315506895727306885052777 10736630171795480163789583)
          ·
            refine ⟨16104945257693220245684375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10736630171795480163789583 16104945257693220245684375)
            ·
              refine ⟨24157417886539830368526563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16104945257693220245684375 24157417886539830368526563)
              ·
                refine ⟨36236126829809745552789845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24157417886539830368526563 36236126829809745552789845)
                ·
                  refine ⟨106160527821708238924189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 36236126829809745552789845 106160527821708238924189)
                  ·
                    rfl

theorem cell23_1860722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_1860722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860722 prefixEnd_1860722 := by exact prefixLift 1860722
  have htrace : WordTrace (prefixWord ++ tailWord_1860722) baseStart_1860722 baseEnd_1860722 := by
    simpa [prefixWord, tailWord_1860722, baseEnd_1860722] using wordTrace_append hprefix tailTrace_1860722
  have hstable : (prefixWord ++ tailWord_1860722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860722).length < 2 ^ (prefixWord ++ tailWord_1860722).sum := by decide
  have hdescent : baseEnd_1860722 < baseStart_1860722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860769 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 3, 5]
def baseStart_1860769 : Nat := 118140960795 + 1860769 * 2 ^ 59
def prefixEnd_1860769 : Nat := 4983230072969 + 3 ^ 40 * 1860769 * 2
def baseEnd_1860769 : Nat := 318489627995378488809995

theorem tailTrace_1860769 : CollatzResearch.WordTrace tailWord_1860769 prefixEnd_1860769 318489627995378488809995 := by
  unfold tailWord_1860769
  simp only [CollatzResearch.WordTrace]
  refine ⟨67867820995759181889433361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45245213997172787926288907 67867820995759181889433361)
  ·
    refine ⟨50900865746819386417075021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67867820995759181889433361 50900865746819386417075021)
    ·
      refine ⟨19087824655057269906403133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50900865746819386417075021 19087824655057269906403133)
      ·
        refine ⟨7157934245646476214901175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19087824655057269906403133 7157934245646476214901175)
        ·
          refine ⟨10736901368469714322351763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7157934245646476214901175 10736901368469714322351763)
          ·
            refine ⟨16105352052704571483527645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10736901368469714322351763 16105352052704571483527645)
            ·
              refine ⟨6039507019764214306322867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16105352052704571483527645 6039507019764214306322867)
              ·
                refine ⟨9059260529646321459484301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6039507019764214306322867 9059260529646321459484301)
                ·
                  refine ⟨3397222698617370547306613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9059260529646321459484301 3397222698617370547306613)
                  ·
                    refine ⟨318489627995378488809995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3397222698617370547306613 318489627995378488809995)
                    ·
                      rfl

theorem cell23_1860769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_1860769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860769 prefixEnd_1860769 := by exact prefixLift 1860769
  have htrace : WordTrace (prefixWord ++ tailWord_1860769) baseStart_1860769 baseEnd_1860769 := by
    simpa [prefixWord, tailWord_1860769, baseEnd_1860769] using wordTrace_append hprefix tailTrace_1860769
  have hstable : (prefixWord ++ tailWord_1860769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860769).length < 2 ^ (prefixWord ++ tailWord_1860769).sum := by decide
  have hdescent : baseEnd_1860769 < baseStart_1860769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860790 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1860790 : Nat := 118140960795 + 1860790 * 2 ^ 59
def prefixEnd_1860790 : Nat := 4983230072969 + 3 ^ 40 * 1860790 * 2
def baseEnd_1860790 : Nat := 106164407453319987140821

theorem tailTrace_1860790 : CollatzResearch.WordTrace tailWord_1860790 prefixEnd_1860790 106164407453319987140821 := by
  unfold tailWord_1860790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241786683042693904746739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45245724619122068317298549 4241786683042693904746739)
  ·
    refine ⟨6362680024564040857120109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241786683042693904746739 6362680024564040857120109)
    ·
      refine ⟨2386005009211515321420041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6362680024564040857120109 2386005009211515321420041)
      ·
        refine ⟨1789503756908636491065031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2386005009211515321420041 1789503756908636491065031)
        ·
          refine ⟨2684255635362954736597547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789503756908636491065031 2684255635362954736597547)
          ·
            refine ⟨4026383453044432104896321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684255635362954736597547 4026383453044432104896321)
            ·
              refine ⟨3019787589783324078672241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026383453044432104896321 3019787589783324078672241)
              ·
                refine ⟨2264840692337493059004181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019787589783324078672241 2264840692337493059004181)
                ·
                  refine ⟨106164407453319987140821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2264840692337493059004181 106164407453319987140821)
                  ·
                    rfl

theorem cell23_1860790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1860790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860790 prefixEnd_1860790 := by exact prefixLift 1860790
  have htrace : WordTrace (prefixWord ++ tailWord_1860790) baseStart_1860790 baseEnd_1860790 := by
    simpa [prefixWord, tailWord_1860790, baseEnd_1860790] using wordTrace_append hprefix tailTrace_1860790
  have hstable : (prefixWord ++ tailWord_1860790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860790).length < 2 ^ (prefixWord ++ tailWord_1860790).sum := by decide
  have hdescent : baseEnd_1860790 < baseStart_1860790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860799 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 4, 4]
def baseStart_1860799 : Nat := 118140960795 + 1860799 * 2 ^ 59
def prefixEnd_1860799 : Nat := 4983230072969 + 3 ^ 40 * 1860799 * 2
def baseEnd_1860799 : Nat := 318494762801923449684949

theorem tailTrace_1860799 : CollatzResearch.WordTrace tailWord_1860799 prefixEnd_1860799 318494762801923449684949 := by
  unfold tailWord_1860799
  simp only [CollatzResearch.WordTrace]
  refine ⟨67868915185650497013025451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45245943457100331342016967 67868915185650497013025451)
  ·
    refine ⟨101803372778475745519538177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67868915185650497013025451 101803372778475745519538177)
    ·
      refine ⟨76352529583856809139653633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101803372778475745519538177 76352529583856809139653633)
      ·
        refine ⟨57264397187892606854740225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76352529583856809139653633 57264397187892606854740225)
        ·
          refine ⟨42948297890919455141055169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57264397187892606854740225 42948297890919455141055169)
          ·
            refine ⟨32211223418189591355791377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42948297890919455141055169 32211223418189591355791377)
            ·
              refine ⟨24158417563642193516843533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32211223418189591355791377 24158417563642193516843533)
              ·
                refine ⟨9059406586365822568816325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24158417563642193516843533 9059406586365822568816325)
                ·
                  refine ⟨1698638734943591731653061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9059406586365822568816325 1698638734943591731653061)
                  ·
                    refine ⟨318494762801923449684949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698638734943591731653061 318494762801923449684949)
                    ·
                      rfl

theorem cell23_1860799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 4].length) (baseStart_1860799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860799 prefixEnd_1860799 := by exact prefixLift 1860799
  have htrace : WordTrace (prefixWord ++ tailWord_1860799) baseStart_1860799 baseEnd_1860799 := by
    simpa [prefixWord, tailWord_1860799, baseEnd_1860799] using wordTrace_append hprefix tailTrace_1860799
  have hstable : (prefixWord ++ tailWord_1860799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860799).length < 2 ^ (prefixWord ++ tailWord_1860799).sum := by decide
  have hdescent : baseEnd_1860799 < baseStart_1860799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860800 : List Nat := [2, 1, 1, 2, 6, 1, 1, 4, 1, 1, 3]
def baseStart_1860800 : Nat := 118140960795 + 1860800 * 2 ^ 59
def prefixEnd_1860800 : Nat := 4983230072969 + 3 ^ 40 * 1860800 * 2
def baseEnd_1860800 : Nat := 955484801886424845142343

theorem tailTrace_1860800 : CollatzResearch.WordTrace tailWord_1860800 prefixEnd_1860800 955484801886424845142343 := by
  unfold tailWord_1860800
  simp only [CollatzResearch.WordTrace]
  refine ⟨33934475829323437091905927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45245967772431249455874569 33934475829323437091905927)
  ·
    refine ⟨50901713743985155637858891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33934475829323437091905927 50901713743985155637858891)
    ·
      refine ⟨76352570615977733456788337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50901713743985155637858891 76352570615977733456788337)
      ·
        refine ⟨57264427961983300092591253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76352570615977733456788337 57264427961983300092591253)
        ·
          refine ⟨2684270060717967191840215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57264427961983300092591253 2684270060717967191840215)
          ·
            refine ⟨4026405091076950787760323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684270060717967191840215 4026405091076950787760323)
            ·
              refine ⟨6039607636615426181640485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026405091076950787760323 6039607636615426181640485)
              ·
                refine ⟨1132426431865392409057591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6039607636615426181640485 1132426431865392409057591)
                ·
                  refine ⟨1698639647798088613586387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132426431865392409057591 1698639647798088613586387)
                  ·
                    refine ⟨2547959471697132920379581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1698639647798088613586387 2547959471697132920379581)
                    ·
                      refine ⟨955484801886424845142343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2547959471697132920379581 955484801886424845142343)
                      ·
                        rfl

theorem cell23_1860800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_1860800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860800 prefixEnd_1860800 := by exact prefixLift 1860800
  have htrace : WordTrace (prefixWord ++ tailWord_1860800) baseStart_1860800 baseEnd_1860800 := by
    simpa [prefixWord, tailWord_1860800, baseEnd_1860800] using wordTrace_append hprefix tailTrace_1860800
  have hstable : (prefixWord ++ tailWord_1860800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860800).length < 2 ^ (prefixWord ++ tailWord_1860800).sum := by decide
  have hdescent : baseEnd_1860800 < baseStart_1860800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860826 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_1860826 : Nat := 118140960795 + 1860826 * 2 ^ 59
def prefixEnd_1860826 : Nat := 4983230072969 + 3 ^ 40 * 1860826 * 2
def baseEnd_1860826 : Nat := 955498152383441743417223

theorem tailTrace_1860826 : CollatzResearch.WordTrace tailWord_1860826 prefixEnd_1860826 955498152383441743417223 := by
  unfold tailWord_1860826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16967474989138170156064583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45246599971035120416172221 16967474989138170156064583)
  ·
    refine ⟨25451212483707255234096875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16967474989138170156064583 25451212483707255234096875)
    ·
      refine ⟨38176818725560882851145313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25451212483707255234096875 38176818725560882851145313)
      ·
        refine ⟨28632614044170662138358985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38176818725560882851145313 28632614044170662138358985)
        ·
          refine ⟨21474460533127996603769239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28632614044170662138358985 21474460533127996603769239)
          ·
            refine ⟨32211690799691994905653859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21474460533127996603769239 32211690799691994905653859)
            ·
              refine ⟨48317536199537992358480789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32211690799691994905653859 48317536199537992358480789)
              ·
                refine ⟨2264884509353343391803787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48317536199537992358480789 2264884509353343391803787)
                ·
                  refine ⟨3397326764030015087705681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264884509353343391803787 3397326764030015087705681)
                  ·
                    refine ⟨2547995073022511315779261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3397326764030015087705681 2547995073022511315779261)
                    ·
                      refine ⟨955498152383441743417223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2547995073022511315779261 955498152383441743417223)
                      ·
                        rfl

theorem cell23_1860826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_1860826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860826 prefixEnd_1860826 := by exact prefixLift 1860826
  have htrace : WordTrace (prefixWord ++ tailWord_1860826) baseStart_1860826 baseEnd_1860826 := by
    simpa [prefixWord, tailWord_1860826, baseEnd_1860826] using wordTrace_append hprefix tailTrace_1860826
  have hstable : (prefixWord ++ tailWord_1860826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860826).length < 2 ^ (prefixWord ++ tailWord_1860826).sum := by decide
  have hdescent : baseEnd_1860826 < baseStart_1860826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860843 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 1, 2, 3]
def baseStart_1860843 : Nat := 118140960795 + 1860843 * 2 ^ 59
def prefixEnd_1860843 : Nat := 4983230072969 + 3 ^ 40 * 1860843 * 2
def baseEnd_1860843 : Nat := 955506881554568176904645

theorem tailTrace_1860843 : CollatzResearch.WordTrace tailWord_1860843 prefixEnd_1860843 955506881554568176904645 := by
  unfold tailWord_1860843
  simp only [CollatzResearch.WordTrace]
  refine ⟨67870519997491092527627183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45247013331660728351751455 67870519997491092527627183)
  ·
    refine ⟨101805779996236638791440775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67870519997491092527627183 101805779996236638791440775)
    ·
      refine ⟨152708669994354958187161163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101805779996236638791440775 152708669994354958187161163)
      ·
        refine ⟨229063004991532437280741745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152708669994354958187161163 229063004991532437280741745)
        ·
          refine ⟨171797253743649327960556309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229063004991532437280741745 171797253743649327960556309)
          ·
            refine ⟨8052996269233562248151077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171797253743649327960556309 8052996269233562248151077)
            ·
              refine ⟨1509936800481292921528327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8052996269233562248151077 1509936800481292921528327)
              ·
                refine ⟨2264905200721939382292491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509936800481292921528327 2264905200721939382292491)
                ·
                  refine ⟨3397357801082909073438737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264905200721939382292491 3397357801082909073438737)
                  ·
                    refine ⟨2548018350812181805079053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3397357801082909073438737 2548018350812181805079053)
                    ·
                      refine ⟨955506881554568176904645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2548018350812181805079053 955506881554568176904645)
                      ·
                        rfl

theorem cell23_1860843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 2, 3].length) (baseStart_1860843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860843 prefixEnd_1860843 := by exact prefixLift 1860843
  have htrace : WordTrace (prefixWord ++ tailWord_1860843) baseStart_1860843 baseEnd_1860843 := by
    simpa [prefixWord, tailWord_1860843, baseEnd_1860843] using wordTrace_append hprefix tailTrace_1860843
  have hstable : (prefixWord ++ tailWord_1860843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860843).length < 2 ^ (prefixWord ++ tailWord_1860843).sum := by decide
  have hdescent : baseEnd_1860843 < baseStart_1860843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860850 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_1860850 : Nat := 118140960795 + 1860850 * 2 ^ 59
def prefixEnd_1860850 : Nat := 4983230072969 + 3 ^ 40 * 1860850 * 2
def baseEnd_1860850 : Nat := 318503491973049883172371

theorem tailTrace_1860850 : CollatzResearch.WordTrace tailWord_1860850 prefixEnd_1860850 318503491973049883172371 := by
  unfold tailWord_1860850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16967693827116433180783001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45247183538977155148754669 16967693827116433180783001)
  ·
    refine ⟨12725770370337324885587251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16967693827116433180783001 12725770370337324885587251)
    ·
      refine ⟨19088655555505987328380877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12725770370337324885587251 19088655555505987328380877)
      ·
        refine ⟨7158245833314745248142829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19088655555505987328380877 7158245833314745248142829)
        ·
          refine ⟨2684342187493029468053561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7158245833314745248142829 2684342187493029468053561)
          ·
            refine ⟨2013256640619772101040171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2684342187493029468053561 2013256640619772101040171)
            ·
              refine ⟨3019884960929658151560257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013256640619772101040171 3019884960929658151560257)
              ·
                refine ⟨2264913720697243613670193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019884960929658151560257 2264913720697243613670193)
                ·
                  refine ⟨1698685290522932710252645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2264913720697243613670193 1698685290522932710252645)
                  ·
                    refine ⟨318503491973049883172371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698685290522932710252645 318503491973049883172371)
                    ·
                      rfl

theorem cell23_1860850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_1860850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860850 prefixEnd_1860850 := by exact prefixLift 1860850
  have htrace : WordTrace (prefixWord ++ tailWord_1860850) baseStart_1860850 baseEnd_1860850 := by
    simpa [prefixWord, tailWord_1860850, baseEnd_1860850] using wordTrace_append hprefix tailTrace_1860850
  have hstable : (prefixWord ++ tailWord_1860850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860850).length < 2 ^ (prefixWord ++ tailWord_1860850).sum := by decide
  have hdescent : baseEnd_1860850 < baseStart_1860850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860899 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1860899 : Nat := 118140960795 + 1860899 * 2 ^ 59
def prefixEnd_1860899 : Nat := 4983230072969 + 3 ^ 40 * 1860899 * 2
def baseEnd_1860899 : Nat := 955535636471219957804387

theorem tailTrace_1860899 : CollatzResearch.WordTrace tailWord_1860899 prefixEnd_1860899 955535636471219957804387 := by
  unfold tailWord_1860899
  simp only [CollatzResearch.WordTrace]
  refine ⟨67872562485288214091665751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45248374990192142727777167 67872562485288214091665751)
  ·
    refine ⟨101808843727932321137498627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67872562485288214091665751 101808843727932321137498627)
    ·
      refine ⟨152713265591898481706247941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101808843727932321137498627 152713265591898481706247941)
      ·
        refine ⟨28633737298480965319921489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152713265591898481706247941 28633737298480965319921489)
        ·
          refine ⟨21475302973860723989941117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28633737298480965319921489 21475302973860723989941117)
          ·
            refine ⟨8053238615197771496227919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21475302973860723989941117 8053238615197771496227919)
            ·
              refine ⟨12079857922796657244341879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053238615197771496227919 12079857922796657244341879)
              ·
                refine ⟨18119786884194985866512819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12079857922796657244341879 18119786884194985866512819)
                ·
                  refine ⟨27179680326292478799769229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18119786884194985866512819 27179680326292478799769229)
                  ·
                    refine ⟨10192380122359679549913461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27179680326292478799769229 10192380122359679549913461)
                    ·
                      refine ⟨955535636471219957804387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10192380122359679549913461 955535636471219957804387)
                      ·
                        rfl

theorem cell23_1860899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1860899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860899 prefixEnd_1860899 := by exact prefixLift 1860899
  have htrace : WordTrace (prefixWord ++ tailWord_1860899) baseStart_1860899 baseEnd_1860899 := by
    simpa [prefixWord, tailWord_1860899, baseEnd_1860899] using wordTrace_append hprefix tailTrace_1860899
  have hstable : (prefixWord ++ tailWord_1860899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860899).length < 2 ^ (prefixWord ++ tailWord_1860899).sum := by decide
  have hdescent : baseEnd_1860899 < baseStart_1860899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860916 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1860916 : Nat := 118140960795 + 1860916 * 2 ^ 59
def prefixEnd_1860916 : Nat := 4983230072969 + 3 ^ 40 * 1860916 * 2
def baseEnd_1860916 : Nat := 955544365642346391291809

theorem tailTrace_1860916 : CollatzResearch.WordTrace tailWord_1860916 prefixEnd_1860916 955544365642346391291809 := by
  unfold tailWord_1860916
  simp only [CollatzResearch.WordTrace]
  refine ⟨33936591263113312997517301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45248788350817750663356401 33936591263113312997517301)
  ·
    refine ⟨3181555430916873093517247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33936591263113312997517301 3181555430916873093517247)
    ·
      refine ⟨4772333146375309640275871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3181555430916873093517247 4772333146375309640275871)
      ·
        refine ⟨7158499719562964460413807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4772333146375309640275871 7158499719562964460413807)
        ·
          refine ⟨10737749579344446690620711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158499719562964460413807 10737749579344446690620711)
          ·
            refine ⟨16106624369016670035931067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10737749579344446690620711 16106624369016670035931067)
            ·
              refine ⟨24159936553525005053896601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16106624369016670035931067 24159936553525005053896601)
              ·
                refine ⟨18119952415143753790422451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24159936553525005053896601 18119952415143753790422451)
                ·
                  refine ⟨27179928622715630685633677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18119952415143753790422451 27179928622715630685633677)
                  ·
                    refine ⟨10192473233518361507112629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27179928622715630685633677 10192473233518361507112629)
                    ·
                      refine ⟨955544365642346391291809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10192473233518361507112629 955544365642346391291809)
                      ·
                        rfl

theorem cell23_1860916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1860916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860916 prefixEnd_1860916 := by exact prefixLift 1860916
  have htrace : WordTrace (prefixWord ++ tailWord_1860916) baseStart_1860916 baseEnd_1860916 := by
    simpa [prefixWord, tailWord_1860916, baseEnd_1860916] using wordTrace_append hprefix tailTrace_1860916
  have hstable : (prefixWord ++ tailWord_1860916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860916).length < 2 ^ (prefixWord ++ tailWord_1860916).sum := by decide
  have hdescent : baseEnd_1860916 < baseStart_1860916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860926 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1860926 : Nat := 118140960795 + 1860926 * 2 ^ 59
def prefixEnd_1860926 : Nat := 4983230072969 + 3 ^ 40 * 1860926 * 2
def baseEnd_1860926 : Nat := 955549500448891352166763

theorem tailTrace_1860926 : CollatzResearch.WordTrace tailWord_1860926 prefixEnd_1860926 955549500448891352166763 := by
  unfold tailWord_1860926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8484193407023799712862329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45249031504126931801932421 8484193407023799712862329)
  ·
    refine ⟨6363145055267849784646747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8484193407023799712862329 6363145055267849784646747)
    ·
      refine ⟨9544717582901774676970121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6363145055267849784646747 9544717582901774676970121)
      ·
        refine ⟨7158538187176331007727591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9544717582901774676970121 7158538187176331007727591)
        ·
          refine ⟨10737807280764496511591387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158538187176331007727591 10737807280764496511591387)
          ·
            refine ⟨16106710921146744767387081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10737807280764496511591387 16106710921146744767387081)
            ·
              refine ⟨12080033190860058575540311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16106710921146744767387081 12080033190860058575540311)
              ·
                refine ⟨18120049786290087863310467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12080033190860058575540311 18120049786290087863310467)
                ·
                  refine ⟨27180074679435131794965701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18120049786290087863310467 27180074679435131794965701)
                  ·
                    refine ⟨5096264002394087211556069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27180074679435131794965701 5096264002394087211556069)
                    ·
                      refine ⟨955549500448891352166763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5096264002394087211556069 955549500448891352166763)
                      ·
                        rfl

theorem cell23_1860926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1860926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860926 prefixEnd_1860926 := by exact prefixLift 1860926
  have htrace : WordTrace (prefixWord ++ tailWord_1860926) baseStart_1860926 baseEnd_1860926 := by
    simpa [prefixWord, tailWord_1860926, baseEnd_1860926] using wordTrace_append hprefix tailTrace_1860926
  have hstable : (prefixWord ++ tailWord_1860926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860926).length < 2 ^ (prefixWord ++ tailWord_1860926).sum := by decide
  have hdescent : baseEnd_1860926 < baseStart_1860926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860934 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1860934 : Nat := 118140960795 + 1860934 * 2 ^ 59
def prefixEnd_1860934 : Nat := 4983230072969 + 3 ^ 40 * 1860934 * 2
def baseEnd_1860934 : Nat := 955553608294127320866727

theorem tailTrace_1860934 : CollatzResearch.WordTrace tailWord_1860934 prefixEnd_1860934 955553608294127320866727 := by
  unfold tailWord_1860934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121057470005044220912183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45249226026774276712793237 2121057470005044220912183)
  ·
    refine ⟨3181586205007566331368275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2121057470005044220912183 3181586205007566331368275)
    ·
      refine ⟨4772379307511349497052413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3181586205007566331368275 4772379307511349497052413)
      ·
        refine ⟨1789642240316756061394655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4772379307511349497052413 1789642240316756061394655)
        ·
          refine ⟨2684463360475134092091983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789642240316756061394655 2684463360475134092091983)
          ·
            refine ⟨4026695040712701138137975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684463360475134092091983 4026695040712701138137975)
            ·
              refine ⟨6040042561069051707206963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026695040712701138137975 6040042561069051707206963)
              ·
                refine ⟨9060063841603577560810445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040042561069051707206963 9060063841603577560810445)
                ·
                  refine ⟨3397523940601341585303917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9060063841603577560810445 3397523940601341585303917)
                  ·
                    refine ⟨1274071477725503094488969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3397523940601341585303917 1274071477725503094488969)
                    ·
                      refine ⟨955553608294127320866727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274071477725503094488969 955553608294127320866727)
                      ·
                        rfl

theorem cell23_1860934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1860934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860934 prefixEnd_1860934 := by exact prefixLift 1860934
  have htrace : WordTrace (prefixWord ++ tailWord_1860934) baseStart_1860934 baseEnd_1860934 := by
    simpa [prefixWord, tailWord_1860934, baseEnd_1860934] using wordTrace_append hprefix tailTrace_1860934
  have hstable : (prefixWord ++ tailWord_1860934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860934).length < 2 ^ (prefixWord ++ tailWord_1860934).sum := by decide
  have hdescent : baseEnd_1860934 < baseStart_1860934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860946 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_1860946 : Nat := 118140960795 + 1860946 * 2 ^ 59
def prefixEnd_1860946 : Nat := 4983230072969 + 3 ^ 40 * 1860946 * 2
def baseEnd_1860946 : Nat := 955559770061981273916671

theorem tailTrace_1860946 : CollatzResearch.WordTrace tailWord_1860946 prefixEnd_1860946 955559770061981273916671 := by
  unfold tailWord_1860946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16968569179029485279656673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45249517810745294079084461 16968569179029485279656673)
  ·
    refine ⟨12726426884272113959742505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16968569179029485279656673 12726426884272113959742505)
    ·
      refine ⟨9544820163204085469806879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12726426884272113959742505 9544820163204085469806879)
      ·
        refine ⟨14317230244806128204710319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9544820163204085469806879 14317230244806128204710319)
        ·
          refine ⟨21475845367209192307065479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14317230244806128204710319 21475845367209192307065479)
          ·
            refine ⟨32213768050813788460598219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21475845367209192307065479 32213768050813788460598219)
            ·
              refine ⟨48320652076220682690897329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32213768050813788460598219 48320652076220682690897329)
              ·
                refine ⟨36240489057165512018172997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48320652076220682690897329 36240489057165512018172997)
                ·
                  refine ⟨6795091698218533503407437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36240489057165512018172997 6795091698218533503407437)
                  ·
                    refine ⟨2548159386831950063777789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6795091698218533503407437 2548159386831950063777789)
                    ·
                      refine ⟨955559770061981273916671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2548159386831950063777789 955559770061981273916671)
                      ·
                        rfl

theorem cell23_1860946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_1860946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860946 prefixEnd_1860946 := by exact prefixLift 1860946
  have htrace : WordTrace (prefixWord ++ tailWord_1860946) baseStart_1860946 baseEnd_1860946 := by
    simpa [prefixWord, tailWord_1860946, baseEnd_1860946] using wordTrace_append hprefix tailTrace_1860946
  have hstable : (prefixWord ++ tailWord_1860946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860946).length < 2 ^ (prefixWord ++ tailWord_1860946).sum := by decide
  have hdescent : baseEnd_1860946 < baseStart_1860946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860970 : List Nat := [3, 1, 3, 3, 2, 1, 1, 4, 5]
def baseStart_1860970 : Nat := 118140960795 + 1860970 * 2 ^ 59
def prefixEnd_1860970 : Nat := 4983230072969 + 3 ^ 40 * 1860970 * 2
def baseEnd_1860970 : Nat := 106174677066409908890729

theorem tailTrace_1860970 : CollatzResearch.WordTrace tailWord_1860970 prefixEnd_1860970 106174677066409908890729 := by
  unfold tailWord_1860970
  simp only [CollatzResearch.WordTrace]
  refine ⟨16968788017007748304375091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45250101378687328811666909 16968788017007748304375091)
  ·
    refine ⟨25453182025511622456562637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16968788017007748304375091 25453182025511622456562637)
    ·
      refine ⟨9544943259566858421210989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25453182025511622456562637 9544943259566858421210989)
      ·
        refine ⟨3579353722337571907954121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9544943259566858421210989 3579353722337571907954121)
        ·
          refine ⟨2684515291753178930965591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3579353722337571907954121 2684515291753178930965591)
          ·
            refine ⟨4026772937629768396448387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684515291753178930965591 4026772937629768396448387)
            ·
              refine ⟨6040159406444652594672581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026772937629768396448387 6040159406444652594672581)
              ·
                refine ⟨1132529888708372361501109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6040159406444652594672581 1132529888708372361501109)
                ·
                  refine ⟨106174677066409908890729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1132529888708372361501109 106174677066409908890729)
                  ·
                    rfl

theorem cell23_1860970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_1860970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860970 prefixEnd_1860970 := by exact prefixLift 1860970
  have htrace : WordTrace (prefixWord ++ tailWord_1860970) baseStart_1860970 baseEnd_1860970 := by
    simpa [prefixWord, tailWord_1860970, baseEnd_1860970] using wordTrace_append hprefix tailTrace_1860970
  have hstable : (prefixWord ++ tailWord_1860970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860970).length < 2 ^ (prefixWord ++ tailWord_1860970).sum := by decide
  have hdescent : baseEnd_1860970 < baseStart_1860970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860973 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_1860973 : Nat := 118140960795 + 1860973 * 2 ^ 59
def prefixEnd_1860973 : Nat := 4983230072969 + 3 ^ 40 * 1860973 * 2
def baseEnd_1860973 : Nat := 955573634039652668279047

theorem tailTrace_1860973 : CollatzResearch.WordTrace tailWord_1860973 prefixEnd_1860973 955573634039652668279047 := by
  unfold tailWord_1860973
  simp only [CollatzResearch.WordTrace]
  refine ⟨67875261487020124729859573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45250174324680083153239715 67875261487020124729859573)
  ·
    refine ⟨6363305764408136693424335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67875261487020124729859573 6363305764408136693424335)
    ·
      refine ⟨9544958646612205040136503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6363305764408136693424335 9544958646612205040136503)
      ·
        refine ⟨14317437969918307560204755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9544958646612205040136503 14317437969918307560204755)
        ·
          refine ⟨21476156954877461340307133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14317437969918307560204755 21476156954877461340307133)
          ·
            refine ⟨8053558858079048002615175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21476156954877461340307133 8053558858079048002615175)
            ·
              refine ⟨12080338287118572003922763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053558858079048002615175 12080338287118572003922763)
              ·
                refine ⟨18120507430677858005884145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12080338287118572003922763 18120507430677858005884145)
                ·
                  refine ⟨13590380573008393504413109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18120507430677858005884145 13590380573008393504413109)
                  ·
                    refine ⟨1274098178719536891038729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13590380573008393504413109 1274098178719536891038729)
                    ·
                      refine ⟨955573634039652668279047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274098178719536891038729 955573634039652668279047)
                      ·
                        rfl

theorem cell23_1860973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_1860973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1860973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1860973 prefixEnd_1860973 := by exact prefixLift 1860973
  have htrace : WordTrace (prefixWord ++ tailWord_1860973) baseStart_1860973 baseEnd_1860973 := by
    simpa [prefixWord, tailWord_1860973, baseEnd_1860973] using wordTrace_append hprefix tailTrace_1860973
  have hstable : (prefixWord ++ tailWord_1860973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860973).length < 2 ^ (prefixWord ++ tailWord_1860973).sum := by decide
  have hdescent : baseEnd_1860973 < baseStart_1860973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861009 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 10]
def baseStart_1861009 : Nat := 118140960795 + 1861009 * 2 ^ 59
def prefixEnd_1861009 : Nat := 4983230072969 + 3 ^ 40 * 1861009 * 2
def baseEnd_1861009 : Nat := 106176902149246058603209

theorem tailTrace_1861009 : CollatzResearch.WordTrace tailWord_1861009 prefixEnd_1861009 106176902149246058603209 := by
  unfold tailWord_1861009
  simp only [CollatzResearch.WordTrace]
  refine ⟨67876574514889702878170081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45251049676593135252113387 67876574514889702878170081)
  ·
    refine ⟨50907430886167277158627561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67876574514889702878170081 50907430886167277158627561)
    ·
      refine ⟨38180573164625457868970671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50907430886167277158627561 38180573164625457868970671)
      ·
        refine ⟨57270859746938186803456007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38180573164625457868970671 57270859746938186803456007)
        ·
          refine ⟨85906289620407280205184011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57270859746938186803456007 85906289620407280205184011)
          ·
            refine ⟨128859434430610920307776017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85906289620407280205184011 128859434430610920307776017)
            ·
              refine ⟨96644575822958190230832013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128859434430610920307776017 96644575822958190230832013)
              ·
                refine ⟨36241715933609321336562005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96644575822958190230832013 36241715933609321336562005)
                ·
                  refine ⟨106176902149246058603209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 36241715933609321336562005 106176902149246058603209)
                  ·
                    rfl

theorem cell23_1861009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 10].length) (baseStart_1861009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861009 prefixEnd_1861009 := by exact prefixLift 1861009
  have htrace : WordTrace (prefixWord ++ tailWord_1861009) baseStart_1861009 baseEnd_1861009 := by
    simpa [prefixWord, tailWord_1861009, baseEnd_1861009] using wordTrace_append hprefix tailTrace_1861009
  have hstable : (prefixWord ++ tailWord_1861009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861009).length < 2 ^ (prefixWord ++ tailWord_1861009).sum := by decide
  have hdescent : baseEnd_1861009 < baseStart_1861009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861056 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 3, 5]
def baseStart_1861056 : Nat := 118140960795 + 1861056 * 2 ^ 59
def prefixEnd_1861056 : Nat := 4983230072969 + 3 ^ 40 * 1861056 * 2
def baseEnd_1861056 : Nat := 318538750977991947847055

theorem tailTrace_1861056 : CollatzResearch.WordTrace tailWord_1861056 prefixEnd_1861056 318538750977991947847055 := by
  unfold tailWord_1861056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33939144372859714952565511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45252192497146286603420681 33939144372859714952565511)
  ·
    refine ⟨50908716559289572428848267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33939144372859714952565511 50908716559289572428848267)
    ·
      refine ⟨76363074838934358643272401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50908716559289572428848267 76363074838934358643272401)
      ·
        refine ⟨57272306129200768982454301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76363074838934358643272401 57272306129200768982454301)
        ·
          refine ⟨21477114798450288368420363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57272306129200768982454301 21477114798450288368420363)
          ·
            refine ⟨32215672197675432552630545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21477114798450288368420363 32215672197675432552630545)
            ·
              refine ⟨24161754148256574414472909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32215672197675432552630545 24161754148256574414472909)
              ·
                refine ⟨9060657805596215405427341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24161754148256574414472909 9060657805596215405427341)
                ·
                  refine ⟨3397746677098580777035253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9060657805596215405427341 3397746677098580777035253)
                  ·
                    refine ⟨318538750977991947847055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3397746677098580777035253 318538750977991947847055)
                    ·
                      rfl

theorem cell23_1861056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_1861056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861056 prefixEnd_1861056 := by exact prefixLift 1861056
  have htrace : WordTrace (prefixWord ++ tailWord_1861056) baseStart_1861056 baseEnd_1861056 := by
    simpa [prefixWord, tailWord_1861056, baseEnd_1861056] using wordTrace_append hprefix tailTrace_1861056
  have hstable : (prefixWord ++ tailWord_1861056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861056).length < 2 ^ (prefixWord ++ tailWord_1861056).sum := by decide
  have hdescent : baseEnd_1861056 < baseStart_1861056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861063 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_1861063 : Nat := 118140960795 + 1861063 * 2 ^ 59
def prefixEnd_1861063 : Nat := 4983230072969 + 3 ^ 40 * 1861063 * 2
def baseEnd_1861063 : Nat := 955619847298557316153633

theorem tailTrace_1861063 : CollatzResearch.WordTrace tailWord_1861063 prefixEnd_1861063 955619847298557316153633 := by
  unfold tailWord_1861063
  simp only [CollatzResearch.WordTrace]
  refine ⟨67878544056694070100635843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45252362704462713400423895 67878544056694070100635843)
  ·
    refine ⟨101817816085041105150953765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67878544056694070100635843 101817816085041105150953765)
    ·
      refine ⟨19090840515945207215803831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101817816085041105150953765 19090840515945207215803831)
      ·
        refine ⟨28636260773917810823705747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19090840515945207215803831 28636260773917810823705747)
        ·
          refine ⟨42954391160876716235558621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28636260773917810823705747 42954391160876716235558621)
          ·
            refine ⟨16107896685328768588334483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42954391160876716235558621 16107896685328768588334483)
            ·
              refine ⟨24161845027993152882501725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16107896685328768588334483 24161845027993152882501725)
              ·
                refine ⟨9060691885497432330938147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24161845027993152882501725 9060691885497432330938147)
                ·
                  refine ⟨13591037828246148496407221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060691885497432330938147 13591037828246148496407221)
                  ·
                    refine ⟨1274159796398076421538177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13591037828246148496407221 1274159796398076421538177)
                    ·
                      refine ⟨955619847298557316153633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274159796398076421538177 955619847298557316153633)
                      ·
                        rfl

theorem cell23_1861063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_1861063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861063 prefixEnd_1861063 := by exact prefixLift 1861063
  have htrace : WordTrace (prefixWord ++ tailWord_1861063) baseStart_1861063 baseEnd_1861063 := by
    simpa [prefixWord, tailWord_1861063, baseEnd_1861063] using wordTrace_append hprefix tailTrace_1861063
  have hstable : (prefixWord ++ tailWord_1861063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861063).length < 2 ^ (prefixWord ++ tailWord_1861063).sum := by decide
  have hdescent : baseEnd_1861063 < baseStart_1861063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861110 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1861110 : Nat := 118140960795 + 1861110 * 2 ^ 59
def prefixEnd_1861110 : Nat := 4983230072969 + 3 ^ 40 * 1861110 * 2
def baseEnd_1861110 : Nat := 955643980889318632265917

theorem tailTrace_1861110 : CollatzResearch.WordTrace tailWord_1861110 prefixEnd_1861110 955643980889318632265917 := by
  unfold tailWord_1861110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242516142970237320474799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45253505525015864751731189 4242516142970237320474799)
  ·
    refine ⟨6363774214455355980712199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4242516142970237320474799 6363774214455355980712199)
    ·
      refine ⟨9545661321683033971068299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6363774214455355980712199 9545661321683033971068299)
      ·
        refine ⟨14318491982524550956602449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9545661321683033971068299 14318491982524550956602449)
        ·
          refine ⟨10738868986893413217451837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14318491982524550956602449 10738868986893413217451837)
          ·
            refine ⟨4027075870085029956544439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10738868986893413217451837 4027075870085029956544439)
            ·
              refine ⟨6040613805127544934816659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027075870085029956544439 6040613805127544934816659)
              ·
                refine ⟨9060920707691317402224989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040613805127544934816659 9060920707691317402224989)
                ·
                  refine ⟨3397845265384244025834371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9060920707691317402224989 3397845265384244025834371)
                  ·
                    refine ⟨5096767898076366038751557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3397845265384244025834371 5096767898076366038751557)
                    ·
                      refine ⟨955643980889318632265917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5096767898076366038751557 955643980889318632265917)
                      ·
                        rfl

theorem cell23_1861110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1861110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861110 prefixEnd_1861110 := by exact prefixLift 1861110
  have htrace : WordTrace (prefixWord ++ tailWord_1861110) baseStart_1861110 baseEnd_1861110 := by
    simpa [prefixWord, tailWord_1861110, baseEnd_1861110] using wordTrace_append hprefix tailTrace_1861110
  have hstable : (prefixWord ++ tailWord_1861110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861110).length < 2 ^ (prefixWord ++ tailWord_1861110).sum := by decide
  have hdescent : baseEnd_1861110 < baseStart_1861110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861116 : List Nat := [2, 2, 2, 1, 2, 1, 4, 9]
def baseStart_1861116 : Nat := 118140960795 + 1861116 * 2 ^ 59
def prefixEnd_1861116 : Nat := 4983230072969 + 3 ^ 40 * 1861116 * 2
def baseEnd_1861116 : Nat := 35394335621231318844107

theorem tailTrace_1861116 : CollatzResearch.WordTrace tailWord_1861116 prefixEnd_1861116 35394335621231318844107 := by
  unfold tailWord_1861116
  simp only [CollatzResearch.WordTrace]
  refine ⟨33940238562751030076157601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45253651417001373434876801 33940238562751030076157601)
  ·
    refine ⟨25455178922063272557118201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33940238562751030076157601 25455178922063272557118201)
    ·
      refine ⟨19091384191547454417838651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25455178922063272557118201 19091384191547454417838651)
      ·
        refine ⟨28637076287321181626757977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19091384191547454417838651 28637076287321181626757977)
        ·
          refine ⟨21477807215490886220068483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28637076287321181626757977 21477807215490886220068483)
          ·
            refine ⟨32216710823236329330102725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21477807215490886220068483 32216710823236329330102725)
            ·
              refine ⟨6040633279356811749394261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32216710823236329330102725 6040633279356811749394261)
              ·
                refine ⟨35394335621231318844107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6040633279356811749394261 35394335621231318844107)
                ·
                  rfl

theorem cell23_1861116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 9].length) (baseStart_1861116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861116 prefixEnd_1861116 := by exact prefixLift 1861116
  have htrace : WordTrace (prefixWord ++ tailWord_1861116) baseStart_1861116 baseEnd_1861116 := by
    simpa [prefixWord, tailWord_1861116, baseEnd_1861116] using wordTrace_append hprefix tailTrace_1861116
  have hstable : (prefixWord ++ tailWord_1861116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861116).length < 2 ^ (prefixWord ++ tailWord_1861116).sum := by decide
  have hdescent : baseEnd_1861116 < baseStart_1861116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861127 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_1861127 : Nat := 118140960795 + 1861127 * 2 ^ 59
def prefixEnd_1861127 : Nat := 4983230072969 + 3 ^ 40 * 1861127 * 2
def baseEnd_1861127 : Nat := 955652710060445065753339

theorem tailTrace_1861127 : CollatzResearch.WordTrace tailWord_1861127 prefixEnd_1861127 955652710060445065753339 := by
  unfold tailWord_1861127
  simp only [CollatzResearch.WordTrace]
  refine ⟨67880878328462209030965635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45253918885641472687310423 67880878328462209030965635)
  ·
    refine ⟨101821317492693313546448453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67880878328462209030965635 101821317492693313546448453)
    ·
      refine ⟨19091497029879996289959085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101821317492693313546448453 19091497029879996289959085)
      ·
        refine ⟨7159311386204998608734657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19091497029879996289959085 7159311386204998608734657)
        ·
          refine ⟨5369483539653748956550993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7159311386204998608734657 5369483539653748956550993)
          ·
            refine ⟨4027112654740311717413245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5369483539653748956550993 4027112654740311717413245)
            ·
              refine ⟨1510167245527616894029967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4027112654740311717413245 1510167245527616894029967)
              ·
                refine ⟨2265250868291425341044951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510167245527616894029967 2265250868291425341044951)
                ·
                  refine ⟨3397876302437138011567427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265250868291425341044951 3397876302437138011567427)
                  ·
                    refine ⟨5096814453655707017351141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3397876302437138011567427 5096814453655707017351141)
                    ·
                      refine ⟨955652710060445065753339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5096814453655707017351141 955652710060445065753339)
                      ·
                        rfl

theorem cell23_1861127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_1861127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861127 prefixEnd_1861127 := by exact prefixLift 1861127
  have htrace : WordTrace (prefixWord ++ tailWord_1861127) baseStart_1861127 baseEnd_1861127 := by
    simpa [prefixWord, tailWord_1861127, baseEnd_1861127] using wordTrace_append hprefix tailTrace_1861127
  have hstable : (prefixWord ++ tailWord_1861127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861127).length < 2 ^ (prefixWord ++ tailWord_1861127).sum := by decide
  have hdescent : baseEnd_1861127 < baseStart_1861127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861130 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_1861130 : Nat := 118140960795 + 1861130 * 2 ^ 59
def prefixEnd_1861130 : Nat := 4983230072969 + 3 ^ 40 * 1861130 * 2
def baseEnd_1861130 : Nat := 955654250502408554015825

theorem tailTrace_1861130 : CollatzResearch.WordTrace tailWord_1861130 prefixEnd_1861130 955654250502408554015825 := by
  unfold tailWord_1861130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16970246936862835135831211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45253991831634227028883229 16970246936862835135831211)
  ·
    refine ⟨25455370405294252703746817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16970246936862835135831211 25455370405294252703746817)
    ·
      refine ⟨19091527803970689527810113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25455370405294252703746817 19091527803970689527810113)
      ·
        refine ⟨14318645852978017145857585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19091527803970689527810113 14318645852978017145857585)
        ·
          refine ⟨10738984389733512859393189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14318645852978017145857585 10738984389733512859393189)
          ·
            refine ⟨2013559573075033661136223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10738984389733512859393189 2013559573075033661136223)
            ·
              refine ⟨3020339359612550491704335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013559573075033661136223 3020339359612550491704335)
              ·
                refine ⟨4530509039418825737556503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020339359612550491704335 4530509039418825737556503)
                ·
                  refine ⟨6795763559128238606334755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530509039418825737556503 6795763559128238606334755)
                  ·
                    refine ⟨10193645338692357909502133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6795763559128238606334755 10193645338692357909502133)
                    ·
                      refine ⟨955654250502408554015825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10193645338692357909502133 955654250502408554015825)
                      ·
                        rfl

theorem cell23_1861130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_1861130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861130 prefixEnd_1861130 := by exact prefixLift 1861130
  have htrace : WordTrace (prefixWord ++ tailWord_1861130) baseStart_1861130 baseEnd_1861130 := by
    simpa [prefixWord, tailWord_1861130, baseEnd_1861130] using wordTrace_append hprefix tailTrace_1861130
  have hstable : (prefixWord ++ tailWord_1861130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861130).length < 2 ^ (prefixWord ++ tailWord_1861130).sum := by decide
  have hdescent : baseEnd_1861130 < baseStart_1861130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861181 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_1861181 : Nat := 118140960795 + 1861181 * 2 ^ 59
def prefixEnd_1861181 : Nat := 4983230072969 + 3 ^ 40 * 1861181 * 2
def baseEnd_1861181 : Nat := 955680438015787854478091

theorem tailTrace_1861181 : CollatzResearch.WordTrace tailWord_1861181 prefixEnd_1861181 955680438015787854478091 := by
  unfold tailWord_1861181
  simp only [CollatzResearch.WordTrace]
  refine ⟨67882847870266576253431397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45255231913511050835620931 67882847870266576253431397)
  ·
    refine ⟨12728033975674983047518387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67882847870266576253431397 12728033975674983047518387)
    ·
      refine ⟨19092050963512474571277581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12728033975674983047518387 19092050963512474571277581)
      ·
        refine ⟨7159519111317177964229093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19092050963512474571277581 7159519111317177964229093)
        ·
          refine ⟨1342409833371970868292955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7159519111317177964229093 1342409833371970868292955)
          ·
            refine ⟨2013614750057956302439433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342409833371970868292955 2013614750057956302439433)
            ·
              refine ⟨1510211062543467226829575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2013614750057956302439433 1510211062543467226829575)
              ·
                refine ⟨2265316593815200840244363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510211062543467226829575 2265316593815200840244363)
                ·
                  refine ⟨3397974890722801260366545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265316593815200840244363 3397974890722801260366545)
                  ·
                    refine ⟨2548481168042100945274909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3397974890722801260366545 2548481168042100945274909)
                    ·
                      refine ⟨955680438015787854478091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2548481168042100945274909 955680438015787854478091)
                      ·
                        rfl

theorem cell23_1861181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_1861181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861181 prefixEnd_1861181 := by exact prefixLift 1861181
  have htrace : WordTrace (prefixWord ++ tailWord_1861181) baseStart_1861181 baseEnd_1861181 := by
    simpa [prefixWord, tailWord_1861181, baseEnd_1861181] using wordTrace_append hprefix tailTrace_1861181
  have hstable : (prefixWord ++ tailWord_1861181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861181).length < 2 ^ (prefixWord ++ tailWord_1861181).sum := by decide
  have hdescent : baseEnd_1861181 < baseStart_1861181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861223 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 7]
def baseStart_1861223 : Nat := 118140960795 + 1861223 * 2 ^ 59
def prefixEnd_1861223 : Nat := 4983230072969 + 3 ^ 40 * 1861223 * 2
def baseEnd_1861223 : Nat := 106189111578141854461433

theorem tailTrace_1861223 : CollatzResearch.WordTrace tailWord_1861223 prefixEnd_1861223 106189111578141854461433 := by
  unfold tailWord_1861223
  simp only [CollatzResearch.WordTrace]
  refine ⟨67884379736114417426460323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45256253157409611617640215 67884379736114417426460323)
  ·
    refine ⟨101826569604171626139690485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67884379736114417426460323 101826569604171626139690485)
    ·
      refine ⟨9546240900391089950595983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101826569604171626139690485 9546240900391089950595983)
      ·
        refine ⟨14319361350586634925893975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9546240900391089950595983 14319361350586634925893975)
        ·
          refine ⟨21479042025879952388840963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14319361350586634925893975 21479042025879952388840963)
          ·
            refine ⟨32218563038819928583261445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21479042025879952388840963 32218563038819928583261445)
            ·
              refine ⟨6040980569778736609361521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32218563038819928583261445 6040980569778736609361521)
              ·
                refine ⟨4530735427334052457021141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6040980569778736609361521 4530735427334052457021141)
                ·
                  refine ⟨106189111578141854461433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4530735427334052457021141 106189111578141854461433)
                  ·
                    rfl

theorem cell23_1861223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 7].length) (baseStart_1861223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861223 prefixEnd_1861223 := by exact prefixLift 1861223
  have htrace : WordTrace (prefixWord ++ tailWord_1861223) baseStart_1861223 baseEnd_1861223 := by
    simpa [prefixWord, tailWord_1861223, baseEnd_1861223] using wordTrace_append hprefix tailTrace_1861223
  have hstable : (prefixWord ++ tailWord_1861223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861223).length < 2 ^ (prefixWord ++ tailWord_1861223).sum := by decide
  have hdescent : baseEnd_1861223 < baseStart_1861223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861233 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_1861233 : Nat := 118140960795 + 1861233 * 2 ^ 59
def prefixEnd_1861233 : Nat := 4983230072969 + 3 ^ 40 * 1861233 * 2
def baseEnd_1861233 : Nat := 955707139009821651027851

theorem tailTrace_1861233 : CollatzResearch.WordTrace tailWord_1861233 prefixEnd_1861233 955707139009821651027851 := by
  unfold tailWord_1861233
  simp only [CollatzResearch.WordTrace]
  refine ⟨67884744466078189134324353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45256496310718792756216235 67884744466078189134324353)
  ·
    refine ⟨50913558349558641850743265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67884744466078189134324353 50913558349558641850743265)
    ·
      refine ⟨38185168762168981388057449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50913558349558641850743265 38185168762168981388057449)
      ·
        refine ⟨28638876571626736041043087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38185168762168981388057449 28638876571626736041043087)
        ·
          refine ⟨42958314857440104061564631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28638876571626736041043087 42958314857440104061564631)
          ·
            refine ⟨64437472286160156092346947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42958314857440104061564631 64437472286160156092346947)
            ·
              refine ⟨96656208429240234138520421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64437472286160156092346947 96656208429240234138520421)
              ·
                refine ⟨18123039080482543900972579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96656208429240234138520421 18123039080482543900972579)
                ·
                  refine ⟨27184558620723815851458869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18123039080482543900972579 27184558620723815851458869)
                  ·
                    refine ⟨2548552370692857736074269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27184558620723815851458869 2548552370692857736074269)
                    ·
                      refine ⟨955707139009821651027851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2548552370692857736074269 955707139009821651027851)
                      ·
                        rfl

theorem cell23_1861233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_1861233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861233 prefixEnd_1861233 := by exact prefixLift 1861233
  have htrace : WordTrace (prefixWord ++ tailWord_1861233) baseStart_1861233 baseEnd_1861233 := by
    simpa [prefixWord, tailWord_1861233, baseEnd_1861233] using wordTrace_append hprefix tailTrace_1861233
  have hstable : (prefixWord ++ tailWord_1861233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861233).length < 2 ^ (prefixWord ++ tailWord_1861233).sum := by decide
  have hdescent : baseEnd_1861233 < baseStart_1861233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861260 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 2, 5, 2]
def baseStart_1861260 : Nat := 118140960795 + 1861260 * 2 ^ 59
def prefixEnd_1861260 : Nat := 4983230072969 + 3 ^ 40 * 1861260 * 2
def baseEnd_1861260 : Nat := 955721002987493045390227

theorem tailTrace_1861260 : CollatzResearch.WordTrace tailWord_1861260 prefixEnd_1861260 955721002987493045390227 := by
  unfold tailWord_1861260
  simp only [CollatzResearch.WordTrace]
  refine ⟨33942864618490186372778617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45257152824653581830371489 33942864618490186372778617)
  ·
    refine ⟨25457148463867639779583963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33942864618490186372778617 25457148463867639779583963)
    ·
      refine ⟨38185722695801459669375945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25457148463867639779583963 38185722695801459669375945)
      ·
        refine ⟨28639292021851094752031959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38185722695801459669375945 28639292021851094752031959)
        ·
          refine ⟨42958938032776642128047939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28639292021851094752031959 42958938032776642128047939)
          ·
            refine ⟨64438407049164963192071909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42958938032776642128047939 64438407049164963192071909)
            ·
              refine ⟨12082201321718430598513483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64438407049164963192071909 12082201321718430598513483)
              ·
                refine ⟨18123301982577645897770225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12082201321718430598513483 18123301982577645897770225)
                ·
                  refine ⟨13592476486933234423327669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18123301982577645897770225 13592476486933234423327669)
                  ·
                    refine ⟨1274294670649990727186969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13592476486933234423327669 1274294670649990727186969)
                    ·
                      refine ⟨955721002987493045390227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274294670649990727186969 955721002987493045390227)
                      ·
                        rfl

theorem cell23_1861260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_1861260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861260 prefixEnd_1861260 := by exact prefixLift 1861260
  have htrace : WordTrace (prefixWord ++ tailWord_1861260) baseStart_1861260 baseEnd_1861260 := by
    simpa [prefixWord, tailWord_1861260, baseEnd_1861260] using wordTrace_append hprefix tailTrace_1861260
  have hstable : (prefixWord ++ tailWord_1861260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861260).length < 2 ^ (prefixWord ++ tailWord_1861260).sum := by decide
  have hdescent : baseEnd_1861260 < baseStart_1861260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861273 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_1861273 : Nat := 118140960795 + 1861273 * 2 ^ 59
def prefixEnd_1861273 : Nat := 4983230072969 + 3 ^ 40 * 1861273 * 2
def baseEnd_1861273 : Nat := 955727678236001494527667

theorem tailTrace_1861273 : CollatzResearch.WordTrace tailWord_1861273 prefixEnd_1861273 955727678236001494527667 := by
  unfold tailWord_1861273
  simp only [CollatzResearch.WordTrace]
  refine ⟨67886203385933275965780473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45257468923955517310520315 67886203385933275965780473)
  ·
    refine ⟨50914652539449956974335355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67886203385933275965780473 50914652539449956974335355)
    ·
      refine ⟨76371978809174935461503033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50914652539449956974335355 76371978809174935461503033)
      ·
        refine ⟨57278984106881201596127275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76371978809174935461503033 57278984106881201596127275)
        ·
          refine ⟨85918476160321802394190913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57278984106881201596127275 85918476160321802394190913)
          ·
            refine ⟨64438857120241351795643185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85918476160321802394190913 64438857120241351795643185)
            ·
              refine ⟨48329142840181013846732389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64438857120241351795643185 48329142840181013846732389)
              ·
                refine ⟨9061714282533940096262323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48329142840181013846732389 9061714282533940096262323)
                ·
                  refine ⟨13592571423800910144393485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9061714282533940096262323 13592571423800910144393485)
                  ·
                    refine ⟨5097214283925341304147557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13592571423800910144393485 5097214283925341304147557)
                    ·
                      refine ⟨955727678236001494527667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5097214283925341304147557 955727678236001494527667)
                      ·
                        rfl

theorem cell23_1861273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_1861273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861273 prefixEnd_1861273 := by exact prefixLift 1861273
  have htrace : WordTrace (prefixWord ++ tailWord_1861273) baseStart_1861273 baseEnd_1861273 := by
    simpa [prefixWord, tailWord_1861273, baseEnd_1861273] using wordTrace_append hprefix tailTrace_1861273
  have hstable : (prefixWord ++ tailWord_1861273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861273).length < 2 ^ (prefixWord ++ tailWord_1861273).sum := by decide
  have hdescent : baseEnd_1861273 < baseStart_1861273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861317 : List Nat := [1, 3, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_1861317 : Nat := 118140960795 + 1861317 * 2 ^ 59
def prefixEnd_1861317 : Nat := 4983230072969 + 3 ^ 40 * 1861317 * 2
def baseEnd_1861317 : Nat := 318583423794933107459155

theorem tailTrace_1861317 : CollatzResearch.WordTrace tailWord_1861317 prefixEnd_1861317 318583423794933107459155 := by
  unfold tailWord_1861317
  simp only [CollatzResearch.WordTrace]
  refine ⟨67887808197773871480382205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45258538798515914320254803 67887808197773871480382205)
  ·
    refine ⟨25457928074165201805143327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67887808197773871480382205 25457928074165201805143327)
    ·
      refine ⟨38186892111247802707714991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25457928074165201805143327 38186892111247802707714991)
      ·
        refine ⟨57280338166871704061572487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38186892111247802707714991 57280338166871704061572487)
        ·
          refine ⟨85920507250307556092358731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57280338166871704061572487 85920507250307556092358731)
          ·
            refine ⟨128880760875461334138538097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85920507250307556092358731 128880760875461334138538097)
            ·
              refine ⟨96660570656596000603903573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128880760875461334138538097 96660570656596000603903573)
              ·
                refine ⟨1132741062381984382076995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 96660570656596000603903573 1132741062381984382076995)
                ·
                  refine ⟨1699111593572976573115493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132741062381984382076995 1699111593572976573115493)
                  ·
                    refine ⟨318583423794933107459155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1699111593572976573115493 318583423794933107459155)
                    ·
                      rfl

theorem cell23_1861317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_1861317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861317 prefixEnd_1861317 := by exact prefixLift 1861317
  have htrace : WordTrace (prefixWord ++ tailWord_1861317) baseStart_1861317 baseEnd_1861317 := by
    simpa [prefixWord, tailWord_1861317, baseEnd_1861317] using wordTrace_append hprefix tailTrace_1861317
  have hstable : (prefixWord ++ tailWord_1861317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861317).length < 2 ^ (prefixWord ++ tailWord_1861317).sum := by decide
  have hdescent : baseEnd_1861317 < baseStart_1861317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861324 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 2, 4, 2]
def baseStart_1861324 : Nat := 118140960795 + 1861324 * 2 ^ 59
def prefixEnd_1861324 : Nat := 4983230072969 + 3 ^ 40 * 1861324 * 2
def baseEnd_1861324 : Nat := 955753865749380794989933

theorem tailTrace_1861324 : CollatzResearch.WordTrace tailWord_1861324 prefixEnd_1861324 955753865749380794989933 := by
  unfold tailWord_1861324
  simp only [CollatzResearch.WordTrace]
  refine ⟨33944031754374255837943513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45258709005832341117258017 33944031754374255837943513)
  ·
    refine ⟨25458023815780691878457635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33944031754374255837943513 25458023815780691878457635)
    ·
      refine ⟨38187035723671037817686453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25458023815780691878457635 38187035723671037817686453)
      ·
        refine ⟨3580034599094159795408105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38187035723671037817686453 3580034599094159795408105)
        ·
          refine ⟨2685025949320619846556079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580034599094159795408105 2685025949320619846556079)
          ·
            refine ⟨4027538923980929769834119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685025949320619846556079 4027538923980929769834119)
            ·
              refine ⟨6041308385971394654751179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027538923980929769834119 6041308385971394654751179)
              ·
                refine ⟨9061962578957091982126769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041308385971394654751179 9061962578957091982126769)
                ·
                  refine ⟨6796471934217818986595077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9061962578957091982126769 6796471934217818986595077)
                  ·
                    refine ⟨1274338487665841059986577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6796471934217818986595077 1274338487665841059986577)
                    ·
                      refine ⟨955753865749380794989933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274338487665841059986577 955753865749380794989933)
                      ·
                        rfl

theorem cell23_1861324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_1861324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861324 prefixEnd_1861324 := by exact prefixLift 1861324
  have htrace : WordTrace (prefixWord ++ tailWord_1861324) baseStart_1861324 baseEnd_1861324 := by
    simpa [prefixWord, tailWord_1861324, baseEnd_1861324] using wordTrace_append hprefix tailTrace_1861324
  have hstable : (prefixWord ++ tailWord_1861324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861324).length < 2 ^ (prefixWord ++ tailWord_1861324).sum := by decide
  have hdescent : baseEnd_1861324 < baseStart_1861324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861341 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1861341 : Nat := 118140960795 + 1861341 * 2 ^ 59
def prefixEnd_1861341 : Nat := 4983230072969 + 3 ^ 40 * 1861341 * 2
def baseEnd_1861341 : Nat := 955762594920507228477355

theorem tailTrace_1861341 : CollatzResearch.WordTrace tailWord_1861341 prefixEnd_1861341 955762594920507228477355 := by
  unfold tailWord_1861341
  simp only [CollatzResearch.WordTrace]
  refine ⟨67888683549686923579255877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45259122366457949052837251 67888683549686923579255877)
  ·
    refine ⟨12729128165566298171110477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67888683549686923579255877 12729128165566298171110477)
    ·
      refine ⟨4773423062087361814166429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12729128165566298171110477 4773423062087361814166429)
      ·
        refine ⟨1790033648282760680312411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4773423062087361814166429 1790033648282760680312411)
        ·
          refine ⟨2685050472424141020468617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790033648282760680312411 2685050472424141020468617)
          ·
            refine ⟨2013787854318105765351463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2685050472424141020468617 2013787854318105765351463)
            ·
              refine ⟨3020681781477158648027195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013787854318105765351463 3020681781477158648027195)
              ·
                refine ⟨4531022672215737972040793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020681781477158648027195 4531022672215737972040793)
                ·
                  refine ⟨3398267004161803479030595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4531022672215737972040793 3398267004161803479030595)
                  ·
                    refine ⟨5097400506242705218545893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3398267004161803479030595 5097400506242705218545893)
                    ·
                      refine ⟨955762594920507228477355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5097400506242705218545893 955762594920507228477355)
                      ·
                        rfl

theorem cell23_1861341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1861341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861341 prefixEnd_1861341 := by exact prefixLift 1861341
  have htrace : WordTrace (prefixWord ++ tailWord_1861341) baseStart_1861341 baseEnd_1861341 := by
    simpa [prefixWord, tailWord_1861341, baseEnd_1861341] using wordTrace_append hprefix tailTrace_1861341
  have hstable : (prefixWord ++ tailWord_1861341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861341).length < 2 ^ (prefixWord ++ tailWord_1861341).sum := by decide
  have hdescent : baseEnd_1861341 < baseStart_1861341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861353 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_1861353 : Nat := 118140960795 + 1861353 * 2 ^ 59
def prefixEnd_1861353 : Nat := 4983230072969 + 3 ^ 40 * 1861353 * 2
def baseEnd_1861353 : Nat := 955768756688361181527299

theorem tailTrace_1861353 : CollatzResearch.WordTrace tailWord_1861353 prefixEnd_1861353 955768756688361181527299 := by
  unfold tailWord_1861353
  simp only [CollatzResearch.WordTrace]
  refine ⟨67889121225643449628692713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45259414150428966419128475 67889121225643449628692713)
  ·
    refine ⟨50916840919232587221519535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67889121225643449628692713 50916840919232587221519535)
    ·
      refine ⟨76375261378848880832279303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50916840919232587221519535 76375261378848880832279303)
      ·
        refine ⟨114562892068273321248418955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76375261378848880832279303 114562892068273321248418955)
        ·
          refine ⟨171844338102409981872628433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114562892068273321248418955 171844338102409981872628433)
          ·
            refine ⟨128883253576807486404471325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171844338102409981872628433 128883253576807486404471325)
            ·
              refine ⟨48331220091302807401676747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128883253576807486404471325 48331220091302807401676747)
              ·
                refine ⟨72496830136954211102515121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48331220091302807401676747 72496830136954211102515121)
                ·
                  refine ⟨54372622602715658326886341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72496830136954211102515121 54372622602715658326886341)
                  ·
                    refine ⟨10194866738009185936291189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54372622602715658326886341 10194866738009185936291189)
                    ·
                      refine ⟨955768756688361181527299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10194866738009185936291189 955768756688361181527299)
                      ·
                        rfl

theorem cell23_1861353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_1861353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861353 prefixEnd_1861353 := by exact prefixLift 1861353
  have htrace : WordTrace (prefixWord ++ tailWord_1861353) baseStart_1861353 baseEnd_1861353 := by
    simpa [prefixWord, tailWord_1861353, baseEnd_1861353] using wordTrace_append hprefix tailTrace_1861353
  have hstable : (prefixWord ++ tailWord_1861353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861353).length < 2 ^ (prefixWord ++ tailWord_1861353).sum := by decide
  have hdescent : baseEnd_1861353 < baseStart_1861353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861364 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1861364 : Nat := 118140960795 + 1861364 * 2 ^ 59
def prefixEnd_1861364 : Nat := 4983230072969 + 3 ^ 40 * 1861364 * 2
def baseEnd_1861364 : Nat := 106197156108395626498861

theorem tailTrace_1861364 : CollatzResearch.WordTrace tailWord_1861364 prefixEnd_1861364 106197156108395626498861 := by
  unfold tailWord_1861364
  simp only [CollatzResearch.WordTrace]
  refine ⟨33944761214301799253671573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45259681619069065671562097 33944761214301799253671573)
  ·
    refine ⟨1591160681920396840015855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33944761214301799253671573 1591160681920396840015855)
    ·
      refine ⟨2386741022880595260023783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591160681920396840015855 2386741022880595260023783)
      ·
        refine ⟨3580111534320892890035675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386741022880595260023783 3580111534320892890035675)
        ·
          refine ⟨5370167301481339335053513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580111534320892890035675 5370167301481339335053513)
          ·
            refine ⟨4027625476111004501290135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5370167301481339335053513 4027625476111004501290135)
            ·
              refine ⟨6041438214166506751935203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027625476111004501290135 6041438214166506751935203)
              ·
                refine ⟨9062157321249760127902805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041438214166506751935203 9062157321249760127902805)
                ·
                  refine ⟨106197156108395626498861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9062157321249760127902805 106197156108395626498861)
                  ·
                    rfl

theorem cell23_1861364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1861364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861364 prefixEnd_1861364 := by exact prefixLift 1861364
  have htrace : WordTrace (prefixWord ++ tailWord_1861364) baseStart_1861364 baseEnd_1861364 := by
    simpa [prefixWord, tailWord_1861364, baseEnd_1861364] using wordTrace_append hprefix tailTrace_1861364
  have hstable : (prefixWord ++ tailWord_1861364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861364).length < 2 ^ (prefixWord ++ tailWord_1861364).sum := by decide
  have hdescent : baseEnd_1861364 < baseStart_1861364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861367 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 2, 3, 2]
def baseStart_1861367 : Nat := 118140960795 + 1861367 * 2 ^ 59
def prefixEnd_1861367 : Nat := 4983230072969 + 3 ^ 40 * 1861367 * 2
def baseEnd_1861367 : Nat := 955775945417524126752235

theorem tailTrace_1861367 : CollatzResearch.WordTrace tailWord_1861367 prefixEnd_1861367 955775945417524126752235 := by
  unfold tailWord_1861367
  simp only [CollatzResearch.WordTrace]
  refine ⟨67889631847592730019702355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45259754565061820013134903 67889631847592730019702355)
  ·
    refine ⟨101834447771389095029553533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67889631847592730019702355 101834447771389095029553533)
    ·
      refine ⟨38187917914270910636082575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101834447771389095029553533 38187917914270910636082575)
      ·
        refine ⟨57281876871406365954123863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38187917914270910636082575 57281876871406365954123863)
        ·
          refine ⟨85922815307109548931185795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57281876871406365954123863 85922815307109548931185795)
          ·
            refine ⟨128884222960664323396778693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85922815307109548931185795 128884222960664323396778693)
            ·
              refine ⟨24165791805124560636896005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128884222960664323396778693 24165791805124560636896005)
              ·
                refine ⟨4531085963460855119418001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24165791805124560636896005 4531085963460855119418001)
                ·
                  refine ⟨3398314472595641339563501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4531085963460855119418001 3398314472595641339563501)
                  ·
                    refine ⟨1274367927223365502336313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398314472595641339563501 1274367927223365502336313)
                    ·
                      refine ⟨955775945417524126752235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274367927223365502336313 955775945417524126752235)
                      ·
                        rfl

theorem cell23_1861367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_1861367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861367 prefixEnd_1861367 := by exact prefixLift 1861367
  have htrace : WordTrace (prefixWord ++ tailWord_1861367) baseStart_1861367 baseEnd_1861367 := by
    simpa [prefixWord, tailWord_1861367, baseEnd_1861367] using wordTrace_append hprefix tailTrace_1861367
  have hstable : (prefixWord ++ tailWord_1861367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861367).length < 2 ^ (prefixWord ++ tailWord_1861367).sum := by decide
  have hdescent : baseEnd_1861367 < baseStart_1861367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861394 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1861394 : Nat := 118140960795 + 1861394 * 2 ^ 59
def prefixEnd_1861394 : Nat := 4983230072969 + 3 ^ 40 * 1861394 * 2
def baseEnd_1861394 : Nat := 318596603131731840371537

theorem tailTrace_1861394 : CollatzResearch.WordTrace tailWord_1861394 prefixEnd_1861394 318596603131731840371537 := by
  unfold tailWord_1861394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16972654154623728407733809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45260411078996609087290157 16972654154623728407733809)
  ·
    refine ⟨12729490615967796305800357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16972654154623728407733809 12729490615967796305800357)
    ·
      refine ⟨2386779490493961807337567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12729490615967796305800357 2386779490493961807337567)
      ·
        refine ⟨3580169235740942711006351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386779490493961807337567 3580169235740942711006351)
        ·
          refine ⟨5370253853611414066509527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580169235740942711006351 5370253853611414066509527)
          ·
            refine ⟨8055380780417121099764291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370253853611414066509527 8055380780417121099764291)
            ·
              refine ⟨12083071170625681649646437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8055380780417121099764291 12083071170625681649646437)
              ·
                refine ⟨2265575844492315309308707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12083071170625681649646437 2265575844492315309308707)
                ·
                  refine ⟨3398363766738472963963061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265575844492315309308707 3398363766738472963963061)
                  ·
                    refine ⟨318596603131731840371537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3398363766738472963963061 318596603131731840371537)
                    ·
                      rfl

theorem cell23_1861394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1861394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861394 prefixEnd_1861394 := by exact prefixLift 1861394
  have htrace : WordTrace (prefixWord ++ tailWord_1861394) baseStart_1861394 baseEnd_1861394 := by
    simpa [prefixWord, tailWord_1861394, baseEnd_1861394] using wordTrace_append hprefix tailTrace_1861394
  have hstable : (prefixWord ++ tailWord_1861394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861394).length < 2 ^ (prefixWord ++ tailWord_1861394).sum := by decide
  have hdescent : baseEnd_1861394 < baseStart_1861394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861397 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_1861397 : Nat := 118140960795 + 1861397 * 2 ^ 59
def prefixEnd_1861397 : Nat := 4983230072969 + 3 ^ 40 * 1861397 * 2
def baseEnd_1861397 : Nat := 955791349837159009377097

theorem tailTrace_1861397 : CollatzResearch.WordTrace tailWord_1861397 prefixEnd_1861397 955791349837159009377097 := by
  unfold tailWord_1861397
  simp only [CollatzResearch.WordTrace]
  refine ⟨67890726037484045143294445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45260484024989363428862963 67890726037484045143294445)
  ·
    refine ⟨25459022264056516928735417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67890726037484045143294445 25459022264056516928735417)
    ·
      refine ⟨19094266698042387696551563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25459022264056516928735417 19094266698042387696551563)
      ·
        refine ⟨28641400047063581544827345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19094266698042387696551563 28641400047063581544827345)
        ·
          refine ⟨21481050035297686158620509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28641400047063581544827345 21481050035297686158620509)
          ·
            refine ⟨8055393763236632309482691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21481050035297686158620509 8055393763236632309482691)
            ·
              refine ⟨12083090644854948464224037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8055393763236632309482691 12083090644854948464224037)
              ·
                refine ⟨2265579495910302837042007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12083090644854948464224037 2265579495910302837042007)
                ·
                  refine ⟨3398369243865454255563011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265579495910302837042007 3398369243865454255563011)
                  ·
                    refine ⟨5097553865798181383344517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3398369243865454255563011 5097553865798181383344517)
                    ·
                      refine ⟨955791349837159009377097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5097553865798181383344517 955791349837159009377097)
                      ·
                        rfl

theorem cell23_1861397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_1861397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861397 prefixEnd_1861397 := by exact prefixLift 1861397
  have htrace : WordTrace (prefixWord ++ tailWord_1861397) baseStart_1861397 baseEnd_1861397 := by
    simpa [prefixWord, tailWord_1861397, baseEnd_1861397] using wordTrace_append hprefix tailTrace_1861397
  have hstable : (prefixWord ++ tailWord_1861397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861397).length < 2 ^ (prefixWord ++ tailWord_1861397).sum := by decide
  have hdescent : baseEnd_1861397 < baseStart_1861397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861403 : List Nat := [1, 1, 1, 1, 1, 1, 4, 13]
def baseStart_1861403 : Nat := 118140960795 + 1861403 * 2 ^ 59
def prefixEnd_1861403 : Nat := 4983230072969 + 3 ^ 40 * 1861403 * 2
def baseEnd_1861403 : Nat := 35399793730410592070447

theorem tailTrace_1861403 : CollatzResearch.WordTrace tailWord_1861403 prefixEnd_1861403 35399793730410592070447 := by
  unfold tailWord_1861403
  simp only [CollatzResearch.WordTrace]
  refine ⟨67890944875462308168012863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45260629916974872112008575 67890944875462308168012863)
  ·
    refine ⟨101836417313193462252019295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67890944875462308168012863 101836417313193462252019295)
    ·
      refine ⟨152754625969790193378028943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101836417313193462252019295 152754625969790193378028943)
      ·
        refine ⟨229131938954685290067043415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152754625969790193378028943 229131938954685290067043415)
        ·
          refine ⟨343697908432027935100565123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229131938954685290067043415 343697908432027935100565123)
          ·
            refine ⟨515546862648041902650847685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343697908432027935100565123 515546862648041902650847685)
            ·
              refine ⟨96665036746507856747033941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515546862648041902650847685 96665036746507856747033941)
              ·
                refine ⟨35399793730410592070447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 96665036746507856747033941 35399793730410592070447)
                ·
                  rfl

theorem cell23_1861403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 13].length) (baseStart_1861403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861403 prefixEnd_1861403 := by exact prefixLift 1861403
  have htrace : WordTrace (prefixWord ++ tailWord_1861403) baseStart_1861403 baseEnd_1861403 := by
    simpa [prefixWord, tailWord_1861403, baseEnd_1861403] using wordTrace_append hprefix tailTrace_1861403
  have hstable : (prefixWord ++ tailWord_1861403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861403).length < 2 ^ (prefixWord ++ tailWord_1861403).sum := by decide
  have hdescent : baseEnd_1861403 < baseStart_1861403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861420 : List Nat := [2, 2, 1, 1, 1, 7, 9]
def baseStart_1861420 : Nat := 118140960795 + 1861420 * 2 ^ 59
def prefixEnd_1861420 : Nat := 4983230072969 + 3 ^ 40 * 1861420 * 2
def baseEnd_1861420 : Nat := 11800039011014968140611

theorem tailTrace_1861420 : CollatzResearch.WordTrace tailWord_1861420 prefixEnd_1861420 11800039011014968140611 := by
  unfold tailWord_1861420
  simp only [CollatzResearch.WordTrace]
  refine ⟨33945782458200360035690857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45261043277600480047587809 33945782458200360035690857)
  ·
    refine ⟨25459336843650270026768143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33945782458200360035690857 25459336843650270026768143)
    ·
      refine ⟨38189005265475405040152215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25459336843650270026768143 38189005265475405040152215)
      ·
        refine ⟨57283507898213107560228323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38189005265475405040152215 57283507898213107560228323)
        ·
          refine ⟨85925261847319661340342485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57283507898213107560228323 85925261847319661340342485)
          ·
            refine ⟨2013873324546554562664277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85925261847319661340342485 2013873324546554562664277)
            ·
              refine ⟨11800039011014968140611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2013873324546554562664277 11800039011014968140611)
              ·
                rfl

theorem cell23_1861420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 9].length) (baseStart_1861420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861420 prefixEnd_1861420 := by exact prefixLift 1861420
  have htrace : WordTrace (prefixWord ++ tailWord_1861420) baseStart_1861420 baseEnd_1861420 := by
    simpa [prefixWord, tailWord_1861420, baseEnd_1861420] using wordTrace_append hprefix tailTrace_1861420
  have hstable : (prefixWord ++ tailWord_1861420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861420).length < 2 ^ (prefixWord ++ tailWord_1861420).sum := by decide
  have hdescent : baseEnd_1861420 < baseStart_1861420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861437 : List Nat := [1, 4, 1, 4, 1, 2, 2, 8]
def baseStart_1861437 : Nat := 118140960795 + 1861437 * 2 ^ 59
def prefixEnd_1861437 : Nat := 4983230072969 + 3 ^ 40 * 1861437 * 2
def baseEnd_1861437 : Nat := 35400440335679216773219

theorem tailTrace_1861437 : CollatzResearch.WordTrace tailWord_1861437 prefixEnd_1861437 35400440335679216773219 := by
  unfold tailWord_1861437
  simp only [CollatzResearch.WordTrace]
  refine ⟨67892184957339131974750565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45261456638226087983167043 67892184957339131974750565)
  ·
    refine ⟨12729784679501087245265731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67892184957339131974750565 12729784679501087245265731)
    ·
      refine ⟨19094677019251630867898597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12729784679501087245265731 19094677019251630867898597)
      ·
        refine ⟨3580251941109680787730987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19094677019251630867898597 3580251941109680787730987)
        ·
          refine ⟨5370377911664521181596481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580251941109680787730987 5370377911664521181596481)
          ·
            refine ⟨4027783433748390886197361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5370377911664521181596481 4027783433748390886197361)
            ·
              refine ⟨3020837575311293164648021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4027783433748390886197361 3020837575311293164648021)
              ·
                refine ⟨35400440335679216773219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3020837575311293164648021 35400440335679216773219)
                ·
                  rfl

theorem cell23_1861437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 8].length) (baseStart_1861437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861437 prefixEnd_1861437 := by exact prefixLift 1861437
  have htrace : WordTrace (prefixWord ++ tailWord_1861437) baseStart_1861437 baseEnd_1861437 := by
    simpa [prefixWord, tailWord_1861437, baseEnd_1861437] using wordTrace_append hprefix tailTrace_1861437
  have hstable : (prefixWord ++ tailWord_1861437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861437).length < 2 ^ (prefixWord ++ tailWord_1861437).sum := by decide
  have hdescent : baseEnd_1861437 < baseStart_1861437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861468 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1861468 : Nat := 118140960795 + 1861468 * 2 ^ 59
def prefixEnd_1861468 : Nat := 4983230072969 + 3 ^ 40 * 1861468 * 2
def baseEnd_1861468 : Nat := 955827806963628231589271

theorem tailTrace_1861468 : CollatzResearch.WordTrace tailWord_1861468 prefixEnd_1861468 955827806963628231589271 := by
  unfold tailWord_1861468
  simp only [CollatzResearch.WordTrace]
  refine ⟨33946657810113412134564529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45262210413484549512752705 33946657810113412134564529)
  ·
    refine ⟨25459993357585059100923397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33946657810113412134564529 25459993357585059100923397)
    ·
      refine ⟨4773748754547198581423137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25459993357585059100923397 4773748754547198581423137)
      ·
        refine ⟨3580311565910398936067353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4773748754547198581423137 3580311565910398936067353)
        ·
          refine ⟨2685233674432799202050515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580311565910398936067353 2685233674432799202050515)
          ·
            refine ⟨4027850511649198803075773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685233674432799202050515 4027850511649198803075773)
            ·
              refine ⟨1510443941868449551153415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4027850511649198803075773 1510443941868449551153415)
              ·
                refine ⟨2265665912802674326730123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510443941868449551153415 2265665912802674326730123)
                ·
                  refine ⟨3398498869204011490095185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265665912802674326730123 3398498869204011490095185)
                  ·
                    refine ⟨2548874151903008617571389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3398498869204011490095185 2548874151903008617571389)
                    ·
                      refine ⟨955827806963628231589271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2548874151903008617571389 955827806963628231589271)
                      ·
                        rfl

theorem cell23_1861468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1861468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861468 prefixEnd_1861468 := by exact prefixLift 1861468
  have htrace : WordTrace (prefixWord ++ tailWord_1861468) baseStart_1861468 baseEnd_1861468 := by
    simpa [prefixWord, tailWord_1861468, baseEnd_1861468] using wordTrace_append hprefix tailTrace_1861468
  have hstable : (prefixWord ++ tailWord_1861468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861468).length < 2 ^ (prefixWord ++ tailWord_1861468).sum := by decide
  have hdescent : baseEnd_1861468 < baseStart_1861468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861504 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 1, 4, 2]
def baseStart_1861504 : Nat := 118140960795 + 1861504 * 2 ^ 59
def prefixEnd_1861504 : Nat := 4983230072969 + 3 ^ 40 * 1861504 * 2
def baseEnd_1861504 : Nat := 955846292267190090739105

theorem tailTrace_1861504 : CollatzResearch.WordTrace tailWord_1861504 prefixEnd_1861504 955846292267190090739105 := by
  unfold tailWord_1861504
  simp only [CollatzResearch.WordTrace]
  refine ⟨33947314324048201208719783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45263085765397601611626377 33947314324048201208719783)
  ·
    refine ⟨50920971486072301813079675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33947314324048201208719783 50920971486072301813079675)
    ·
      refine ⟨76381457229108452719619513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50920971486072301813079675 76381457229108452719619513)
      ·
        refine ⟨57286092921831339539714635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76381457229108452719619513 57286092921831339539714635)
        ·
          refine ⟨85929139382747009309571953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57286092921831339539714635 85929139382747009309571953)
          ·
            refine ⟨64446854537060256982178965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85929139382747009309571953 64446854537060256982178965)
            ·
              refine ⟨3020946306424699546039639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64446854537060256982178965 3020946306424699546039639)
              ·
                refine ⟨4531419459637049319059459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020946306424699546039639 4531419459637049319059459)
                ·
                  refine ⟨6797129189455573978589189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4531419459637049319059459 6797129189455573978589189)
                  ·
                    refine ⟨1274461723022920120985473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6797129189455573978589189 1274461723022920120985473)
                    ·
                      refine ⟨955846292267190090739105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274461723022920120985473 955846292267190090739105)
                      ·
                        rfl

theorem cell23_1861504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_1861504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861504 prefixEnd_1861504 := by exact prefixLift 1861504
  have htrace : WordTrace (prefixWord ++ tailWord_1861504) baseStart_1861504 baseEnd_1861504 := by
    simpa [prefixWord, tailWord_1861504, baseEnd_1861504] using wordTrace_append hprefix tailTrace_1861504
  have hstable : (prefixWord ++ tailWord_1861504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861504).length < 2 ^ (prefixWord ++ tailWord_1861504).sum := by decide
  have hdescent : baseEnd_1861504 < baseStart_1861504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861538 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_1861538 : Nat := 118140960795 + 1861538 * 2 ^ 59
def prefixEnd_1861538 : Nat := 4983230072969 + 3 ^ 40 * 1861538 * 2
def baseEnd_1861538 : Nat := 955863750609442957713949

theorem tailTrace_1861538 : CollatzResearch.WordTrace tailWord_1861538 prefixEnd_1861538 955863750609442957713949 := by
  unfold tailWord_1861538
  simp only [CollatzResearch.WordTrace]
  refine ⟨16973967182493306556044317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45263912486648817482784845 16973967182493306556044317)
  ·
    refine ⟨6365237693434989958516619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16973967182493306556044317 6365237693434989958516619)
    ·
      refine ⟨9547856540152484937774929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6365237693434989958516619 9547856540152484937774929)
      ·
        refine ⟨7160892405114363703331197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9547856540152484937774929 7160892405114363703331197)
        ·
          refine ⟨2685334651917886388749199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7160892405114363703331197 2685334651917886388749199)
          ·
            refine ⟨4028001977876829583123799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685334651917886388749199 4028001977876829583123799)
            ·
              refine ⟨6042002966815244374685699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028001977876829583123799 6042002966815244374685699)
              ·
                refine ⟨9063004450222866562028549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042002966815244374685699 9063004450222866562028549)
                ·
                  refine ⟨1699313334416787480380353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9063004450222866562028549 1699313334416787480380353)
                  ·
                    refine ⟨1274485000812590610285265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1699313334416787480380353 1274485000812590610285265)
                    ·
                      refine ⟨955863750609442957713949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274485000812590610285265 955863750609442957713949)
                      ·
                        rfl

theorem cell23_1861538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_1861538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861538 prefixEnd_1861538 := by exact prefixLift 1861538
  have htrace : WordTrace (prefixWord ++ tailWord_1861538) baseStart_1861538 baseEnd_1861538 := by
    simpa [prefixWord, tailWord_1861538, baseEnd_1861538] using wordTrace_append hprefix tailTrace_1861538
  have hstable : (prefixWord ++ tailWord_1861538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861538).length < 2 ^ (prefixWord ++ tailWord_1861538).sum := by decide
  have hdescent : baseEnd_1861538 < baseStart_1861538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861557 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1861557 : Nat := 118140960795 + 1861557 * 2 ^ 59
def prefixEnd_1861557 : Nat := 4983230072969 + 3 ^ 40 * 1861557 * 2
def baseEnd_1861557 : Nat := 318624502247292794458787

theorem tailTrace_1861557 : CollatzResearch.WordTrace tailWord_1861557 prefixEnd_1861557 318624502247292794458787 := by
  unfold tailWord_1861557
  simp only [CollatzResearch.WordTrace]
  refine ⟨67896561716904392469118925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45264374477936261646079283 67896561716904392469118925)
  ·
    refine ⟨25461210643839147175919597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67896561716904392469118925 25461210643839147175919597)
    ·
      refine ⟨9547953991439680190969849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25461210643839147175919597 9547953991439680190969849)
      ·
        refine ⟨7160965493579760143227387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9547953991439680190969849 7160965493579760143227387)
        ·
          refine ⟨10741448240369640214841081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7160965493579760143227387 10741448240369640214841081)
          ·
            refine ⟨8056086180277230161130811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10741448240369640214841081 8056086180277230161130811)
            ·
              refine ⟨12084129270415845241696217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056086180277230161130811 12084129270415845241696217)
              ·
                refine ⟨9063096952811883931272163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12084129270415845241696217 9063096952811883931272163)
                ·
                  refine ⟨13594645429217825896908245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063096952811883931272163 13594645429217825896908245)
                  ·
                    refine ⟨318624502247292794458787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13594645429217825896908245 318624502247292794458787)
                    ·
                      rfl

theorem cell23_1861557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1861557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861557 prefixEnd_1861557 := by exact prefixLift 1861557
  have htrace : WordTrace (prefixWord ++ tailWord_1861557) baseStart_1861557 baseEnd_1861557 := by
    simpa [prefixWord, tailWord_1861557, baseEnd_1861557] using wordTrace_append hprefix tailTrace_1861557
  have hstable : (prefixWord ++ tailWord_1861557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861557).length < 2 ^ (prefixWord ++ tailWord_1861557).sum := by decide
  have hdescent : baseEnd_1861557 < baseStart_1861557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861627 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 3]
def baseStart_1861627 : Nat := 118140960795 + 1861627 * 2 ^ 59
def prefixEnd_1861627 : Nat := 4983230072969 + 3 ^ 40 * 1861627 * 2
def baseEnd_1861627 : Nat := 955909450387693109501039

theorem tailTrace_1861627 : CollatzResearch.WordTrace tailWord_1861627 prefixEnd_1861627 955909450387693109501039 := by
  unfold tailWord_1861627
  simp only [CollatzResearch.WordTrace]
  refine ⟨67899114826650794424167135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45266076551100529616111423 67899114826650794424167135)
  ·
    refine ⟨101848672239976191636250703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67899114826650794424167135 101848672239976191636250703)
    ·
      refine ⟨152773008359964287454376055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101848672239976191636250703 152773008359964287454376055)
      ·
        refine ⟨229159512539946431181564083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152773008359964287454376055 229159512539946431181564083)
        ·
          refine ⟨343739268809919646772346125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229159512539946431181564083 343739268809919646772346125)
          ·
            refine ⟨128902225803719867539629797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343739268809919646772346125 128902225803719867539629797)
            ·
              refine ⟨24169167338197475163680587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128902225803719867539629797 24169167338197475163680587)
              ·
                refine ⟨36253751007296212745520881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24169167338197475163680587 36253751007296212745520881)
                ·
                  refine ⟨27190313255472159559140661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36253751007296212745520881 27190313255472159559140661)
                  ·
                    refine ⟨2549091867700514958669437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27190313255472159559140661 2549091867700514958669437)
                    ·
                      refine ⟨955909450387693109501039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2549091867700514958669437 955909450387693109501039)
                      ·
                        rfl

theorem cell23_1861627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 3].length) (baseStart_1861627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861627 prefixEnd_1861627 := by exact prefixLift 1861627
  have htrace : WordTrace (prefixWord ++ tailWord_1861627) baseStart_1861627 baseEnd_1861627 := by
    simpa [prefixWord, tailWord_1861627, baseEnd_1861627] using wordTrace_append hprefix tailTrace_1861627
  have hstable : (prefixWord ++ tailWord_1861627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861627).length < 2 ^ (prefixWord ++ tailWord_1861627).sum := by decide
  have hdescent : baseEnd_1861627 < baseStart_1861627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861678 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1861678 : Nat := 118140960795 + 1861678 * 2 ^ 59
def prefixEnd_1861678 : Nat := 4983230072969 + 3 ^ 40 * 1861678 * 2
def baseEnd_1861678 : Nat := 955935637901072409963305

theorem tailTrace_1861678 : CollatzResearch.WordTrace tailWord_1861678 prefixEnd_1861678 955935637901072409963305 := by
  unfold tailWord_1861678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487621868683253766784211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45267316632977353422849125 8487621868683253766784211)
  ·
    refine ⟨12731432803024880650176317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8487621868683253766784211 12731432803024880650176317)
    ·
      refine ⟨4774287301134330243816119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12731432803024880650176317 4774287301134330243816119)
      ·
        refine ⟨7161430951701495365724179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774287301134330243816119 7161430951701495365724179)
        ·
          refine ⟨10742146427552243048586269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161430951701495365724179 10742146427552243048586269)
          ·
            refine ⟨4028304910332091143219851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10742146427552243048586269 4028304910332091143219851)
            ·
              refine ⟨6042457365498136714829777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028304910332091143219851 6042457365498136714829777)
              ·
                refine ⟨4531843024123602536122333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6042457365498136714829777 4531843024123602536122333)
                ·
                  refine ⟨1699441134046350951045875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4531843024123602536122333 1699441134046350951045875)
                  ·
                    refine ⟨2549161701069526426568813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1699441134046350951045875 2549161701069526426568813)
                    ·
                      refine ⟨955935637901072409963305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2549161701069526426568813 955935637901072409963305)
                      ·
                        rfl

theorem cell23_1861678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1861678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861678 prefixEnd_1861678 := by exact prefixLift 1861678
  have htrace : WordTrace (prefixWord ++ tailWord_1861678) baseStart_1861678 baseEnd_1861678 := by
    simpa [prefixWord, tailWord_1861678, baseEnd_1861678] using wordTrace_append hprefix tailTrace_1861678
  have hstable : (prefixWord ++ tailWord_1861678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861678).length < 2 ^ (prefixWord ++ tailWord_1861678).sum := by decide
  have hdescent : baseEnd_1861678 < baseStart_1861678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861701 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 7, 2, 2]
def baseStart_1861701 : Nat := 118140960795 + 1861701 * 2 ^ 59
def prefixEnd_1861701 : Nat := 4983230072969 + 3 ^ 40 * 1861701 * 2
def baseEnd_1861701 : Nat := 955947447956125819975699

theorem tailTrace_1861701 : CollatzResearch.WordTrace tailWord_1861701 prefixEnd_1861701 955947447956125819975699 := by
  unfold tailWord_1861701
  simp only [CollatzResearch.WordTrace]
  refine ⟨67901813828382705062360957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45267875885588470041573971 67901813828382705062360957)
  ·
    refine ⟨25463180185643514398385359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67901813828382705062360957 25463180185643514398385359)
    ·
      refine ⟨38194770278465271597578039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25463180185643514398385359 38194770278465271597578039)
      ·
        refine ⟨57292155417697907396367059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38194770278465271597578039 57292155417697907396367059)
        ·
          refine ⟨85938233126546861094550589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57292155417697907396367059 85938233126546861094550589)
          ·
            refine ⟨32226837422455072910456471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85938233126546861094550589 32226837422455072910456471)
            ·
              refine ⟨48340256133682609365684707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32226837422455072910456471 48340256133682609365684707)
              ·
                refine ⟨72510384200523914048527061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48340256133682609365684707 72510384200523914048527061)
                ·
                  refine ⟨1699462129699779235512353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 72510384200523914048527061 1699462129699779235512353)
                  ·
                    refine ⟨1274596597274834426634265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1699462129699779235512353 1274596597274834426634265)
                    ·
                      refine ⟨955947447956125819975699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274596597274834426634265 955947447956125819975699)
                      ·
                        rfl

theorem cell23_1861701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_1861701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861701 prefixEnd_1861701 := by exact prefixLift 1861701
  have htrace : WordTrace (prefixWord ++ tailWord_1861701) baseStart_1861701 baseEnd_1861701 := by
    simpa [prefixWord, tailWord_1861701, baseEnd_1861701] using wordTrace_append hprefix tailTrace_1861701
  have hstable : (prefixWord ++ tailWord_1861701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861701).length < 2 ^ (prefixWord ++ tailWord_1861701).sum := by decide
  have hdescent : baseEnd_1861701 < baseStart_1861701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861704 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_1861704 : Nat := 118140960795 + 1861704 * 2 ^ 59
def prefixEnd_1861704 : Nat := 4983230072969 + 3 ^ 40 * 1861704 * 2
def baseEnd_1861704 : Nat := 955948988398089308238185

theorem tailTrace_1861704 : CollatzResearch.WordTrace tailWord_1861704 prefixEnd_1861704 955948988398089308238185 := by
  unfold tailWord_1861704
  simp only [CollatzResearch.WordTrace]
  refine ⟨33950961623685918287360083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45267948831581224383146777 33950961623685918287360083)
  ·
    refine ⟨50926442435528877431040125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33950961623685918287360083 50926442435528877431040125)
    ·
      refine ⟨19097415913323329036640047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50926442435528877431040125 19097415913323329036640047)
      ·
        refine ⟨28646123869984993554960071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097415913323329036640047 28646123869984993554960071)
        ·
          refine ⟨42969185804977490332440107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28646123869984993554960071 42969185804977490332440107)
          ·
            refine ⟨64453778707466235498660161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42969185804977490332440107 64453778707466235498660161)
            ·
              refine ⟨48340334030599676623995121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64453778707466235498660161 48340334030599676623995121)
              ·
                refine ⟨36255250522949757467996341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48340334030599676623995121 36255250522949757467996341)
                ·
                  refine ⟨3398929736526539762624657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36255250522949757467996341 3398929736526539762624657)
                  ·
                    refine ⟨2549197302394904821968493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3398929736526539762624657 2549197302394904821968493)
                    ·
                      refine ⟨955948988398089308238185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2549197302394904821968493 955948988398089308238185)
                      ·
                        rfl

theorem cell23_1861704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_1861704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861704 prefixEnd_1861704 := by exact prefixLift 1861704
  have htrace : WordTrace (prefixWord ++ tailWord_1861704) baseStart_1861704 baseEnd_1861704 := by
    simpa [prefixWord, tailWord_1861704, baseEnd_1861704] using wordTrace_append hprefix tailTrace_1861704
  have hstable : (prefixWord ++ tailWord_1861704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861704).length < 2 ^ (prefixWord ++ tailWord_1861704).sum := by decide
  have hdescent : baseEnd_1861704 < baseStart_1861704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861727 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_1861727 : Nat := 118140960795 + 1861727 * 2 ^ 59
def prefixEnd_1861727 : Nat := 4983230072969 + 3 ^ 40 * 1861727 * 2
def baseEnd_1861727 : Nat := 955960798453142718250579

theorem tailTrace_1861727 : CollatzResearch.WordTrace tailWord_1861727 prefixEnd_1861727 955960798453142718250579 := by
  unfold tailWord_1861727
  simp only [CollatzResearch.WordTrace]
  refine ⟨67902762126288511502807435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45268508084192341001871623 67902762126288511502807435)
  ·
    refine ⟨101854143189432767254211153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67902762126288511502807435 101854143189432767254211153)
    ·
      refine ⟨76390607392074575440658365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101854143189432767254211153 76390607392074575440658365)
      ·
        refine ⟨28646477772027965790246887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76390607392074575440658365 28646477772027965790246887)
        ·
          refine ⟨42969716658041948685370331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28646477772027965790246887 42969716658041948685370331)
          ·
            refine ⟨64454574987062923028055497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42969716658041948685370331 64454574987062923028055497)
            ·
              refine ⟨48340931240297192271041623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64454574987062923028055497 48340931240297192271041623)
              ·
                refine ⟨72511396860445788406562435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48340931240297192271041623 72511396860445788406562435)
                ·
                  refine ⟨108767095290668682609843653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72511396860445788406562435 108767095290668682609843653)
                  ·
                    refine ⟨20393830367000377989345685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108767095290668682609843653 20393830367000377989345685)
                    ·
                      refine ⟨955960798453142718250579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20393830367000377989345685 955960798453142718250579)
                      ·
                        rfl

theorem cell23_1861727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_1861727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861727 prefixEnd_1861727 := by exact prefixLift 1861727
  have htrace : WordTrace (prefixWord ++ tailWord_1861727) baseStart_1861727 baseEnd_1861727 := by
    simpa [prefixWord, tailWord_1861727, baseEnd_1861727] using wordTrace_append hprefix tailTrace_1861727
  have hstable : (prefixWord ++ tailWord_1861727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861727).length < 2 ^ (prefixWord ++ tailWord_1861727).sum := by decide
  have hdescent : baseEnd_1861727 < baseStart_1861727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861728 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 2, 4]
def baseStart_1861728 : Nat := 118140960795 + 1861728 * 2 ^ 59
def prefixEnd_1861728 : Nat := 4983230072969 + 3 ^ 40 * 1861728 * 2
def baseEnd_1861728 : Nat := 318653770644599071446025

theorem tailTrace_1861728 : CollatzResearch.WordTrace tailWord_1861728 prefixEnd_1861728 318653770644599071446025 := by
  unfold tailWord_1861728
  simp only [CollatzResearch.WordTrace]
  refine ⟨33951399299642444336796919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45268532399523259115729225 33951399299642444336796919)
  ·
    refine ⟨50927098949463666505195379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33951399299642444336796919 50927098949463666505195379)
    ·
      refine ⟨76390648424195499757793069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50927098949463666505195379 76390648424195499757793069)
      ·
        refine ⟨28646493159073312409172401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76390648424195499757793069 28646493159073312409172401)
        ·
          refine ⟨21484869869304984306879301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28646493159073312409172401 21484869869304984306879301)
          ·
            refine ⟨4028413100494684557539869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21484869869304984306879301 4028413100494684557539869)
            ·
              refine ⟨1510654912685506709077451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4028413100494684557539869 1510654912685506709077451)
              ·
                refine ⟨2265982369028260063616177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510654912685506709077451 2265982369028260063616177)
                ·
                  refine ⟨1699486776771195047712133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2265982369028260063616177 1699486776771195047712133)
                  ·
                    refine ⟨318653770644599071446025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1699486776771195047712133 318653770644599071446025)
                    ·
                      rfl

theorem cell23_1861728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 4].length) (baseStart_1861728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861728 prefixEnd_1861728 := by exact prefixLift 1861728
  have htrace : WordTrace (prefixWord ++ tailWord_1861728) baseStart_1861728 baseEnd_1861728 := by
    simpa [prefixWord, tailWord_1861728, baseEnd_1861728] using wordTrace_append hprefix tailTrace_1861728
  have hstable : (prefixWord ++ tailWord_1861728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861728).length < 2 ^ (prefixWord ++ tailWord_1861728).sum := by decide
  have hdescent : baseEnd_1861728 < baseStart_1861728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861751 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_1861751 : Nat := 118140960795 + 1861751 * 2 ^ 59
def prefixEnd_1861751 : Nat := 4983230072969 + 3 ^ 40 * 1861751 * 2
def baseEnd_1861751 : Nat := 955973121988850624350469

theorem tailTrace_1861751 : CollatzResearch.WordTrace tailWord_1861751 prefixEnd_1861751 955973121988850624350469 := by
  unfold tailWord_1861751
  simp only [CollatzResearch.WordTrace]
  refine ⟨67903637478201563601681107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45269091652134375734454071 67903637478201563601681107)
  ·
    refine ⟨101855456217302345402521661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67903637478201563601681107 101855456217302345402521661)
    ·
      refine ⟨38195796081488379525945623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101855456217302345402521661 38195796081488379525945623)
      ·
        refine ⟨57293694122232569288918435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38195796081488379525945623 57293694122232569288918435)
        ·
          refine ⟨85940541183348853933377653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57293694122232569288918435 85940541183348853933377653)
          ·
            refine ⟨8056925735938955056254155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85940541183348853933377653 8056925735938955056254155)
            ·
              refine ⟨12085388603908432584381233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056925735938955056254155 12085388603908432584381233)
              ·
                refine ⟨9064041452931324438285925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085388603908432584381233 9064041452931324438285925)
                ·
                  refine ⟨1699507772424623332178611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9064041452931324438285925 1699507772424623332178611)
                  ·
                    refine ⟨2549261658636934998267917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1699507772424623332178611 2549261658636934998267917)
                    ·
                      refine ⟨955973121988850624350469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2549261658636934998267917 955973121988850624350469)
                      ·
                        rfl

theorem cell23_1861751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_1861751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861751 prefixEnd_1861751 := by exact prefixLift 1861751
  have htrace : WordTrace (prefixWord ++ tailWord_1861751) baseStart_1861751 baseEnd_1861751 := by
    simpa [prefixWord, tailWord_1861751, baseEnd_1861751] using wordTrace_append hprefix tailTrace_1861751
  have hstable : (prefixWord ++ tailWord_1861751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861751).length < 2 ^ (prefixWord ++ tailWord_1861751).sum := by decide
  have hdescent : baseEnd_1861751 < baseStart_1861751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861764 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1861764 : Nat := 118140960795 + 1861764 * 2 ^ 59
def prefixEnd_1861764 : Nat := 4983230072969 + 3 ^ 40 * 1861764 * 2
def baseEnd_1861764 : Nat := 955979797237359073487909

theorem tailTrace_1861764 : CollatzResearch.WordTrace tailWord_1861764 prefixEnd_1861764 955979797237359073487909 := by
  unfold tailWord_1861764
  simp only [CollatzResearch.WordTrace]
  refine ⟨33952055813577233410952173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45269407751436311214602897 33952055813577233410952173)
  ·
    refine ⟨12732020930091462529107065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33952055813577233410952173 12732020930091462529107065)
    ·
      refine ⟨9549015697568596896830299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12732020930091462529107065 9549015697568596896830299)
      ·
        refine ⟨14323523546352895345245449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9549015697568596896830299 14323523546352895345245449)
        ·
          refine ⟨10742642659764671508934087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14323523546352895345245449 10742642659764671508934087)
          ·
            refine ⟨16113963989647007263401131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742642659764671508934087 16113963989647007263401131)
            ·
              refine ⟨24170945984470510895101697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16113963989647007263401131 24170945984470510895101697)
              ·
                refine ⟨18128209488352883171326273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24170945984470510895101697 18128209488352883171326273)
                ·
                  refine ⟨13596157116264662378494705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18128209488352883171326273 13596157116264662378494705)
                  ·
                    refine ⟨10197117837198496783871029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13596157116264662378494705 10197117837198496783871029)
                    ·
                      refine ⟨955979797237359073487909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10197117837198496783871029 955979797237359073487909)
                      ·
                        rfl

theorem cell23_1861764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1861764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861764 prefixEnd_1861764 := by exact prefixLift 1861764
  have htrace : WordTrace (prefixWord ++ tailWord_1861764) baseStart_1861764 baseEnd_1861764 := by
    simpa [prefixWord, tailWord_1861764, baseEnd_1861764] using wordTrace_append hprefix tailTrace_1861764
  have hstable : (prefixWord ++ tailWord_1861764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861764).length < 2 ^ (prefixWord ++ tailWord_1861764).sum := by decide
  have hdescent : baseEnd_1861764 < baseStart_1861764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861768 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1861768 : Nat := 118140960795 + 1861768 * 2 ^ 59
def prefixEnd_1861768 : Nat := 4983230072969 + 3 ^ 40 * 1861768 * 2
def baseEnd_1861768 : Nat := 955981851159977057837891

theorem tailTrace_1861768 : CollatzResearch.WordTrace tailWord_1861768 prefixEnd_1861768 955981851159977057837891 := by
  unfold tailWord_1861768
  simp only [CollatzResearch.WordTrace]
  refine ⟨33952128759569987752524979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45269505012759983670033305 33952128759569987752524979)
  ·
    refine ⟨50928193139354981628787469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33952128759569987752524979 50928193139354981628787469)
    ·
      refine ⟨19098072427258118110795301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50928193139354981628787469 19098072427258118110795301)
      ·
        refine ⟨3580888580110897145774119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19098072427258118110795301 3580888580110897145774119)
        ·
          refine ⟨5371332870166345718661179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580888580110897145774119 5371332870166345718661179)
          ·
            refine ⟨8056999305249518577991769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371332870166345718661179 8056999305249518577991769)
            ·
              refine ⟨6042749478937138933493827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8056999305249518577991769 6042749478937138933493827)
              ·
                refine ⟨9064124218405708400240741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042749478937138933493827 9064124218405708400240741)
                ·
                  refine ⟨1699523290951070325045139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9064124218405708400240741 1699523290951070325045139)
                  ·
                    refine ⟨2549284936426605487567709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1699523290951070325045139 2549284936426605487567709)
                    ·
                      refine ⟨955981851159977057837891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2549284936426605487567709 955981851159977057837891)
                      ·
                        rfl

theorem cell23_1861768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1861768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861768 prefixEnd_1861768 := by exact prefixLift 1861768
  have htrace : WordTrace (prefixWord ++ tailWord_1861768) baseStart_1861768 baseEnd_1861768 := by
    simpa [prefixWord, tailWord_1861768, baseEnd_1861768] using wordTrace_append hprefix tailTrace_1861768
  have hstable : (prefixWord ++ tailWord_1861768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861768).length < 2 ^ (prefixWord ++ tailWord_1861768).sum := by decide
  have hdescent : baseEnd_1861768 < baseStart_1861768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861778 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1861778 : Nat := 118140960795 + 1861778 * 2 ^ 59
def prefixEnd_1861778 : Nat := 4983230072969 + 3 ^ 40 * 1861778 * 2
def baseEnd_1861778 : Nat := 955986985966522018712845

theorem tailTrace_1861778 : CollatzResearch.WordTrace tailWord_1861778 prefixEnd_1861778 955986985966522018712845 := by
  unfold tailWord_1861778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16976155562275936803228497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45269748166069164808609325 16976155562275936803228497)
  ·
    refine ⟨12732116671706952602421373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16976155562275936803228497 12732116671706952602421373)
    ·
      refine ⟨4774543751890107225908015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12732116671706952602421373 4774543751890107225908015)
      ·
        refine ⟨7161815627835160838862023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774543751890107225908015 7161815627835160838862023)
        ·
          refine ⟨10742723441752741258293035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161815627835160838862023 10742723441752741258293035)
          ·
            refine ⟨16114085162629111887439553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742723441752741258293035 16114085162629111887439553)
            ·
              refine ⟨12085563871971833915579665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16114085162629111887439553 12085563871971833915579665)
              ·
                refine ⟨9064172903978875436684749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085563871971833915579665 9064172903978875436684749)
                ·
                  refine ⟨3399064838992078288756781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9064172903978875436684749 3399064838992078288756781)
                  ·
                    refine ⟨1274649314622029358283793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399064838992078288756781 1274649314622029358283793)
                    ·
                      refine ⟨955986985966522018712845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274649314622029358283793 955986985966522018712845)
                      ·
                        rfl

theorem cell23_1861778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1861778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861778 prefixEnd_1861778 := by exact prefixLift 1861778
  have htrace : WordTrace (prefixWord ++ tailWord_1861778) baseStart_1861778 baseEnd_1861778 := by
    simpa [prefixWord, tailWord_1861778, baseEnd_1861778] using wordTrace_append hprefix tailTrace_1861778
  have hstable : (prefixWord ++ tailWord_1861778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861778).length < 2 ^ (prefixWord ++ tailWord_1861778).sum := by decide
  have hdescent : baseEnd_1861778 < baseStart_1861778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861861 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_1861861 : Nat := 118140960795 + 1861861 * 2 ^ 59
def prefixEnd_1861861 : Nat := 4983230072969 + 3 ^ 40 * 1861861 * 2
def baseEnd_1861861 : Nat := 318676534953615064658321

theorem tailTrace_1861861 : CollatzResearch.WordTrace tailWord_1861861 prefixEnd_1861861 318676534953615064658321 := by
  unfold tailWord_1861861
  simp only [CollatzResearch.WordTrace]
  refine ⟨67907649507803052388185437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45271766338535368258790291 67907649507803052388185437)
  ·
    refine ⟨25465368565426144645569539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67907649507803052388185437 25465368565426144645569539)
    ·
      refine ⟨38198052848139216968354309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25465368565426144645569539 38198052848139216968354309)
      ·
        refine ⟨7162134909026103181566433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38198052848139216968354309 7162134909026103181566433)
        ·
          refine ⟨5371601181769577386174825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7162134909026103181566433 5371601181769577386174825)
          ·
            refine ⟨4028700886327183039631119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5371601181769577386174825 4028700886327183039631119)
            ·
              refine ⟨6043051329490774559446679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028700886327183039631119 6043051329490774559446679)
              ·
                refine ⟨9064576994236161839170019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6043051329490774559446679 9064576994236161839170019)
                ·
                  refine ⟨13596865491354242758755029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9064576994236161839170019 13596865491354242758755029)
                  ·
                    refine ⟨318676534953615064658321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13596865491354242758755029 318676534953615064658321)
                    ·
                      rfl

theorem cell23_1861861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_1861861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861861 prefixEnd_1861861 := by exact prefixLift 1861861
  have htrace : WordTrace (prefixWord ++ tailWord_1861861) baseStart_1861861 baseEnd_1861861 := by
    simpa [prefixWord, tailWord_1861861, baseEnd_1861861] using wordTrace_append hprefix tailTrace_1861861
  have hstable : (prefixWord ++ tailWord_1861861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861861).length < 2 ^ (prefixWord ++ tailWord_1861861).sum := by decide
  have hdescent : baseEnd_1861861 < baseStart_1861861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861898 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_1861898 : Nat := 118140960795 + 1861898 * 2 ^ 59
def prefixEnd_1861898 : Nat := 4983230072969 + 3 ^ 40 * 1861898 * 2
def baseEnd_1861898 : Nat := 956048603645061549212293

theorem tailTrace_1861898 : CollatzResearch.WordTrace tailWord_1861898 prefixEnd_1861898 956048603645061549212293 := by
  unfold tailWord_1861898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16977249752167251926820587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45272666005779338471521565 16977249752167251926820587)
  ·
    refine ⟨25465874628250877890230881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16977249752167251926820587 25465874628250877890230881)
    ·
      refine ⟨19099405971188158417673161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25465874628250877890230881 19099405971188158417673161)
      ·
        refine ⟨14324554478391118813254871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19099405971188158417673161 14324554478391118813254871)
        ·
          refine ⟨21486831717586678219882307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14324554478391118813254871 21486831717586678219882307)
          ·
            refine ⟨32230247576380017329823461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21486831717586678219882307 32230247576380017329823461)
            ·
              refine ⟨6043171420571253249341899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32230247576380017329823461 6043171420571253249341899)
              ·
                refine ⟨9064757130856879874012849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6043171420571253249341899 9064757130856879874012849)
                ·
                  refine ⟨6798567848142659905509637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9064757130856879874012849 6798567848142659905509637)
                  ·
                    refine ⟨1274731471526748732283057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6798567848142659905509637 1274731471526748732283057)
                    ·
                      refine ⟨956048603645061549212293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274731471526748732283057 956048603645061549212293)
                      ·
                        rfl

theorem cell23_1861898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_1861898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861898 prefixEnd_1861898 := by exact prefixLift 1861898
  have htrace : WordTrace (prefixWord ++ tailWord_1861898) baseStart_1861898 baseEnd_1861898 := by
    simpa [prefixWord, tailWord_1861898, baseEnd_1861898] using wordTrace_append hprefix tailTrace_1861898
  have hstable : (prefixWord ++ tailWord_1861898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861898).length < 2 ^ (prefixWord ++ tailWord_1861898).sum := by decide
  have hdescent : baseEnd_1861898 < baseStart_1861898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861951 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 3, 5]
def baseStart_1861951 : Nat := 118140960795 + 1861951 * 2 ^ 59
def prefixEnd_1861951 : Nat := 4983230072969 + 3 ^ 40 * 1861951 * 2
def baseEnd_1861951 : Nat := 318691939373249947283183

theorem tailTrace_1861951 : CollatzResearch.WordTrace tailWord_1861951 prefixEnd_1861951 318691939373249947283183 := by
  unfold tailWord_1861951
  simp only [CollatzResearch.WordTrace]
  refine ⟨67910932077476997758961707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45273954718317998505974471 67910932077476997758961707)
  ·
    refine ⟨101866398116215496638442561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67910932077476997758961707 101866398116215496638442561)
    ·
      refine ⟨76399798587161622478831921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101866398116215496638442561 76399798587161622478831921)
      ·
        refine ⟨57299848940371216859123941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76399798587161622478831921 57299848940371216859123941)
        ·
          refine ⟨10743721676319603161085739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57299848940371216859123941 10743721676319603161085739)
          ·
            refine ⟨16115582514479404741628609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10743721676319603161085739 16115582514479404741628609)
            ·
              refine ⟨12086686885859553556221457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16115582514479404741628609 12086686885859553556221457)
              ·
                refine ⟨9065015164394665167166093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12086686885859553556221457 9065015164394665167166093)
                ·
                  refine ⟨3399380686647999437687285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9065015164394665167166093 3399380686647999437687285)
                  ·
                    refine ⟨318691939373249947283183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3399380686647999437687285 318691939373249947283183)
                    ·
                      rfl

theorem cell23_1861951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_1861951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861951 prefixEnd_1861951 := by exact prefixLift 1861951
  have htrace : WordTrace (prefixWord ++ tailWord_1861951) baseStart_1861951 baseEnd_1861951 := by
    simpa [prefixWord, tailWord_1861951, baseEnd_1861951] using wordTrace_append hprefix tailTrace_1861951
  have hstable : (prefixWord ++ tailWord_1861951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861951).length < 2 ^ (prefixWord ++ tailWord_1861951).sum := by decide
  have hdescent : baseEnd_1861951 < baseStart_1861951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861968 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 1, 5]
def baseStart_1861968 : Nat := 118140960795 + 1861968 * 2 ^ 59
def prefixEnd_1861968 : Nat := 4983230072969 + 3 ^ 40 * 1861968 * 2
def baseEnd_1861968 : Nat := 318694849096958758445657

theorem tailTrace_1861968 : CollatzResearch.WordTrace tailWord_1861968 prefixEnd_1861968 318694849096958758445657 := by
  unfold tailWord_1861968
  simp only [CollatzResearch.WordTrace]
  refine ⟨33955776059207704831165279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45274368078943606441553705 33955776059207704831165279)
  ·
    refine ⟨50933664088811557246747919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33955776059207704831165279 50933664088811557246747919)
    ·
      refine ⟨76400496133217335870121879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50933664088811557246747919 76400496133217335870121879)
      ·
        refine ⟨114600744199826003805182819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76400496133217335870121879 114600744199826003805182819)
        ·
          refine ⟨171901116299739005707774229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114600744199826003805182819 171901116299739005707774229)
          ·
            refine ⟨8057864826550265892551917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171901116299739005707774229 8057864826550265892551917)
            ·
              refine ⟨3021699309956349709706969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8057864826550265892551917 3021699309956349709706969)
              ·
                refine ⟨2266274482467262282280227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021699309956349709706969 2266274482467262282280227)
                ·
                  refine ⟨3399411723700893423420341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266274482467262282280227 3399411723700893423420341)
                  ·
                    refine ⟨318694849096958758445657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3399411723700893423420341 318694849096958758445657)
                    ·
                      rfl

theorem cell23_1861968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_1861968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861968 prefixEnd_1861968 := by exact prefixLift 1861968
  have htrace : WordTrace (prefixWord ++ tailWord_1861968) baseStart_1861968 baseEnd_1861968 := by
    simpa [prefixWord, tailWord_1861968, baseEnd_1861968] using wordTrace_append hprefix tailTrace_1861968
  have hstable : (prefixWord ++ tailWord_1861968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861968).length < 2 ^ (prefixWord ++ tailWord_1861968).sum := by decide
  have hdescent : baseEnd_1861968 < baseStart_1861968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861975 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 2, 3, 2]
def baseStart_1861975 : Nat := 118140960795 + 1861975 * 2 ^ 59
def prefixEnd_1861975 : Nat := 4983230072969 + 3 ^ 40 * 1861975 * 2
def baseEnd_1861975 : Nat := 956088141655457747949439

theorem tailTrace_1861975 : CollatzResearch.WordTrace tailWord_1861975 prefixEnd_1861975 956088141655457747949439 := by
  unfold tailWord_1861975
  simp only [CollatzResearch.WordTrace]
  refine ⟨67911807429390049857835379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45274538286260033238556919 67911807429390049857835379)
  ·
    refine ⟨101867711144085074786753069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67911807429390049857835379 101867711144085074786753069)
    ·
      refine ⟨38200391679031903045032401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101867711144085074786753069 38200391679031903045032401)
      ·
        refine ⟨28650293759273927283774301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38200391679031903045032401 28650293759273927283774301)
        ·
          refine ⟨10743860159727722731415363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28650293759273927283774301 10743860159727722731415363)
          ·
            refine ⟨16115790239591584097123045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10743860159727722731415363 16115790239591584097123045)
            ·
              refine ⟨3021710669923422018210571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16115790239591584097123045 3021710669923422018210571)
              ·
                refine ⟨4532566004885133027315857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021710669923422018210571 4532566004885133027315857)
                ·
                  refine ⟨3399424503663849770486893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4532566004885133027315857 3399424503663849770486893)
                  ·
                    refine ⟨1274784188873943663932585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399424503663849770486893 1274784188873943663932585)
                    ·
                      refine ⟨956088141655457747949439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274784188873943663932585 956088141655457747949439)
                      ·
                        rfl

theorem cell23_1861975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_1861975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1861975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1861975 prefixEnd_1861975 := by exact prefixLift 1861975
  have htrace : WordTrace (prefixWord ++ tailWord_1861975) baseStart_1861975 baseEnd_1861975 := by
    simpa [prefixWord, tailWord_1861975, baseEnd_1861975] using wordTrace_append hprefix tailTrace_1861975
  have hstable : (prefixWord ++ tailWord_1861975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861975).length < 2 ^ (prefixWord ++ tailWord_1861975).sum := by decide
  have hdescent : baseEnd_1861975 < baseStart_1861975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862001 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_1862001 : Nat := 118140960795 + 1862001 * 2 ^ 59
def prefixEnd_1862001 : Nat := 4983230072969 + 3 ^ 40 * 1862001 * 2
def baseEnd_1862001 : Nat := 956101492152474646224319

theorem tailTrace_1862001 : CollatzResearch.WordTrace tailWord_1862001 prefixEnd_1862001 956101492152474646224319 := by
  unfold tailWord_1862001
  simp only [CollatzResearch.WordTrace]
  refine ⟨67912755727295856298281857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45275170484863904198854571 67912755727295856298281857)
  ·
    refine ⟨50934566795471892223711393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67912755727295856298281857 50934566795471892223711393)
    ·
      refine ⟨38200925096603919167783545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50934566795471892223711393 38200925096603919167783545)
      ·
        refine ⟨28650693822452939375837659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38200925096603919167783545 28650693822452939375837659)
        ·
          refine ⟨42976040733679409063756489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28650693822452939375837659 42976040733679409063756489)
          ·
            refine ⟨32232030550259556797817367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42976040733679409063756489 32232030550259556797817367)
            ·
              refine ⟨48348045825389335196726051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32232030550259556797817367 48348045825389335196726051)
              ·
                refine ⟨72522068738084002795089077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48348045825389335196726051 72522068738084002795089077)
                ·
                  refine ⟨6798943944195375262039601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72522068738084002795089077 6798943944195375262039601)
                  ·
                    refine ⟨5099207958146531446529701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6798943944195375262039601 5099207958146531446529701)
                    ·
                      refine ⟨956101492152474646224319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5099207958146531446529701 956101492152474646224319)
                      ·
                        rfl

theorem cell23_1862001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_1862001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862001 prefixEnd_1862001 := by exact prefixLift 1862001
  have htrace : WordTrace (prefixWord ++ tailWord_1862001) baseStart_1862001 baseEnd_1862001 := by
    simpa [prefixWord, tailWord_1862001, baseEnd_1862001] using wordTrace_append hprefix tailTrace_1862001
  have hstable : (prefixWord ++ tailWord_1862001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862001).length < 2 ^ (prefixWord ++ tailWord_1862001).sum := by decide
  have hdescent : baseEnd_1862001 < baseStart_1862001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862011 : List Nat := [1, 1, 1, 1, 1, 7, 3, 8]
def baseStart_1862011 : Nat := 118140960795 + 1862011 * 2 ^ 59
def prefixEnd_1862011 : Nat := 4983230072969 + 3 ^ 40 * 1862011 * 2
def baseEnd_1862011 : Nat := 35411356554037763225899

theorem tailTrace_1862011 : CollatzResearch.WordTrace tailWord_1862011 prefixEnd_1862011 35411356554037763225899 := by
  unfold tailWord_1862011
  simp only [CollatzResearch.WordTrace]
  refine ⟨67913120457259628006145887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45275413638173085337430591 67913120457259628006145887)
  ·
    refine ⟨101869680685889442009218831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67913120457259628006145887 101869680685889442009218831)
    ·
      refine ⟨152804521028834163013828247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101869680685889442009218831 152804521028834163013828247)
      ·
        refine ⟨229206781543251244520742371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152804521028834163013828247 229206781543251244520742371)
        ·
          refine ⟨343810172314876866781113557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229206781543251244520742371 343810172314876866781113557)
          ·
            refine ⟨8058050913629926565182349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 343810172314876866781113557 8058050913629926565182349)
            ·
              refine ⟨3021769092611222461943381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8058050913629926565182349 3021769092611222461943381)
              ·
                refine ⟨35411356554037763225899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3021769092611222461943381 35411356554037763225899)
                ·
                  rfl

theorem cell23_1862011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 8].length) (baseStart_1862011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862011 prefixEnd_1862011 := by exact prefixLift 1862011
  have htrace : WordTrace (prefixWord ++ tailWord_1862011) baseStart_1862011 baseEnd_1862011 := by
    simpa [prefixWord, tailWord_1862011, baseEnd_1862011] using wordTrace_append hprefix tailTrace_1862011
  have hstable : (prefixWord ++ tailWord_1862011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862011).length < 2 ^ (prefixWord ++ tailWord_1862011).sum := by decide
  have hdescent : baseEnd_1862011 < baseStart_1862011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862026 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1862026 : Nat := 118140960795 + 1862026 * 2 ^ 59
def prefixEnd_1862026 : Nat := 4983230072969 + 3 ^ 40 * 1862026 * 2
def baseEnd_1862026 : Nat := 956114329168837048411705

theorem tailTrace_1862026 : CollatzResearch.WordTrace tailWord_1862026 prefixEnd_1862026 956114329168837048411705 := by
  unfold tailWord_1862026
  simp only [CollatzResearch.WordTrace]
  refine ⟨16978416888051321391985483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45275778368136857045294621 16978416888051321391985483)
  ·
    refine ⟨25467625332076982087978225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16978416888051321391985483 25467625332076982087978225)
    ·
      refine ⟨19100718999057736565983669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25467625332076982087978225 19100718999057736565983669)
      ·
        refine ⟨1790692406161662803060969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19100718999057736565983669 1790692406161662803060969)
        ·
          refine ⟨1343019304621247102295727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1790692406161662803060969 1343019304621247102295727)
          ·
            refine ⟨2014528956931870653443591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343019304621247102295727 2014528956931870653443591)
            ·
              refine ⟨3021793435397805980165387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014528956931870653443591 3021793435397805980165387)
              ·
                refine ⟨4532690153096708970248081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021793435397805980165387 4532690153096708970248081)
                ·
                  refine ⟨3399517614822531727686061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4532690153096708970248081 3399517614822531727686061)
                  ·
                    refine ⟨1274819105558449397882273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399517614822531727686061 1274819105558449397882273)
                    ·
                      refine ⟨956114329168837048411705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274819105558449397882273 956114329168837048411705)
                      ·
                        rfl

theorem cell23_1862026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1862026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862026 prefixEnd_1862026 := by exact prefixLift 1862026
  have htrace : WordTrace (prefixWord ++ tailWord_1862026) baseStart_1862026 baseEnd_1862026 := by
    simpa [prefixWord, tailWord_1862026, baseEnd_1862026] using wordTrace_append hprefix tailTrace_1862026
  have hstable : (prefixWord ++ tailWord_1862026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862026).length < 2 ^ (prefixWord ++ tailWord_1862026).sum := by decide
  have hdescent : baseEnd_1862026 < baseStart_1862026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862028 : List Nat := [2, 2, 1, 2, 1, 5, 3, 7]
def baseStart_1862028 : Nat := 118140960795 + 1862028 * 2 ^ 59
def prefixEnd_1862028 : Nat := 4983230072969 + 3 ^ 40 * 1862028 * 2
def baseEnd_1862028 : Nat := 35411679856672075577285

theorem tailTrace_1862028 : CollatzResearch.WordTrace tailWord_1862028 prefixEnd_1862028 35411679856672075577285 := by
  unfold tailWord_1862028
  simp only [CollatzResearch.WordTrace]
  refine ⟨33956870249099019954757369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45275826998798693273009825 33956870249099019954757369)
  ·
    refine ⟨25467652686824264966068027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33956870249099019954757369 25467652686824264966068027)
    ·
      refine ⟨38201479030236397449102041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25467652686824264966068027 38201479030236397449102041)
      ·
        refine ⟨28651109272677298086826531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38201479030236397449102041 28651109272677298086826531)
        ·
          refine ⟨42976663909015947130239797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28651109272677298086826531 42976663909015947130239797)
          ·
            refine ⟨4029062241470245043459981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42976663909015947130239797 4029062241470245043459981)
            ·
              refine ⟨1510898340551341891297493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4029062241470245043459981 1510898340551341891297493)
              ·
                refine ⟨35411679856672075577285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1510898340551341891297493 35411679856672075577285)
                ·
                  rfl

theorem cell23_1862028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 7].length) (baseStart_1862028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862028 prefixEnd_1862028 := by exact prefixLift 1862028
  have htrace : WordTrace (prefixWord ++ tailWord_1862028) baseStart_1862028 baseEnd_1862028 := by
    simpa [prefixWord, tailWord_1862028, baseEnd_1862028] using wordTrace_append hprefix tailTrace_1862028
  have hstable : (prefixWord ++ tailWord_1862028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862028).length < 2 ^ (prefixWord ++ tailWord_1862028).sum := by decide
  have hdescent : baseEnd_1862028 < baseStart_1862028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862042 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3]
def baseStart_1862042 : Nat := 118140960795 + 1862042 * 2 ^ 59
def prefixEnd_1862042 : Nat := 4983230072969 + 3 ^ 40 * 1862042 * 2
def baseEnd_1862042 : Nat := 956122544859308985811631

theorem tailTrace_1862042 : CollatzResearch.WordTrace tailWord_1862042 prefixEnd_1862042 956122544859308985811631 := by
  unfold tailWord_1862042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16978562780036830075131095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45276167413431546867016253 16978562780036830075131095)
  ·
    refine ⟨25467844170055245112696643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16978562780036830075131095 25467844170055245112696643)
    ·
      refine ⟨38201766255082867669044965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25467844170055245112696643 38201766255082867669044965)
      ·
        refine ⟨7162831172828037687945931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38201766255082867669044965 7162831172828037687945931)
        ·
          refine ⟨10744246759242056531918897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7162831172828037687945931 10744246759242056531918897)
          ·
            refine ⟨8058185069431542398939173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10744246759242056531918897 8058185069431542398939173)
            ·
              refine ⟨1510909700518414199801095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8058185069431542398939173 1510909700518414199801095)
              ·
                refine ⟨2266364550777621299701643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510909700518414199801095 2266364550777621299701643)
                ·
                  refine ⟨3399546826166431949552465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266364550777621299701643 3399546826166431949552465)
                  ·
                    refine ⟨2549660119624823962164349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3399546826166431949552465 2549660119624823962164349)
                    ·
                      refine ⟨956122544859308985811631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2549660119624823962164349 956122544859308985811631)
                      ·
                        rfl

theorem cell23_1862042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_1862042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862042 prefixEnd_1862042 := by exact prefixLift 1862042
  have htrace : WordTrace (prefixWord ++ tailWord_1862042) baseStart_1862042 baseEnd_1862042 := by
    simpa [prefixWord, tailWord_1862042, baseEnd_1862042] using wordTrace_append hprefix tailTrace_1862042
  have hstable : (prefixWord ++ tailWord_1862042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862042).length < 2 ^ (prefixWord ++ tailWord_1862042).sum := by decide
  have hdescent : baseEnd_1862042 < baseStart_1862042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862049 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 2, 4]
def baseStart_1862049 : Nat := 118140960795 + 1862049 * 2 ^ 59
def prefixEnd_1862049 : Nat := 4983230072969 + 3 ^ 40 * 1862049 * 2
def baseEnd_1862049 : Nat := 318708713074630152808033

theorem tailTrace_1862049 : CollatzResearch.WordTrace tailWord_1862049 prefixEnd_1862049 318708713074630152808033 := by
  unfold tailWord_1862049
  simp only [CollatzResearch.WordTrace]
  refine ⟨67914506431121960496029201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45276337620747973664019467 67914506431121960496029201)
  ·
    refine ⟨50935879823341470372021901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67914506431121960496029201 50935879823341470372021901)
    ·
      refine ⟨19100954933753051389508213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50935879823341470372021901 19100954933753051389508213)
      ·
        refine ⟨1790714525039348567766395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19100954933753051389508213 1790714525039348567766395)
        ·
          refine ⟨2686071787559022851649593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790714525039348567766395 2686071787559022851649593)
          ·
            refine ⟨2014553840669267138737195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686071787559022851649593 2014553840669267138737195)
            ·
              refine ⟨3021830761003900708105793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014553840669267138737195 3021830761003900708105793)
              ·
                refine ⟨2266373070752925531079345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021830761003900708105793 2266373070752925531079345)
                ·
                  refine ⟨1699779803064694148309509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266373070752925531079345 1699779803064694148309509)
                  ·
                    refine ⟨318708713074630152808033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1699779803064694148309509 318708713074630152808033)
                    ·
                      rfl

theorem cell23_1862049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_1862049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862049 prefixEnd_1862049 := by exact prefixLift 1862049
  have htrace : WordTrace (prefixWord ++ tailWord_1862049) baseStart_1862049 baseEnd_1862049 := by
    simpa [prefixWord, tailWord_1862049, baseEnd_1862049] using wordTrace_append hprefix tailTrace_1862049
  have hstable : (prefixWord ++ tailWord_1862049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862049).length < 2 ^ (prefixWord ++ tailWord_1862049).sum := by decide
  have hdescent : baseEnd_1862049 < baseStart_1862049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862056 : List Nat := [2, 1, 6, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1862056 : Nat := 118140960795 + 1862056 * 2 ^ 59
def prefixEnd_1862056 : Nat := 4983230072969 + 3 ^ 40 * 1862056 * 2
def baseEnd_1862056 : Nat := 956129733588471931036567

theorem tailTrace_1862056 : CollatzResearch.WordTrace tailWord_1862056 prefixEnd_1862056 956129733588471931036567 := by
  unfold tailWord_1862056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33957380871048300345767011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45276507828064400461022681 33957380871048300345767011)
  ·
    refine ⟨50936071306572450518650517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33957380871048300345767011 50936071306572450518650517)
    ·
      refine ⟨2387628342495583618061743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50936071306572450518650517 2387628342495583618061743)
      ·
        refine ⟨3581442513743375427092615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387628342495583618061743 3581442513743375427092615)
        ·
          refine ⟨5372163770615063140638923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581442513743375427092615 5372163770615063140638923)
          ·
            refine ⟨8058245655922594710958385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5372163770615063140638923 8058245655922594710958385)
            ·
              refine ⟨6043684241941946033218789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8058245655922594710958385 6043684241941946033218789)
              ·
                refine ⟨1133190795364114881228523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6043684241941946033218789 1133190795364114881228523)
                ·
                  refine ⟨1699786193046172321842785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133190795364114881228523 1699786193046172321842785)
                  ·
                    refine ⟨1274839644784629241382089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1699786193046172321842785 1274839644784629241382089)
                    ·
                      refine ⟨956129733588471931036567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274839644784629241382089 956129733588471931036567)
                      ·
                        rfl

theorem cell23_1862056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1862056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862056 prefixEnd_1862056 := by exact prefixLift 1862056
  have htrace : WordTrace (prefixWord ++ tailWord_1862056) baseStart_1862056 baseEnd_1862056 := by
    simpa [prefixWord, tailWord_1862056, baseEnd_1862056] using wordTrace_append hprefix tailTrace_1862056
  have hstable : (prefixWord ++ tailWord_1862056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862056).length < 2 ^ (prefixWord ++ tailWord_1862056).sum := by decide
  have hdescent : baseEnd_1862056 < baseStart_1862056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862078 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1862078 : Nat := 118140960795 + 1862078 * 2 ^ 59
def prefixEnd_1862078 : Nat := 4983230072969 + 3 ^ 40 * 1862078 * 2
def baseEnd_1862078 : Nat := 956141030162870844961465

theorem tailTrace_1862078 : CollatzResearch.WordTrace tailWord_1862078 prefixEnd_1862078 956141030162870844961465 := by
  unfold tailWord_1862078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489445518502112306104361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45277042765344598965889925 8489445518502112306104361)
  ·
    refine ⟨6367084138876584229578271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8489445518502112306104361 6367084138876584229578271)
    ·
      refine ⟨9550626208314876344367407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6367084138876584229578271 9550626208314876344367407)
      ·
        refine ⟨14325939312472314516551111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9550626208314876344367407 14325939312472314516551111)
        ·
          refine ⟨21488908968708471774826667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14325939312472314516551111 21488908968708471774826667)
          ·
            refine ⟨32233363453062707662240001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21488908968708471774826667 32233363453062707662240001)
            ·
              refine ⟨24175022589797030746680001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32233363453062707662240001 24175022589797030746680001)
              ·
                refine ⟨18131266942347773060010001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24175022589797030746680001 18131266942347773060010001)
                ·
                  refine ⟨13598450206760829795007501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18131266942347773060010001 13598450206760829795007501)
                  ·
                    refine ⟨5099418827535311173127813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13598450206760829795007501 5099418827535311173127813)
                    ·
                      refine ⟨956141030162870844961465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5099418827535311173127813 956141030162870844961465)
                      ·
                        rfl

theorem cell23_1862078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1862078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862078 prefixEnd_1862078 := by exact prefixLift 1862078
  have htrace : WordTrace (prefixWord ++ tailWord_1862078) baseStart_1862078 baseEnd_1862078 := by
    simpa [prefixWord, tailWord_1862078, baseEnd_1862078] using wordTrace_append hprefix tailTrace_1862078
  have hstable : (prefixWord ++ tailWord_1862078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862078).length < 2 ^ (prefixWord ++ tailWord_1862078).sum := by decide
  have hdescent : baseEnd_1862078 < baseStart_1862078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862112 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 2, 2, 2]
def baseStart_1862112 : Nat := 118140960795 + 1862112 * 2 ^ 59
def prefixEnd_1862112 : Nat := 4983230072969 + 3 ^ 40 * 1862112 * 2
def baseEnd_1862112 : Nat := 956158488505123711936309

theorem tailTrace_1862112 : CollatzResearch.WordTrace tailWord_1862112 prefixEnd_1862112 956158488505123711936309 := by
  unfold tailWord_1862112
  simp only [CollatzResearch.WordTrace]
  refine ⟨33958402114946861127786295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45277869486595814837048393 33958402114946861127786295)
  ·
    refine ⟨50937603172420291691679443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33958402114946861127786295 50937603172420291691679443)
    ·
      refine ⟨76406404758630437537519165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50937603172420291691679443 76406404758630437537519165)
      ·
        refine ⟨28652401784486414076569687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76406404758630437537519165 28652401784486414076569687)
        ·
          refine ⟨42978602676729621114854531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28652401784486414076569687 42978602676729621114854531)
          ·
            refine ⟨64467904015094431672281797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42978602676729621114854531 64467904015094431672281797)
            ·
              refine ⟨12087732002830205938552837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64467904015094431672281797 12087732002830205938552837)
              ·
                refine ⟨2266449750530663613478657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12087732002830205938552837 2266449750530663613478657)
                ·
                  refine ⟨1699837312897997710108993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266449750530663613478657 1699837312897997710108993)
                  ·
                    refine ⟨1274877984673498282581745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1699837312897997710108993 1274877984673498282581745)
                    ·
                      refine ⟨956158488505123711936309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274877984673498282581745 956158488505123711936309)
                      ·
                        rfl

theorem cell23_1862112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_1862112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862112 prefixEnd_1862112 := by exact prefixLift 1862112
  have htrace : WordTrace (prefixWord ++ tailWord_1862112) baseStart_1862112 baseEnd_1862112 := by
    simpa [prefixWord, tailWord_1862112, baseEnd_1862112] using wordTrace_append hprefix tailTrace_1862112
  have hstable : (prefixWord ++ tailWord_1862112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862112).length < 2 ^ (prefixWord ++ tailWord_1862112).sum := by decide
  have hdescent : baseEnd_1862112 < baseStart_1862112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862121 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_1862121 : Nat := 118140960795 + 1862121 * 2 ^ 59
def prefixEnd_1862121 : Nat := 4983230072969 + 3 ^ 40 * 1862121 * 2
def baseEnd_1862121 : Nat := 956163109831014176723767

theorem tailTrace_1862121 : CollatzResearch.WordTrace tailWord_1862121 prefixEnd_1862121 956163109831014176723767 := by
  unfold tailWord_1862121
  simp only [CollatzResearch.WordTrace]
  refine ⟨67917132486861116792650217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45278088324574077861766811 67917132486861116792650217)
  ·
    refine ⟨50937849365145837594487663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67917132486861116792650217 50937849365145837594487663)
    ·
      refine ⟨76406774047718756391731495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50937849365145837594487663 76406774047718756391731495)
      ·
        refine ⟨114610161071578134587597243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76406774047718756391731495 114610161071578134587597243)
        ·
          refine ⟨171915241607367201881395865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114610161071578134587597243 171915241607367201881395865)
          ·
            refine ⟨128936431205525401411046899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171915241607367201881395865 128936431205525401411046899)
            ·
              refine ⟨193404646808288102116570349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128936431205525401411046899 193404646808288102116570349)
              ·
                refine ⟨72526742553108038293713881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193404646808288102116570349 72526742553108038293713881)
                ·
                  refine ⟨54395056914831028720285411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72526742553108038293713881 54395056914831028720285411)
                  ·
                    refine ⟨81592585372246543080428117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54395056914831028720285411 81592585372246543080428117)
                    ·
                      refine ⟨956163109831014176723767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 81592585372246543080428117 956163109831014176723767)
                      ·
                        rfl

theorem cell23_1862121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_1862121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862121 prefixEnd_1862121 := by exact prefixLift 1862121
  have htrace : WordTrace (prefixWord ++ tailWord_1862121) baseStart_1862121 baseEnd_1862121 := by
    simpa [prefixWord, tailWord_1862121, baseEnd_1862121] using wordTrace_append hprefix tailTrace_1862121
  have hstable : (prefixWord ++ tailWord_1862121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862121).length < 2 ^ (prefixWord ++ tailWord_1862121).sum := by decide
  have hdescent : baseEnd_1862121 < baseStart_1862121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862128 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 3]
def baseStart_1862128 : Nat := 118140960795 + 1862128 * 2 ^ 59
def prefixEnd_1862128 : Nat := 4983230072969 + 3 ^ 40 * 1862128 * 2
def baseEnd_1862128 : Nat := 956166704195595649336235

theorem tailTrace_1862128 : CollatzResearch.WordTrace tailWord_1862128 prefixEnd_1862128 956166704195595649336235 := by
  unfold tailWord_1862128
  simp only [CollatzResearch.WordTrace]
  refine ⟨33958693898917878494077519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45278258531890504658770025 33958693898917878494077519)
  ·
    refine ⟨50938040848376817741116279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33958693898917878494077519 50938040848376817741116279)
    ·
      refine ⟨76407061272565226611674419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50938040848376817741116279 76407061272565226611674419)
      ·
        refine ⟨114610591908847839917511629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76407061272565226611674419 114610591908847839917511629)
        ·
          refine ⟨42978971965817939969066861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114610591908847839917511629 42978971965817939969066861)
          ·
            refine ⟨16117114487181727488400073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42978971965817939969066861 16117114487181727488400073)
            ·
              refine ⟨12087835865386295616300055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16117114487181727488400073 12087835865386295616300055)
              ·
                refine ⟨18131753798079443424450083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12087835865386295616300055 18131753798079443424450083)
                ·
                  refine ⟨27197630697119165136675125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18131753798079443424450083 27197630697119165136675125)
                  ·
                    refine ⟨2549777877854921731563293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27197630697119165136675125 2549777877854921731563293)
                    ·
                      refine ⟨956166704195595649336235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2549777877854921731563293 956166704195595649336235)
                      ·
                        rfl

theorem cell23_1862128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_1862128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862128 prefixEnd_1862128 := by exact prefixLift 1862128
  have htrace : WordTrace (prefixWord ++ tailWord_1862128) baseStart_1862128 baseEnd_1862128 := by
    simpa [prefixWord, tailWord_1862128, baseEnd_1862128] using wordTrace_append hprefix tailTrace_1862128
  have hstable : (prefixWord ++ tailWord_1862128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862128).length < 2 ^ (prefixWord ++ tailWord_1862128).sum := by decide
  have hdescent : baseEnd_1862128 < baseStart_1862128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862133 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1862133 : Nat := 118140960795 + 1862133 * 2 ^ 59
def prefixEnd_1862133 : Nat := 4983230072969 + 3 ^ 40 * 1862133 * 2
def baseEnd_1862133 : Nat := 956169271598868129773713

theorem tailTrace_1862133 : CollatzResearch.WordTrace tailWord_1862133 prefixEnd_1862133 956169271598868129773713 := by
  unfold tailWord_1862133
  simp only [CollatzResearch.WordTrace]
  refine ⟨67917570162817642842087053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45278380108545095228058035 67917570162817642842087053)
  ·
    refine ⟨25469088811056616065782645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67917570162817642842087053 25469088811056616065782645)
    ·
      refine ⟨2387727076036557756167123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25469088811056616065782645 2387727076036557756167123)
      ·
        refine ⟨3581590614054836634250685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387727076036557756167123 3581590614054836634250685)
        ·
          refine ⟨1343096480270563737844007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3581590614054836634250685 1343096480270563737844007)
          ·
            refine ⟨2014644720405845606766011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343096480270563737844007 2014644720405845606766011)
            ·
              refine ⟨3021967080608768410149017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014644720405845606766011 3021967080608768410149017)
              ·
                refine ⟨2266475310456576307611763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021967080608768410149017 2266475310456576307611763)
                ·
                  refine ⟨3399712965684864461417645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266475310456576307611763 3399712965684864461417645)
                  ·
                    refine ⟨1274892362131824173031617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399712965684864461417645 1274892362131824173031617)
                    ·
                      refine ⟨956169271598868129773713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274892362131824173031617 956169271598868129773713)
                      ·
                        rfl

theorem cell23_1862133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1862133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862133 prefixEnd_1862133 := by exact prefixLift 1862133
  have htrace : WordTrace (prefixWord ++ tailWord_1862133) baseStart_1862133 baseEnd_1862133 := by
    simpa [prefixWord, tailWord_1862133, baseEnd_1862133] using wordTrace_append hprefix tailTrace_1862133
  have hstable : (prefixWord ++ tailWord_1862133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862133).length < 2 ^ (prefixWord ++ tailWord_1862133).sum := by decide
  have hdescent : baseEnd_1862133 < baseStart_1862133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862150 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1862150 : Nat := 118140960795 + 1862150 * 2 ^ 59
def prefixEnd_1862150 : Nat := 4983230072969 + 3 ^ 40 * 1862150 * 2
def baseEnd_1862150 : Nat := 956178000769994563261135

theorem tailTrace_1862150 : CollatzResearch.WordTrace tailWord_1862150 prefixEnd_1862150 956178000769994563261135 := by
  unfold tailWord_1862150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122443443867376710795497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45278793469170703163637269 2122443443867376710795497)
  ·
    refine ⟨1591832582900532533096623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2122443443867376710795497 1591832582900532533096623)
    ·
      refine ⟨2387748874350798799644935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591832582900532533096623 2387748874350798799644935)
      ·
        refine ⟨3581623311526198199467403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387748874350798799644935 3581623311526198199467403)
        ·
          refine ⟨5372434967289297299201105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581623311526198199467403 5372434967289297299201105)
          ·
            refine ⟨4029326225466972974400829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5372434967289297299201105 4029326225466972974400829)
            ·
              refine ⟨1510997334550114865400311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4029326225466972974400829 1510997334550114865400311)
              ·
                refine ⟨2266496001825172298100467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510997334550114865400311 2266496001825172298100467)
                ·
                  refine ⟨3399744002737758447150701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266496001825172298100467 3399744002737758447150701)
                  ·
                    refine ⟨1274904001026659417681513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399744002737758447150701 1274904001026659417681513)
                    ·
                      refine ⟨956178000769994563261135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1274904001026659417681513 956178000769994563261135)
                      ·
                        rfl

theorem cell23_1862150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1862150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862150 prefixEnd_1862150 := by exact prefixLift 1862150
  have htrace : WordTrace (prefixWord ++ tailWord_1862150) baseStart_1862150 baseEnd_1862150 := by
    simpa [prefixWord, tailWord_1862150, baseEnd_1862150] using wordTrace_append hprefix tailTrace_1862150
  have hstable : (prefixWord ++ tailWord_1862150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862150).length < 2 ^ (prefixWord ++ tailWord_1862150).sum := by decide
  have hdescent : baseEnd_1862150 < baseStart_1862150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862178 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1862178 : Nat := 118140960795 + 1862178 * 2 ^ 59
def prefixEnd_1862178 : Nat := 4983230072969 + 3 ^ 40 * 1862178 * 2
def baseEnd_1862178 : Nat := 318730792742773484570335

theorem tailTrace_1862178 : CollatzResearch.WordTrace tailWord_1862178 prefixEnd_1862178 318730792742773484570335 := by
  unfold tailWord_1862178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16979802861913653881868797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45279474298436410351650125 16979802861913653881868797)
  ·
    refine ⟨6367426073217620205700799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16979802861913653881868797 6367426073217620205700799)
    ·
      refine ⟨9551139109826430308551199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6367426073217620205700799 9551139109826430308551199)
      ·
        refine ⟨14326708664739645462826799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9551139109826430308551199 14326708664739645462826799)
        ·
          refine ⟨21490062997109468194240199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14326708664739645462826799 21490062997109468194240199)
          ·
            refine ⟨32235094495664202291360299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21490062997109468194240199 32235094495664202291360299)
            ·
              refine ⟨48352641743496303437040449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32235094495664202291360299 48352641743496303437040449)
              ·
                refine ⟨36264481307622227577780337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48352641743496303437040449 36264481307622227577780337)
                ·
                  refine ⟨27198360980716670683335253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36264481307622227577780337 27198360980716670683335253)
                  ·
                    refine ⟨318730792742773484570335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27198360980716670683335253 318730792742773484570335)
                    ·
                      rfl

theorem cell23_1862178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1862178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862178 prefixEnd_1862178 := by exact prefixLift 1862178
  have htrace : WordTrace (prefixWord ++ tailWord_1862178) baseStart_1862178 baseEnd_1862178 := by
    simpa [prefixWord, tailWord_1862178, baseEnd_1862178] using wordTrace_append hprefix tailTrace_1862178
  have hstable : (prefixWord ++ tailWord_1862178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862178).length < 2 ^ (prefixWord ++ tailWord_1862178).sum := by decide
  have hdescent : baseEnd_1862178 < baseStart_1862178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862195 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 3, 4]
def baseStart_1862195 : Nat := 118140960795 + 1862195 * 2 ^ 59
def prefixEnd_1862195 : Nat := 4983230072969 + 3 ^ 40 * 1862195 * 2
def baseEnd_1862195 : Nat := 318733702466482295732809

theorem tailTrace_1862195 : CollatzResearch.WordTrace tailWord_1862195 prefixEnd_1862195 318733702466482295732809 := by
  unfold tailWord_1862195
  simp only [CollatzResearch.WordTrace]
  refine ⟨67919831488593027430844039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45279887659062018287229359 67919831488593027430844039)
  ·
    refine ⟨101879747232889541146266059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67919831488593027430844039 101879747232889541146266059)
    ·
      refine ⟨152819620849334311719399089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101879747232889541146266059 152819620849334311719399089)
      ·
        refine ⟨114614715637000733789549317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152819620849334311719399089 114614715637000733789549317)
        ·
          refine ⟨21490259181937637585540497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114614715637000733789549317 21490259181937637585540497)
          ·
            refine ⟨16117694386453228189155373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21490259181937637585540497 16117694386453228189155373)
            ·
              refine ⟨6044135394919960570933265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16117694386453228189155373 6044135394919960570933265)
              ·
                refine ⟨4533101546189970428199949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044135394919960570933265 4533101546189970428199949)
                ·
                  refine ⟨1699913079821238910574981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4533101546189970428199949 1699913079821238910574981)
                  ·
                    refine ⟨318733702466482295732809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1699913079821238910574981 318733702466482295732809)
                    ·
                      rfl

theorem cell23_1862195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 4].length) (baseStart_1862195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862195 prefixEnd_1862195 := by exact prefixLift 1862195
  have htrace : WordTrace (prefixWord ++ tailWord_1862195) baseStart_1862195 baseEnd_1862195 := by
    simpa [prefixWord, tailWord_1862195, baseEnd_1862195] using wordTrace_append hprefix tailTrace_1862195
  have hstable : (prefixWord ++ tailWord_1862195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862195).length < 2 ^ (prefixWord ++ tailWord_1862195).sum := by decide
  have hdescent : baseEnd_1862195 < baseStart_1862195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862202 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_1862202 : Nat := 118140960795 + 1862202 * 2 ^ 59
def prefixEnd_1862202 : Nat := 4983230072969 + 3 ^ 40 * 1862202 * 2
def baseEnd_1862202 : Nat := 956204701764028359810895

theorem tailTrace_1862202 : CollatzResearch.WordTrace tailWord_1862202 prefixEnd_1862202 956204701764028359810895 := by
  unfold tailWord_1862202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16980021699891916906587215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45280057866378445084232573 16980021699891916906587215)
  ·
    refine ⟨25470032549837875359880823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16980021699891916906587215 25470032549837875359880823)
    ·
      refine ⟨38205048824756813039821235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25470032549837875359880823 38205048824756813039821235)
      ·
        refine ⟨57307573237135219559731853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38205048824756813039821235 57307573237135219559731853)
        ·
          refine ⟨21490339963925707334899445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57307573237135219559731853 21490339963925707334899445)
          ·
            refine ⟨2014719371618035062646823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21490339963925707334899445 2014719371618035062646823)
            ·
              refine ⟨3022079057427052593970235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014719371618035062646823 3022079057427052593970235)
              ·
                refine ⟨4533118586140578890955353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022079057427052593970235 4533118586140578890955353)
                ·
                  refine ⟨3399838939605434168216515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4533118586140578890955353 3399838939605434168216515)
                  ·
                    refine ⟨5099758409408151252324773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3399838939605434168216515 5099758409408151252324773)
                    ·
                      refine ⟨956204701764028359810895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5099758409408151252324773 956204701764028359810895)
                      ·
                        rfl

theorem cell23_1862202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_1862202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862202 prefixEnd_1862202 := by exact prefixLift 1862202
  have htrace : WordTrace (prefixWord ++ tailWord_1862202) baseStart_1862202 baseEnd_1862202 := by
    simpa [prefixWord, tailWord_1862202, baseEnd_1862202] using wordTrace_append hprefix tailTrace_1862202
  have hstable : (prefixWord ++ tailWord_1862202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862202).length < 2 ^ (prefixWord ++ tailWord_1862202).sum := by decide
  have hdescent : baseEnd_1862202 < baseStart_1862202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862225 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 6]
def baseStart_1862225 : Nat := 118140960795 + 1862225 * 2 ^ 59
def prefixEnd_1862225 : Nat := 4983230072969 + 3 ^ 40 * 1862225 * 2
def baseEnd_1862225 : Nat := 106246279091009085535921

theorem tailTrace_1862225 : CollatzResearch.WordTrace tailWord_1862225 prefixEnd_1862225 106246279091009085535921 := by
  unfold tailWord_1862225
  simp only [CollatzResearch.WordTrace]
  refine ⟨67920925678484342554436129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45280617118989561702957419 67920925678484342554436129)
  ·
    refine ⟨50940694258863256915827097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67920925678484342554436129 50940694258863256915827097)
    ·
      refine ⟨38205520694147442686870323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50940694258863256915827097 38205520694147442686870323)
      ·
        refine ⟨57308281041221164030305485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38205520694147442686870323 57308281041221164030305485)
        ·
          refine ⟨21490605390457936511364557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57308281041221164030305485 21490605390457936511364557)
          ·
            refine ⟨8058977021421726191761709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21490605390457936511364557 8058977021421726191761709)
            ·
              refine ⟨3022116383033147321910641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8058977021421726191761709 3022116383033147321910641)
              ·
                refine ⟨2266587287274860491432981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022116383033147321910641 2266587287274860491432981)
                ·
                  refine ⟨106246279091009085535921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2266587287274860491432981 106246279091009085535921)
                  ·
                    rfl

theorem cell23_1862225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 6].length) (baseStart_1862225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862225 prefixEnd_1862225 := by exact prefixLift 1862225
  have htrace : WordTrace (prefixWord ++ tailWord_1862225) baseStart_1862225 baseEnd_1862225 := by
    simpa [prefixWord, tailWord_1862225, baseEnd_1862225] using wordTrace_append hprefix tailTrace_1862225
  have hstable : (prefixWord ++ tailWord_1862225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862225).length < 2 ^ (prefixWord ++ tailWord_1862225).sum := by decide
  have hdescent : baseEnd_1862225 < baseStart_1862225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862252 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_1862252 : Nat := 118140960795 + 1862252 * 2 ^ 59
def prefixEnd_1862252 : Nat := 4983230072969 + 3 ^ 40 * 1862252 * 2
def baseEnd_1862252 : Nat := 956230375796753164185665

theorem tailTrace_1862252 : CollatzResearch.WordTrace tailWord_1862252 prefixEnd_1862252 956230375796753164185665 := by
  unfold tailWord_1862252
  simp only [CollatzResearch.WordTrace]
  refine ⟨33960955224693263082834505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45281273632924350777112673 33960955224693263082834505)
  ·
    refine ⟨25470716418519947312125879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33960955224693263082834505 25470716418519947312125879)
    ·
      refine ⟨38206074627779920968188819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25470716418519947312125879 38206074627779920968188819)
      ·
        refine ⟨57309111941669881452283229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38206074627779920968188819 57309111941669881452283229)
        ·
          refine ⟨21490916978126205544606211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57309111941669881452283229 21490916978126205544606211)
          ·
            refine ⟨32236375467189308316909317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21490916978126205544606211 32236375467189308316909317)
            ·
              refine ⟨6044320400097995309420497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32236375467189308316909317 6044320400097995309420497)
              ·
                refine ⟨4533240300073496482065373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044320400097995309420497 4533240300073496482065373)
                ·
                  refine ⟨1699965112527561180774515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4533240300073496482065373 1699965112527561180774515)
                  ·
                    refine ⟨2549947668791341771161773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1699965112527561180774515 2549947668791341771161773)
                    ·
                      refine ⟨956230375796753164185665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2549947668791341771161773 956230375796753164185665)
                      ·
                        rfl

theorem cell23_1862252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_1862252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862252 prefixEnd_1862252 := by exact prefixLift 1862252
  have htrace : WordTrace (prefixWord ++ tailWord_1862252) baseStart_1862252 baseEnd_1862252 := by
    simpa [prefixWord, tailWord_1862252, baseEnd_1862252] using wordTrace_append hprefix tailTrace_1862252
  have hstable : (prefixWord ++ tailWord_1862252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862252).length < 2 ^ (prefixWord ++ tailWord_1862252).sum := by decide
  have hdescent : baseEnd_1862252 < baseStart_1862252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862255 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 1, 5]
def baseStart_1862255 : Nat := 118140960795 + 1862255 * 2 ^ 59
def prefixEnd_1862255 : Nat := 4983230072969 + 3 ^ 40 * 1862255 * 2
def baseEnd_1862255 : Nat := 318743972079572217482717

theorem tailTrace_1862255 : CollatzResearch.WordTrace tailWord_1862255 prefixEnd_1862255 318743972079572217482717 := by
  unfold tailWord_1862255
  simp only [CollatzResearch.WordTrace]
  refine ⟨67922019868375657678028219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45281346578917105118685479 67922019868375657678028219)
  ·
    refine ⟨101883029802563486517042329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67922019868375657678028219 101883029802563486517042329)
    ·
      refine ⟨76412272351922614887781747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101883029802563486517042329 76412272351922614887781747)
      ·
        refine ⟨114618408527883922331672621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76412272351922614887781747 114618408527883922331672621)
        ·
          refine ⟨42981903197956470874377233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114618408527883922331672621 42981903197956470874377233)
          ·
            refine ⟨32236427398467353155782925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42981903197956470874377233 32236427398467353155782925)
            ·
              refine ⟨12088660274425257433418597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32236427398467353155782925 12088660274425257433418597)
              ·
                refine ⟨2266623801454735768765987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12088660274425257433418597 2266623801454735768765987)
                ·
                  refine ⟨3399935702182103653148981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266623801454735768765987 3399935702182103653148981)
                  ·
                    refine ⟨318743972079572217482717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3399935702182103653148981 318743972079572217482717)
                    ·
                      rfl

theorem cell23_1862255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_1862255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862255 prefixEnd_1862255 := by exact prefixLift 1862255
  have htrace : WordTrace (prefixWord ++ tailWord_1862255) baseStart_1862255 baseEnd_1862255 := by
    simpa [prefixWord, tailWord_1862255, baseEnd_1862255] using wordTrace_append hprefix tailTrace_1862255
  have hstable : (prefixWord ++ tailWord_1862255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862255).length < 2 ^ (prefixWord ++ tailWord_1862255).sum := by decide
  have hdescent : baseEnd_1862255 < baseStart_1862255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862295 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1862295 : Nat := 118140960795 + 1862295 * 2 ^ 59
def prefixEnd_1862295 : Nat := 4983230072969 + 3 ^ 40 * 1862295 * 2
def baseEnd_1862295 : Nat := 956252455464896495947967

theorem tailTrace_1862295 : CollatzResearch.WordTrace tailWord_1862295 prefixEnd_1862295 956252455464896495947967 := by
  unfold tailWord_1862295
  simp only [CollatzResearch.WordTrace]
  refine ⟨67923478788230744509484339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45282319192153829672989559 67923478788230744509484339)
  ·
    refine ⟨101885218182346116764226509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67923478788230744509484339 101885218182346116764226509)
    ·
      refine ⟨38206956818379793786584941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101885218182346116764226509 38206956818379793786584941)
      ·
        refine ⟨14327608806892422669969353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38206956818379793786584941 14327608806892422669969353)
        ·
          refine ⟨10745706605169317002477015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14327608806892422669969353 10745706605169317002477015)
          ·
            refine ⟨16118559907753975503715523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745706605169317002477015 16118559907753975503715523)
            ·
              refine ⟨24177839861630963255573285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16118559907753975503715523 24177839861630963255573285)
              ·
                refine ⟨4533344974055805610419991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24177839861630963255573285 4533344974055805610419991)
                ·
                  refine ⟨6800017461083708415629987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533344974055805610419991 6800017461083708415629987)
                  ·
                    refine ⟨10200026191625562623444981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6800017461083708415629987 10200026191625562623444981)
                    ·
                      refine ⟨956252455464896495947967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10200026191625562623444981 956252455464896495947967)
                      ·
                        rfl

theorem cell23_1862295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1862295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862295 prefixEnd_1862295 := by exact prefixLift 1862295
  have htrace : WordTrace (prefixWord ++ tailWord_1862295) baseStart_1862295 baseEnd_1862295 := by
    simpa [prefixWord, tailWord_1862295, baseEnd_1862295] using wordTrace_append hprefix tailTrace_1862295
  have hstable : (prefixWord ++ tailWord_1862295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862295).length < 2 ^ (prefixWord ++ tailWord_1862295).sum := by decide
  have hdescent : baseEnd_1862295 < baseStart_1862295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862302 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1862302 : Nat := 118140960795 + 1862302 * 2 ^ 59
def prefixEnd_1862302 : Nat := 4983230072969 + 3 ^ 40 * 1862302 * 2
def baseEnd_1862302 : Nat := 318752016609825989520145

theorem tailTrace_1862302 : CollatzResearch.WordTrace tailWord_1862302 prefixEnd_1862302 318752016609825989520145 := by
  unfold tailWord_1862302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490466762400673088123645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45282489399470256469992773 8490466762400673088123645)
  ·
    refine ⟨3183925035900252408046367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8490466762400673088123645 3183925035900252408046367)
    ·
      refine ⟨4775887553850378612069551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3183925035900252408046367 4775887553850378612069551)
      ·
        refine ⟨7163831330775567918104327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4775887553850378612069551 7163831330775567918104327)
        ·
          refine ⟨10745746996163351877156491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7163831330775567918104327 10745746996163351877156491)
          ·
            refine ⟨16118620494245027815734737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745746996163351877156491 16118620494245027815734737)
            ·
              refine ⟨12088965370683770861801053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16118620494245027815734737 12088965370683770861801053)
              ·
                refine ⟨4533362014006414073175395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12088965370683770861801053 4533362014006414073175395)
                ·
                  refine ⟨6800043021009621109763093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533362014006414073175395 6800043021009621109763093)
                  ·
                    refine ⟨318752016609825989520145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6800043021009621109763093 318752016609825989520145)
                    ·
                      rfl

theorem cell23_1862302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1862302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862302 prefixEnd_1862302 := by exact prefixLift 1862302
  have htrace : WordTrace (prefixWord ++ tailWord_1862302) baseStart_1862302 baseEnd_1862302 := by
    simpa [prefixWord, tailWord_1862302, baseEnd_1862302] using wordTrace_append hprefix tailTrace_1862302
  have hstable : (prefixWord ++ tailWord_1862302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862302).length < 2 ^ (prefixWord ++ tailWord_1862302).sum := by decide
  have hdescent : baseEnd_1862302 < baseStart_1862302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862337 : List Nat := [1, 2, 6, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1862337 : Nat := 118140960795 + 1862337 * 2 ^ 59
def prefixEnd_1862337 : Nat := 4983230072969 + 3 ^ 40 * 1862337 * 2
def baseEnd_1862337 : Nat := 956274021652385331622775

theorem tailTrace_1862337 : CollatzResearch.WordTrace tailWord_1862337 prefixEnd_1862337 956274021652385331622775 := by
  unfold tailWord_1862337
  simp only [CollatzResearch.WordTrace]
  refine ⟨67925010654078585682513265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45283340436052390455008843 67925010654078585682513265)
  ·
    refine ⟨50943757990558939261884949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67925010654078585682513265 50943757990558939261884949)
    ·
      refine ⟨2387988655807450277900857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50943757990558939261884949 2387988655807450277900857)
      ·
        refine ⟨1790991491855587708425643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2387988655807450277900857 1790991491855587708425643)
        ·
          refine ⟨2686487237783381562638465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790991491855587708425643 2686487237783381562638465)
          ·
            refine ⟨2014865428337536171978849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686487237783381562638465 2014865428337536171978849)
            ·
              refine ⟨1511149071253152128984137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014865428337536171978849 1511149071253152128984137)
              ·
                refine ⟨1133361803439864096738103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511149071253152128984137 1133361803439864096738103)
                ·
                  refine ⟨1700042705159796145107155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133361803439864096738103 1700042705159796145107155)
                  ·
                    refine ⟨2550064057739694217660733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1700042705159796145107155 2550064057739694217660733)
                    ·
                      refine ⟨956274021652385331622775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2550064057739694217660733 956274021652385331622775)
                      ·
                        rfl

theorem cell23_1862337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1862337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862337 prefixEnd_1862337 := by exact prefixLift 1862337
  have htrace : WordTrace (prefixWord ++ tailWord_1862337) baseStart_1862337 baseEnd_1862337 := by
    simpa [prefixWord, tailWord_1862337, baseEnd_1862337] using wordTrace_append hprefix tailTrace_1862337
  have hstable : (prefixWord ++ tailWord_1862337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862337).length < 2 ^ (prefixWord ++ tailWord_1862337).sum := by decide
  have hdescent : baseEnd_1862337 < baseStart_1862337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862359 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_1862359 : Nat := 118140960795 + 1862359 * 2 ^ 59
def prefixEnd_1862359 : Nat := 4983230072969 + 3 ^ 40 * 1862359 * 2
def baseEnd_1862359 : Nat := 956285318226784245547673

theorem tailTrace_1862359 : CollatzResearch.WordTrace tailWord_1862359 prefixEnd_1862359 956285318226784245547673 := by
  unfold tailWord_1862359
  simp only [CollatzResearch.WordTrace]
  refine ⟨67925813059998883439814131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45283875373332588959876087 67925813059998883439814131)
  ·
    refine ⟨101888719589998325159721197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67925813059998883439814131 101888719589998325159721197)
    ·
      refine ⟨38208269846249371934895449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101888719589998325159721197 38208269846249371934895449)
      ·
        refine ⟨28656202384687028951171587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38208269846249371934895449 28656202384687028951171587)
        ·
          refine ⟨42984303577030543426757381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28656202384687028951171587 42984303577030543426757381)
          ·
            refine ⟨8059556920693226892517009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42984303577030543426757381 8059556920693226892517009)
            ·
              refine ⟨6044667690519920169387757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8059556920693226892517009 6044667690519920169387757)
              ·
                refine ⟨2266750383944970063520409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6044667690519920169387757 2266750383944970063520409)
                ·
                  refine ⟨1700062787958727547640307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266750383944970063520409 1700062787958727547640307)
                  ·
                    refine ⟨2550094181938091321460461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1700062787958727547640307 2550094181938091321460461)
                    ·
                      refine ⟨956285318226784245547673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2550094181938091321460461 956285318226784245547673)
                      ·
                        rfl

theorem cell23_1862359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_1862359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862359 prefixEnd_1862359 := by exact prefixLift 1862359
  have htrace : WordTrace (prefixWord ++ tailWord_1862359) baseStart_1862359 baseEnd_1862359 := by
    simpa [prefixWord, tailWord_1862359, baseEnd_1862359] using wordTrace_append hprefix tailTrace_1862359
  have hstable : (prefixWord ++ tailWord_1862359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862359).length < 2 ^ (prefixWord ++ tailWord_1862359).sum := by decide
  have hdescent : baseEnd_1862359 < baseStart_1862359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862369 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_1862369 : Nat := 118140960795 + 1862369 * 2 ^ 59
def prefixEnd_1862369 : Nat := 4983230072969 + 3 ^ 40 * 1862369 * 2
def baseEnd_1862369 : Nat := 956290453033329206422627

theorem tailTrace_1862369 : CollatzResearch.WordTrace tailWord_1862369 prefixEnd_1862369 956290453033329206422627 := by
  unfold tailWord_1862369
  simp only [CollatzResearch.WordTrace]
  refine ⟨67926177789962655147678161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45284118526641770098452107 67926177789962655147678161)
  ·
    refine ⟨50944633342471991360758621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67926177789962655147678161 50944633342471991360758621)
    ·
      refine ⟨19104237503426996760284483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50944633342471991360758621 19104237503426996760284483)
      ·
        refine ⟨28656356255140495140426725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19104237503426996760284483 28656356255140495140426725)
        ·
          refine ⟨5373066797838842838830011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28656356255140495140426725 5373066797838842838830011)
          ·
            refine ⟨8059600196758264258245017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5373066797838842838830011 8059600196758264258245017)
            ·
              refine ⟨6044700147568698193683763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8059600196758264258245017 6044700147568698193683763)
              ·
                refine ⟨9067050221353047290525645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6044700147568698193683763 9067050221353047290525645)
                ·
                  refine ⟨3400143833007392733947117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9067050221353047290525645 3400143833007392733947117)
                  ·
                    refine ⟨1275053937377772275230169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3400143833007392733947117 1275053937377772275230169)
                    ·
                      refine ⟨956290453033329206422627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275053937377772275230169 956290453033329206422627)
                      ·
                        rfl

theorem cell23_1862369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_1862369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862369 prefixEnd_1862369 := by exact prefixLift 1862369
  have htrace : WordTrace (prefixWord ++ tailWord_1862369) baseStart_1862369 baseEnd_1862369 := by
    simpa [prefixWord, tailWord_1862369, baseEnd_1862369] using wordTrace_append hprefix tailTrace_1862369
  have hstable : (prefixWord ++ tailWord_1862369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862369).length < 2 ^ (prefixWord ++ tailWord_1862369).sum := by decide
  have hdescent : baseEnd_1862369 < baseStart_1862369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862385 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1862385 : Nat := 118140960795 + 1862385 * 2 ^ 59
def prefixEnd_1862385 : Nat := 4983230072969 + 3 ^ 40 * 1862385 * 2
def baseEnd_1862385 : Nat := 956298668723801143822553

theorem tailTrace_1862385 : CollatzResearch.WordTrace tailWord_1862385 prefixEnd_1862385 956298668723801143822553 := by
  unfold tailWord_1862385
  simp only [CollatzResearch.WordTrace]
  refine ⟨67926761357904689880260609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45284507571936459920173739 67926761357904689880260609)
  ·
    refine ⟨50945071018428517410195457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67926761357904689880260609 50945071018428517410195457)
    ·
      refine ⟨38208803263821388057646593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50945071018428517410195457 38208803263821388057646593)
      ·
        refine ⟨28656602447866041043234945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38208803263821388057646593 28656602447866041043234945)
        ·
          refine ⟨21492451835899530782426209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28656602447866041043234945 21492451835899530782426209)
          ·
            refine ⟨16119338876924648086819657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21492451835899530782426209 16119338876924648086819657)
            ·
              refine ⟨12089504157693486065114743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16119338876924648086819657 12089504157693486065114743)
              ·
                refine ⟨18134256236540229097672115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12089504157693486065114743 18134256236540229097672115)
                ·
                  refine ⟨27201384354810343646508173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18134256236540229097672115 27201384354810343646508173)
                  ·
                    refine ⟨10200519133053878867440565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27201384354810343646508173 10200519133053878867440565)
                    ·
                      refine ⟨956298668723801143822553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10200519133053878867440565 956298668723801143822553)
                      ·
                        rfl

theorem cell23_1862385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1862385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862385 prefixEnd_1862385 := by exact prefixLift 1862385
  have htrace : WordTrace (prefixWord ++ tailWord_1862385) baseStart_1862385 baseEnd_1862385 := by
    simpa [prefixWord, tailWord_1862385, baseEnd_1862385] using wordTrace_append hprefix tailTrace_1862385
  have hstable : (prefixWord ++ tailWord_1862385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862385).length < 2 ^ (prefixWord ++ tailWord_1862385).sum := by decide
  have hdescent : baseEnd_1862385 < baseStart_1862385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862386 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_1862386 : Nat := 118140960795 + 1862386 * 2 ^ 59
def prefixEnd_1862386 : Nat := 4983230072969 + 3 ^ 40 * 1862386 * 2
def baseEnd_1862386 : Nat := 956299182204455639910049

theorem tailTrace_1862386 : CollatzResearch.WordTrace tailWord_1862386 prefixEnd_1862386 956299182204455639910049 := by
  unfold tailWord_1862386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16981699457725266762761753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45284531887267378034031341 16981699457725266762761753)
  ·
    refine ⟨12736274593293950072071315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16981699457725266762761753 12736274593293950072071315)
    ·
      refine ⟨19104411889940925108106973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12736274593293950072071315 19104411889940925108106973)
      ·
        refine ⟨7164154458727846915540115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19104411889940925108106973 7164154458727846915540115)
        ·
          refine ⟨10746231688091770373310173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7164154458727846915540115 10746231688091770373310173)
          ·
            refine ⟨4029836883034413889991315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10746231688091770373310173 4029836883034413889991315)
            ·
              refine ⟨6044755324551620834986973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029836883034413889991315 6044755324551620834986973)
              ·
                refine ⟨2266783246706857813120115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6044755324551620834986973 2266783246706857813120115)
                ·
                  refine ⟨3400174870060286719680173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266783246706857813120115 3400174870060286719680173)
                  ·
                    refine ⟨1275065576272607519880065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3400174870060286719680173 1275065576272607519880065)
                    ·
                      refine ⟨956299182204455639910049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275065576272607519880065 956299182204455639910049)
                      ·
                        rfl

theorem cell23_1862386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_1862386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862386 prefixEnd_1862386 := by exact prefixLift 1862386
  have htrace : WordTrace (prefixWord ++ tailWord_1862386) baseStart_1862386 baseEnd_1862386 := by
    simpa [prefixWord, tailWord_1862386, baseEnd_1862386] using wordTrace_append hprefix tailTrace_1862386
  have hstable : (prefixWord ++ tailWord_1862386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862386).length < 2 ^ (prefixWord ++ tailWord_1862386).sum := by decide
  have hdescent : baseEnd_1862386 < baseStart_1862386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862472 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_1862472 : Nat := 118140960795 + 1862472 * 2 ^ 59
def prefixEnd_1862472 : Nat := 4983230072969 + 3 ^ 40 * 1862472 * 2
def baseEnd_1862472 : Nat := 956343341540742303434653

theorem tailTrace_1862472 : CollatzResearch.WordTrace tailWord_1862472 prefixEnd_1862472 956343341540742303434653 := by
  unfold tailWord_1862472
  simp only [CollatzResearch.WordTrace]
  refine ⟨33964967254294751869338835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45286623005726335825785113 33964967254294751869338835)
  ·
    refine ⟨50947450881442127804008253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33964967254294751869338835 50947450881442127804008253)
    ·
      refine ⟨19105294080540797926503095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50947450881442127804008253 19105294080540797926503095)
      ·
        refine ⟨28657941120811196889754643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19105294080540797926503095 28657941120811196889754643)
        ·
          refine ⟨42986911681216795334631965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28657941120811196889754643 42986911681216795334631965)
          ·
            refine ⟨16120091880456298250486987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42986911681216795334631965 16120091880456298250486987)
            ·
              refine ⟨24180137820684447375730481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16120091880456298250486987 24180137820684447375730481)
              ·
                refine ⟨18135103365513335531797861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24180137820684447375730481 18135103365513335531797861)
                ·
                  refine ⟨3400331881033750412212099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18135103365513335531797861 3400331881033750412212099)
                  ·
                    refine ⟨5100497821550625618318149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3400331881033750412212099 5100497821550625618318149)
                    ·
                      refine ⟨956343341540742303434653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5100497821550625618318149 956343341540742303434653)
                      ·
                        rfl

theorem cell23_1862472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_1862472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862472 prefixEnd_1862472 := by exact prefixLift 1862472
  have htrace : WordTrace (prefixWord ++ tailWord_1862472) baseStart_1862472 baseEnd_1862472 := by
    simpa [prefixWord, tailWord_1862472, baseEnd_1862472] using wordTrace_append hprefix tailTrace_1862472
  have hstable : (prefixWord ++ tailWord_1862472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862472).length < 2 ^ (prefixWord ++ tailWord_1862472).sum := by decide
  have hdescent : baseEnd_1862472 < baseStart_1862472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862475 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 5]
def baseStart_1862475 : Nat := 118140960795 + 1862475 * 2 ^ 59
def prefixEnd_1862475 : Nat := 4983230072969 + 3 ^ 40 * 1862475 * 2
def baseEnd_1862475 : Nat := 956344881982705791697139

theorem tailTrace_1862475 : CollatzResearch.WordTrace tailWord_1862475 prefixEnd_1862475 956344881982705791697139 := by
  unfold tailWord_1862475
  simp only [CollatzResearch.WordTrace]
  refine ⟨67930043927578635251036879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45286695951719090167357919 67930043927578635251036879)
  ·
    refine ⟨101895065891367952876555319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67930043927578635251036879 101895065891367952876555319)
    ·
      refine ⟨152842598837051929314832979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101895065891367952876555319 152842598837051929314832979)
      ·
        refine ⟨229263898255577893972249469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152842598837051929314832979 229263898255577893972249469)
        ·
          refine ⟨85973961845841710239593551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229263898255577893972249469 85973961845841710239593551)
          ·
            refine ⟨128960942768762565359390327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85973961845841710239593551 128960942768762565359390327)
            ·
              refine ⟨193441414153143848039085491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128960942768762565359390327 193441414153143848039085491)
              ·
                refine ⟨290162121229715772058628237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193441414153143848039085491 290162121229715772058628237)
                ·
                  refine ⟨108810795461143414521985589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290162121229715772058628237 108810795461143414521985589)
                  ·
                    refine ⟨10201012074482195111436149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108810795461143414521985589 10201012074482195111436149)
                    ·
                      refine ⟨956344881982705791697139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10201012074482195111436149 956344881982705791697139)
                      ·
                        rfl

theorem cell23_1862475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_1862475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862475 prefixEnd_1862475 := by exact prefixLift 1862475
  have htrace : WordTrace (prefixWord ++ tailWord_1862475) baseStart_1862475 baseEnd_1862475 := by
    simpa [prefixWord, tailWord_1862475, baseEnd_1862475] using wordTrace_append hprefix tailTrace_1862475
  have hstable : (prefixWord ++ tailWord_1862475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862475).length < 2 ^ (prefixWord ++ tailWord_1862475).sum := by decide
  have hdescent : baseEnd_1862475 < baseStart_1862475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862489 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 4]
def baseStart_1862489 : Nat := 118140960795 + 1862489 * 2 ^ 59
def prefixEnd_1862489 : Nat := 4983230072969 + 3 ^ 40 * 1862489 * 2
def baseEnd_1862489 : Nat := 956352070711868736922075

theorem tailTrace_1862489 : CollatzResearch.WordTrace tailWord_1862489 prefixEnd_1862489 956352070711868736922075 := by
  unfold tailWord_1862489
  simp only [CollatzResearch.WordTrace]
  refine ⟨67930554549527915642046521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45287036366351943761364347 67930554549527915642046521)
  ·
    refine ⟨50947915912145936731534891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67930554549527915642046521 50947915912145936731534891)
    ·
      refine ⟨76421873868218905097302337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50947915912145936731534891 76421873868218905097302337)
      ·
        refine ⟨57316405401164178822976753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76421873868218905097302337 57316405401164178822976753)
        ·
          refine ⟨42987304050873134117232565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57316405401164178822976753 42987304050873134117232565)
          ·
            refine ⟨4030059754769356323490553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42987304050873134117232565 4030059754769356323490553)
            ·
              refine ⟨3022544816077017242617915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030059754769356323490553 3022544816077017242617915)
              ·
                refine ⟨4533817224115525863926873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022544816077017242617915 4533817224115525863926873)
                ·
                  refine ⟨3400362918086644397945155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4533817224115525863926873 3400362918086644397945155)
                  ·
                    refine ⟨5100544377129966596917733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3400362918086644397945155 5100544377129966596917733)
                    ·
                      refine ⟨956352070711868736922075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5100544377129966596917733 956352070711868736922075)
                      ·
                        rfl

theorem cell23_1862489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_1862489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862489 prefixEnd_1862489 := by exact prefixLift 1862489
  have htrace : WordTrace (prefixWord ++ tailWord_1862489) baseStart_1862489 baseEnd_1862489 := by
    simpa [prefixWord, tailWord_1862489, baseEnd_1862489] using wordTrace_append hprefix tailTrace_1862489
  have hstable : (prefixWord ++ tailWord_1862489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862489).length < 2 ^ (prefixWord ++ tailWord_1862489).sum := by decide
  have hdescent : baseEnd_1862489 < baseStart_1862489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862512 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 6]
def baseStart_1862512 : Nat := 118140960795 + 1862512 * 2 ^ 59
def prefixEnd_1862512 : Nat := 4983230072969 + 3 ^ 40 * 1862512 * 2
def baseEnd_1862512 : Nat := 106262653418546905214941

theorem tailTrace_1862512 : CollatzResearch.WordTrace tailWord_1862512 prefixEnd_1862512 106262653418546905214941 := by
  unfold tailWord_1862512
  simp only [CollatzResearch.WordTrace]
  refine ⟨33965696714222295285066895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45287595618963060380089193 33965696714222295285066895)
  ·
    refine ⟨50948545071333442927600343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33965696714222295285066895 50948545071333442927600343)
    ·
      refine ⟨76422817607000164391400515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50948545071333442927600343 76422817607000164391400515)
      ·
        refine ⟨114634226410500246587100773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76422817607000164391400515 114634226410500246587100773)
        ·
          refine ⟨21493917451968796235081395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114634226410500246587100773 21493917451968796235081395)
          ·
            refine ⟨32240876177953194352622093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21493917451968796235081395 32240876177953194352622093)
            ·
              refine ⟨12090328566732447882233285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32240876177953194352622093 12090328566732447882233285)
              ·
                refine ⟨2266936606262333977918741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12090328566732447882233285 2266936606262333977918741)
                ·
                  refine ⟨106262653418546905214941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2266936606262333977918741 106262653418546905214941)
                  ·
                    rfl

theorem cell23_1862512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 6].length) (baseStart_1862512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862512 prefixEnd_1862512 := by exact prefixLift 1862512
  have htrace : WordTrace (prefixWord ++ tailWord_1862512) baseStart_1862512 baseEnd_1862512 := by
    simpa [prefixWord, tailWord_1862512, baseEnd_1862512] using wordTrace_append hprefix tailTrace_1862512
  have hstable : (prefixWord ++ tailWord_1862512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862512).length < 2 ^ (prefixWord ++ tailWord_1862512).sum := by decide
  have hdescent : baseEnd_1862512 < baseStart_1862512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862522 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_1862522 : Nat := 118140960795 + 1862522 * 2 ^ 59
def prefixEnd_1862522 : Nat := 4983230072969 + 3 ^ 40 * 1862522 * 2
def baseEnd_1862522 : Nat := 956369015573467107809423

theorem tailTrace_1862522 : CollatzResearch.WordTrace tailWord_1862522 prefixEnd_1862522 956369015573467107809423 := by
  unfold tailWord_1862522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16982939539602090569499455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45287838772272241518665213 16982939539602090569499455)
  ·
    refine ⟨25474409309403135854249183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16982939539602090569499455 25474409309403135854249183)
    ·
      refine ⟨38211613964104703781373775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25474409309403135854249183 38211613964104703781373775)
      ·
        refine ⟨57317420946157055672060663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38211613964104703781373775 57317420946157055672060663)
        ·
          refine ⟨85976131419235583508090995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57317420946157055672060663 85976131419235583508090995)
          ·
            refine ⟨128964197128853375262136493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85976131419235583508090995 128964197128853375262136493)
            ·
              refine ⟨48361573923320015723301185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128964197128853375262136493 48361573923320015723301185)
              ·
                refine ⟨36271180442490011792475889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48361573923320015723301185 36271180442490011792475889)
                ·
                  refine ⟨27203385331867508844356917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36271180442490011792475889 27203385331867508844356917)
                  ·
                    refine ⟨2550317374862578954158461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27203385331867508844356917 2550317374862578954158461)
                    ·
                      refine ⟨956369015573467107809423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2550317374862578954158461 956369015573467107809423)
                      ·
                        rfl

theorem cell23_1862522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_1862522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862522 prefixEnd_1862522 := by exact prefixLift 1862522
  have htrace : WordTrace (prefixWord ++ tailWord_1862522) baseStart_1862522 baseEnd_1862522 := by
    simpa [prefixWord, tailWord_1862522, baseEnd_1862522] using wordTrace_append hprefix tailTrace_1862522
  have hstable : (prefixWord ++ tailWord_1862522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862522).length < 2 ^ (prefixWord ++ tailWord_1862522).sum := by decide
  have hdescent : baseEnd_1862522 < baseStart_1862522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862539 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 3]
def baseStart_1862539 : Nat := 118140960795 + 1862539 * 2 ^ 59
def prefixEnd_1862539 : Nat := 4983230072969 + 3 ^ 40 * 1862539 * 2
def baseEnd_1862539 : Nat := 956377744744593541296845

theorem tailTrace_1862539 : CollatzResearch.WordTrace tailWord_1862539 prefixEnd_1862539 956377744744593541296845 := by
  unfold tailWord_1862539
  simp only [CollatzResearch.WordTrace]
  refine ⟨67932378199346774181366671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45288252132897849454244447 67932378199346774181366671)
  ·
    refine ⟨101898567299020161272050007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67932378199346774181366671 101898567299020161272050007)
    ·
      refine ⟨152847850948530241908075011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101898567299020161272050007 152847850948530241908075011)
      ·
        refine ⟨229271776422795362862112517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152847850948530241908075011 229271776422795362862112517)
        ·
          refine ⟨42988458079274130536646097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229271776422795362862112517 42988458079274130536646097)
          ·
            refine ⟨32241343559455597902484573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42988458079274130536646097 32241343559455597902484573)
            ·
              refine ⟨12090503834795849213431715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32241343559455597902484573 12090503834795849213431715)
              ·
                refine ⟨18135755752193773820147573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12090503834795849213431715 18135755752193773820147573)
                ·
                  refine ⟨1700227101768166295638835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18135755752193773820147573 1700227101768166295638835)
                  ·
                    refine ⟨2550340652652249443458253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1700227101768166295638835 2550340652652249443458253)
                    ·
                      refine ⟨956377744744593541296845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2550340652652249443458253 956377744744593541296845)
                      ·
                        rfl

theorem cell23_1862539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 3].length) (baseStart_1862539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862539 prefixEnd_1862539 := by exact prefixLift 1862539
  have htrace : WordTrace (prefixWord ++ tailWord_1862539) baseStart_1862539 baseEnd_1862539 := by
    simpa [prefixWord, tailWord_1862539, baseEnd_1862539] using wordTrace_append hprefix tailTrace_1862539
  have hstable : (prefixWord ++ tailWord_1862539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862539).length < 2 ^ (prefixWord ++ tailWord_1862539).sum := by decide
  have hdescent : baseEnd_1862539 < baseStart_1862539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862599 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_1862599 : Nat := 118140960795 + 1862599 * 2 ^ 59
def prefixEnd_1862599 : Nat := 4983230072969 + 3 ^ 40 * 1862599 * 2
def baseEnd_1862599 : Nat := 956408553583863306546569

theorem tailTrace_1862599 : CollatzResearch.WordTrace tailWord_1862599 prefixEnd_1862599 956408553583863306546569 := by
  unfold tailWord_1862599
  simp only [CollatzResearch.WordTrace]
  refine ⟨67934566579129404428550851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45289711052752936285700567 67934566579129404428550851)
  ·
    refine ⟨101901849868694106642826277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67934566579129404428550851 101901849868694106642826277)
    ·
      refine ⟨19106596850380144995529927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101901849868694106642826277 19106596850380144995529927)
      ·
        refine ⟨28659895275570217493294891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19106596850380144995529927 28659895275570217493294891)
        ·
          refine ⟨42989842913355326239942337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28659895275570217493294891 42989842913355326239942337)
          ·
            refine ⟨32242382185016494679956753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42989842913355326239942337 32242382185016494679956753)
            ·
              refine ⟨24181786638762371009967565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32242382185016494679956753 24181786638762371009967565)
              ·
                refine ⟨9068169989535889128737837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24181786638762371009967565 9068169989535889128737837)
                ·
                  refine ⟨3400563746075958423276689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9068169989535889128737837 3400563746075958423276689)
                  ·
                    refine ⟨2550422809556968817457517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3400563746075958423276689 2550422809556968817457517)
                    ·
                      refine ⟨956408553583863306546569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2550422809556968817457517 956408553583863306546569)
                      ·
                        rfl

theorem cell23_1862599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_1862599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862599 prefixEnd_1862599 := by exact prefixLift 1862599
  have htrace : WordTrace (prefixWord ++ tailWord_1862599) baseStart_1862599 baseEnd_1862599 := by
    simpa [prefixWord, tailWord_1862599, baseEnd_1862599] using wordTrace_append hprefix tailTrace_1862599
  have hstable : (prefixWord ++ tailWord_1862599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862599).length < 2 ^ (prefixWord ++ tailWord_1862599).sum := by decide
  have hdescent : baseEnd_1862599 < baseStart_1862599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862616 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_1862616 : Nat := 118140960795 + 1862616 * 2 ^ 59
def prefixEnd_1862616 : Nat := 4983230072969 + 3 ^ 40 * 1862616 * 2
def baseEnd_1862616 : Nat := 956417282754989740033991

theorem tailTrace_1862616 : CollatzResearch.WordTrace tailWord_1862616 prefixEnd_1862616 956417282754989740033991 := by
  unfold tailWord_1862616
  simp only [CollatzResearch.WordTrace]
  refine ⟨33967593310033908165959851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45290124413378544221279801 33967593310033908165959851)
  ·
    refine ⟨50951389965050862248939777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33967593310033908165959851 50951389965050862248939777)
    ·
      refine ⟨38213542473788146686704833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50951389965050862248939777 38213542473788146686704833)
      ·
        refine ⟨28660156855341110015028625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38213542473788146686704833 28660156855341110015028625)
        ·
          refine ⟨21495117641505832511271469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28660156855341110015028625 21495117641505832511271469)
          ·
            refine ⟨8060669115564687191726801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21495117641505832511271469 8060669115564687191726801)
            ·
              refine ⟨6045501836673515393795101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060669115564687191726801 6045501836673515393795101)
              ·
                refine ⟨2267063188752568272673163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6045501836673515393795101 2267063188752568272673163)
                ·
                  refine ⟨3400594783128852409009745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267063188752568272673163 3400594783128852409009745)
                  ·
                    refine ⟨2550446087346639306757309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3400594783128852409009745 2550446087346639306757309)
                    ·
                      refine ⟨956417282754989740033991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2550446087346639306757309 956417282754989740033991)
                      ·
                        rfl

theorem cell23_1862616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_1862616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862616 prefixEnd_1862616 := by exact prefixLift 1862616
  have htrace : WordTrace (prefixWord ++ tailWord_1862616) baseStart_1862616 baseEnd_1862616 := by
    simpa [prefixWord, tailWord_1862616, baseEnd_1862616] using wordTrace_append hprefix tailTrace_1862616
  have hstable : (prefixWord ++ tailWord_1862616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862616).length < 2 ^ (prefixWord ++ tailWord_1862616).sum := by decide
  have hdescent : baseEnd_1862616 < baseStart_1862616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862626 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1862626 : Nat := 118140960795 + 1862626 * 2 ^ 59
def prefixEnd_1862626 : Nat := 4983230072969 + 3 ^ 40 * 1862626 * 2
def baseEnd_1862626 : Nat := 956422417561534700908945

theorem tailTrace_1862626 : CollatzResearch.WordTrace tailWord_1862626 prefixEnd_1862626 956422417561534700908945 := by
  unfold tailWord_1862626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16983887837507897009945933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45290367566687725359855821 16983887837507897009945933)
  ·
    refine ⟨6368957939065461378729725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16983887837507897009945933 6368957939065461378729725)
    ·
      refine ⟨2388359227149548017023647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6368957939065461378729725 2388359227149548017023647)
      ·
        refine ⟨3582538840724322025535471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388359227149548017023647 3582538840724322025535471)
        ·
          refine ⟨5373808261086483038303207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582538840724322025535471 5373808261086483038303207)
          ·
            refine ⟨8060712391629724557454811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5373808261086483038303207 8060712391629724557454811)
            ·
              refine ⟨12091068587444586836182217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8060712391629724557454811 12091068587444586836182217)
              ·
                refine ⟨9068301440583440127136663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12091068587444586836182217 9068301440583440127136663)
                ·
                  refine ⟨13602452160875160190704995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9068301440583440127136663 13602452160875160190704995)
                  ·
                    refine ⟨20403678241312740286057493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13602452160875160190704995 20403678241312740286057493)
                    ·
                      refine ⟨956422417561534700908945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20403678241312740286057493 956422417561534700908945)
                      ·
                        rfl

theorem cell23_1862626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1862626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862626 prefixEnd_1862626 := by exact prefixLift 1862626
  have htrace : WordTrace (prefixWord ++ tailWord_1862626) baseStart_1862626 baseEnd_1862626 := by
    simpa [prefixWord, tailWord_1862626, baseEnd_1862626] using wordTrace_append hprefix tailTrace_1862626
  have hstable : (prefixWord ++ tailWord_1862626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862626).length < 2 ^ (prefixWord ++ tailWord_1862626).sum := by decide
  have hdescent : baseEnd_1862626 < baseStart_1862626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862644 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1862644 : Nat := 118140960795 + 1862644 * 2 ^ 59
def prefixEnd_1862644 : Nat := 4983230072969 + 3 ^ 40 * 1862644 * 2
def baseEnd_1862644 : Nat := 318810553404438543494621

theorem tailTrace_1862644 : CollatzResearch.WordTrace tailWord_1862644 prefixEnd_1862644 318810553404438543494621 := by
  unfold tailWord_1862644
  simp only [CollatzResearch.WordTrace]
  refine ⟨33968103931983188556969493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45290805242644251409292657 33968103931983188556969493)
  ·
    refine ⟨1592254871811711963607945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33968103931983188556969493 1592254871811711963607945)
    ·
      refine ⟨1194191153858783972705959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1592254871811711963607945 1194191153858783972705959)
      ·
        refine ⟨1791286730788175959058939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194191153858783972705959 1791286730788175959058939)
        ·
          refine ⟨2686930096182263938588409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791286730788175959058939 2686930096182263938588409)
          ·
            refine ⟨2015197572136697953941307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686930096182263938588409 2015197572136697953941307)
            ·
              refine ⟨3022796358205046930911961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015197572136697953941307 3022796358205046930911961)
              ·
                refine ⟨2267097268653785198183971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022796358205046930911961 2267097268653785198183971)
                ·
                  refine ⟨3400645902980677797275957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267097268653785198183971 3400645902980677797275957)
                  ·
                    refine ⟨318810553404438543494621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3400645902980677797275957 318810553404438543494621)
                    ·
                      rfl

theorem cell23_1862644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1862644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862644 prefixEnd_1862644 := by exact prefixLift 1862644
  have htrace : WordTrace (prefixWord ++ tailWord_1862644) baseStart_1862644 baseEnd_1862644 := by
    simpa [prefixWord, tailWord_1862644, baseEnd_1862644] using wordTrace_append hprefix tailTrace_1862644
  have hstable : (prefixWord ++ tailWord_1862644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862644).length < 2 ^ (prefixWord ++ tailWord_1862644).sum := by decide
  have hdescent : baseEnd_1862644 < baseStart_1862644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862699 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 4]
def baseStart_1862699 : Nat := 118140960795 + 1862699 * 2 ^ 59
def prefixEnd_1862699 : Nat := 4983230072969 + 3 ^ 40 * 1862699 * 2
def baseEnd_1862699 : Nat := 956459901649312915296109

theorem tailTrace_1862699 : CollatzResearch.WordTrace tailWord_1862699 prefixEnd_1862699 956459901649312915296109 := by
  unfold tailWord_1862699
  simp only [CollatzResearch.WordTrace]
  refine ⟨67938213878767121507191151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45292142585844747671460767 67938213878767121507191151)
  ·
    refine ⟨101907320818150682260786727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67938213878767121507191151 101907320818150682260786727)
    ·
      refine ⟨152860981227226023391180091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101907320818150682260786727 152860981227226023391180091)
      ·
        refine ⟨229291471840839035086770137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152860981227226023391180091 229291471840839035086770137)
        ·
          refine ⟨171968603880629276315077603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229291471840839035086770137 171968603880629276315077603)
          ·
            refine ⟨257952905820943914472616405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171968603880629276315077603 257952905820943914472616405)
            ·
              refine ⟨6045771230178372995451947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 257952905820943914472616405 6045771230178372995451947)
              ·
                refine ⟨9068656845267559493177921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045771230178372995451947 9068656845267559493177921)
                ·
                  refine ⟨6801492633950669619883441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9068656845267559493177921 6801492633950669619883441)
                  ·
                    refine ⟨5101119475463002214912581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801492633950669619883441 5101119475463002214912581)
                    ·
                      refine ⟨956459901649312915296109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5101119475463002214912581 956459901649312915296109)
                      ·
                        rfl

theorem cell23_1862699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 4].length) (baseStart_1862699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862699 prefixEnd_1862699 := by exact prefixLift 1862699
  have htrace : WordTrace (prefixWord ++ tailWord_1862699) baseStart_1862699 baseEnd_1862699 := by
    simpa [prefixWord, tailWord_1862699, baseEnd_1862699] using wordTrace_append hprefix tailTrace_1862699
  have hstable : (prefixWord ++ tailWord_1862699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862699).length < 2 ^ (prefixWord ++ tailWord_1862699).sum := by decide
  have hdescent : baseEnd_1862699 < baseStart_1862699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862719 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 3]
def baseStart_1862719 : Nat := 118140960795 + 1862719 * 2 ^ 59
def prefixEnd_1862719 : Nat := 4983230072969 + 3 ^ 40 * 1862719 * 2
def baseEnd_1862719 : Nat := 956470171262402837046017

theorem tailTrace_1862719 : CollatzResearch.WordTrace tailWord_1862719 prefixEnd_1862719 956470171262402837046017 := by
  unfold tailWord_1862719
  simp only [CollatzResearch.WordTrace]
  refine ⟨67938943338694664922919211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45292628892463109948612807 67938943338694664922919211)
  ·
    refine ⟨101908415008041997384378817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67938943338694664922919211 101908415008041997384378817)
    ·
      refine ⟨76431311256031498038284113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101908415008041997384378817 76431311256031498038284113)
      ·
        refine ⟨57323483442023623528713085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76431311256031498038284113 57323483442023623528713085)
        ·
          refine ⟨21496306290758858823267407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57323483442023623528713085 21496306290758858823267407)
          ·
            refine ⟨32244459436138288234901111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21496306290758858823267407 32244459436138288234901111)
            ·
              refine ⟨48366689154207432352351667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32244459436138288234901111 48366689154207432352351667)
              ·
                refine ⟨72550033731311148528527501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48366689154207432352351667 72550033731311148528527501)
                ·
                  refine ⟨27206262649241680698197813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72550033731311148528527501 27206262649241680698197813)
                  ·
                    refine ⟨2550587123366407565456045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27206262649241680698197813 2550587123366407565456045)
                    ·
                      refine ⟨956470171262402837046017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2550587123366407565456045 956470171262402837046017)
                      ·
                        rfl

theorem cell23_1862719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_1862719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862719 prefixEnd_1862719 := by exact prefixLift 1862719
  have htrace : WordTrace (prefixWord ++ tailWord_1862719) baseStart_1862719 baseEnd_1862719 := by
    simpa [prefixWord, tailWord_1862719, baseEnd_1862719] using wordTrace_append hprefix tailTrace_1862719
  have hstable : (prefixWord ++ tailWord_1862719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862719).length < 2 ^ (prefixWord ++ tailWord_1862719).sum := by decide
  have hdescent : baseEnd_1862719 < baseStart_1862719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862746 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2]
def baseStart_1862746 : Nat := 118140960795 + 1862746 * 2 ^ 59
def prefixEnd_1862746 : Nat := 4983230072969 + 3 ^ 40 * 1862746 * 2
def baseEnd_1862746 : Nat := 956484035240074231408393

theorem tailTrace_1862746 : CollatzResearch.WordTrace tailWord_1862746 prefixEnd_1862746 956484035240074231408393 := by
  unfold tailWord_1862746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16984982027399212133538023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45293285406397899022768061 16984982027399212133538023)
  ·
    refine ⟨25477473041098818200307035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16984982027399212133538023 25477473041098818200307035)
    ·
      refine ⟨38216209561648227300460553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25477473041098818200307035 38216209561648227300460553)
      ·
        refine ⟨28662157171236170475345415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38216209561648227300460553 28662157171236170475345415)
        ·
          refine ⟨42993235756854255713018123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28662157171236170475345415 42993235756854255713018123)
          ·
            refine ⟨64489853635281383569527185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42993235756854255713018123 64489853635281383569527185)
            ·
              refine ⟨48367390226461037677145389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64489853635281383569527185 48367390226461037677145389)
              ·
                refine ⟨18137771334922889128929521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48367390226461037677145389 18137771334922889128929521)
                ·
                  refine ⟨13603328501192166846697141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18137771334922889128929521 13603328501192166846697141)
                  ·
                    refine ⟨1275312046986765641877857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13603328501192166846697141 1275312046986765641877857)
                    ·
                      refine ⟨956484035240074231408393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275312046986765641877857 956484035240074231408393)
                      ·
                        rfl

theorem cell23_1862746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_1862746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862746 prefixEnd_1862746 := by exact prefixLift 1862746
  have htrace : WordTrace (prefixWord ++ tailWord_1862746) baseStart_1862746 baseEnd_1862746 := by
    simpa [prefixWord, tailWord_1862746, baseEnd_1862746] using wordTrace_append hprefix tailTrace_1862746
  have hstable : (prefixWord ++ tailWord_1862746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862746).length < 2 ^ (prefixWord ++ tailWord_1862746).sum := by decide
  have hdescent : baseEnd_1862746 < baseStart_1862746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862750 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1862750 : Nat := 118140960795 + 1862750 * 2 ^ 59
def prefixEnd_1862750 : Nat := 4983230072969 + 3 ^ 40 * 1862750 * 2
def baseEnd_1862750 : Nat := 956486089162692215758375

theorem tailTrace_1862750 : CollatzResearch.WordTrace tailWord_1862750 prefixEnd_1862750 956486089162692215758375 := by
  unfold tailWord_1862750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492509250197794652162213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45293382667721571478198469 8492509250197794652162213)
  ·
    refine ⟨1592345484412086497280415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8492509250197794652162213 1592345484412086497280415)
    ·
      refine ⟨2388518226618129745920623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592345484412086497280415 2388518226618129745920623)
      ·
        refine ⟨3582777339927194618880935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388518226618129745920623 3582777339927194618880935)
        ·
          refine ⟨5374166009890791928321403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582777339927194618880935 5374166009890791928321403)
          ·
            refine ⟨8061249014836187892482105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374166009890791928321403 8061249014836187892482105)
            ·
              refine ⟨6045936761127140919361579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8061249014836187892482105 6045936761127140919361579)
              ·
                refine ⟨9068905141690711379042369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045936761127140919361579 9068905141690711379042369)
                ·
                  refine ⟨6801678856268033534281777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9068905141690711379042369 6801678856268033534281777)
                  ·
                    refine ⟨5101259142201025150711333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801678856268033534281777 5101259142201025150711333)
                    ·
                      refine ⟨956486089162692215758375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5101259142201025150711333 956486089162692215758375)
                      ·
                        rfl

theorem cell23_1862750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1862750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862750 prefixEnd_1862750 := by exact prefixLift 1862750
  have htrace : WordTrace (prefixWord ++ tailWord_1862750) baseStart_1862750 baseEnd_1862750 := by
    simpa [prefixWord, tailWord_1862750, baseEnd_1862750] using wordTrace_append hprefix tailTrace_1862750
  have hstable : (prefixWord ++ tailWord_1862750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862750).length < 2 ^ (prefixWord ++ tailWord_1862750).sum := by decide
  have hdescent : baseEnd_1862750 < baseStart_1862750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862754 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_1862754 : Nat := 118140960795 + 1862754 * 2 ^ 59
def prefixEnd_1862754 : Nat := 4983230072969 + 3 ^ 40 * 1862754 * 2
def baseEnd_1862754 : Nat := 956488143085310200108357

theorem tailTrace_1862754 : CollatzResearch.WordTrace tailWord_1862754 prefixEnd_1862754 956488143085310200108357 := by
  unfold tailWord_1862754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16985054973391966475110829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45293479929045243933628877 16985054973391966475110829)
  ·
    refine ⟨6369395615021987428166561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16985054973391966475110829 6369395615021987428166561)
    ·
      refine ⟨4777046711266490571124921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6369395615021987428166561 4777046711266490571124921)
      ·
        refine ⟨3582785033449867928343691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4777046711266490571124921 3582785033449867928343691)
        ·
          refine ⟨5374177550174801892515537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582785033449867928343691 5374177550174801892515537)
          ·
            refine ⟨4030633162631101419386653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5374177550174801892515537 4030633162631101419386653)
            ·
              refine ⟨1511487435986663032269995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4030633162631101419386653 1511487435986663032269995)
              ·
                refine ⟨2267231153979994548404993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511487435986663032269995 2267231153979994548404993)
                ·
                  refine ⟨1700423365484995911303745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2267231153979994548404993 1700423365484995911303745)
                  ·
                    refine ⟨1275317524113746933477809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1700423365484995911303745 1275317524113746933477809)
                    ·
                      refine ⟨956488143085310200108357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275317524113746933477809 956488143085310200108357)
                      ·
                        rfl

theorem cell23_1862754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_1862754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862754 prefixEnd_1862754 := by exact prefixLift 1862754
  have htrace : WordTrace (prefixWord ++ tailWord_1862754) baseStart_1862754 baseEnd_1862754 := by
    simpa [prefixWord, tailWord_1862754, baseEnd_1862754] using wordTrace_append hprefix tailTrace_1862754
  have hstable : (prefixWord ++ tailWord_1862754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862754).length < 2 ^ (prefixWord ++ tailWord_1862754).sum := by decide
  have hdescent : baseEnd_1862754 < baseStart_1862754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862776 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 1, 6, 2]
def baseStart_1862776 : Nat := 118140960795 + 1862776 * 2 ^ 59
def prefixEnd_1862776 : Nat := 4983230072969 + 3 ^ 40 * 1862776 * 2
def baseEnd_1862776 : Nat := 956499439659709114033255

theorem tailTrace_1862776 : CollatzResearch.WordTrace tailWord_1862776 prefixEnd_1862776 956499439659709114033255 := by
  unfold tailWord_1862776
  simp only [CollatzResearch.WordTrace]
  refine ⟨33970511149744081828872091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45294014866325442438496121 33970511149744081828872091)
  ·
    refine ⟨50955766724616122743308137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33970511149744081828872091 50955766724616122743308137)
    ·
      refine ⟨38216825043462092057481103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50955766724616122743308137 38216825043462092057481103)
      ·
        refine ⟨57325237565193138086221655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38216825043462092057481103 57325237565193138086221655)
        ·
          refine ⟨85987856347789707129332483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57325237565193138086221655 85987856347789707129332483)
          ·
            refine ⟨128981784521684560693998725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85987856347789707129332483 128981784521684560693998725)
            ·
              refine ⟨24184084597815855130124761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128981784521684560693998725 24184084597815855130124761)
              ·
                refine ⟨18138063448361891347593571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24184084597815855130124761 18138063448361891347593571)
                ·
                  refine ⟨27207095172542837021390357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18138063448361891347593571 27207095172542837021390357)
                  ·
                    refine ⟨1275332586212945485377673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27207095172542837021390357 1275332586212945485377673)
                    ·
                      refine ⟨956499439659709114033255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1275332586212945485377673 956499439659709114033255)
                      ·
                        rfl

theorem cell23_1862776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_1862776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862776 prefixEnd_1862776 := by exact prefixLift 1862776
  have htrace : WordTrace (prefixWord ++ tailWord_1862776) baseStart_1862776 baseEnd_1862776 := by
    simpa [prefixWord, tailWord_1862776, baseEnd_1862776] using wordTrace_append hprefix tailTrace_1862776
  have hstable : (prefixWord ++ tailWord_1862776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862776).length < 2 ^ (prefixWord ++ tailWord_1862776).sum := by decide
  have hdescent : baseEnd_1862776 < baseStart_1862776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862803 : List Nat := [1, 1, 1, 2, 1, 2, 4, 6, 1, 4]
def baseStart_1862803 : Nat := 118140960795 + 1862803 * 2 ^ 59
def prefixEnd_1862803 : Nat := 4983230072969 + 3 ^ 40 * 1862803 * 2
def baseEnd_1862803 : Nat := 318837767879126836131877

theorem tailTrace_1862803 : CollatzResearch.WordTrace tailWord_1862803 prefixEnd_1862803 318837767879126836131877 := by
  unfold tailWord_1862803
  simp only [CollatzResearch.WordTrace]
  refine ⟨67942007070390347268977063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45294671380260231512651375 67942007070390347268977063)
  ·
    refine ⟨101913010605585520903465595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67942007070390347268977063 101913010605585520903465595)
    ·
      refine ⟨152869515908378281355198393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101913010605585520903465595 152869515908378281355198393)
      ·
        refine ⟨114652136931283711016398795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152869515908378281355198393 114652136931283711016398795)
        ·
          refine ⟨171978205396925566524598193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114652136931283711016398795 171978205396925566524598193)
          ·
            refine ⟨128983654047694174893448645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171978205396925566524598193 128983654047694174893448645)
            ·
              refine ⟨24184435133942657792521621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128983654047694174893448645 24184435133942657792521621)
              ·
                refine ⟨1133645396903562084024451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24184435133942657792521621 1133645396903562084024451)
                ·
                  refine ⟨1700468095355343126036677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133645396903562084024451 1700468095355343126036677)
                  ·
                    refine ⟨318837767879126836131877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1700468095355343126036677 318837767879126836131877)
                    ·
                      rfl

theorem cell23_1862803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 4].length) (baseStart_1862803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862803 prefixEnd_1862803 := by exact prefixLift 1862803
  have htrace : WordTrace (prefixWord ++ tailWord_1862803) baseStart_1862803 baseEnd_1862803 := by
    simpa [prefixWord, tailWord_1862803, baseEnd_1862803] using wordTrace_append hprefix tailTrace_1862803
  have hstable : (prefixWord ++ tailWord_1862803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862803).length < 2 ^ (prefixWord ++ tailWord_1862803).sum := by decide
  have hdescent : baseEnd_1862803 < baseStart_1862803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862816 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 6]
def baseStart_1862816 : Nat := 118140960795 + 1862816 * 2 ^ 59
def prefixEnd_1862816 : Nat := 4983230072969 + 3 ^ 40 * 1862816 * 2
def baseEnd_1862816 : Nat := 106279997653987661948119

theorem tailTrace_1862816 : CollatzResearch.WordTrace tailWord_1862816 prefixEnd_1862816 106279997653987661948119 := by
  unfold tailWord_1862816
  simp only [CollatzResearch.WordTrace]
  refine ⟨33971240609671625244600151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45294987479562166992800201 33971240609671625244600151)
  ·
    refine ⟨50956860914507437866900227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33971240609671625244600151 50956860914507437866900227)
    ·
      refine ⟨76435291371761156800350341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50956860914507437866900227 76435291371761156800350341)
      ·
        refine ⟨14331617132205216900065689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76435291371761156800350341 14331617132205216900065689)
        ·
          refine ⟨10748712849153912675049267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14331617132205216900065689 10748712849153912675049267)
          ·
            refine ⟨16123069273730869012573901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748712849153912675049267 16123069273730869012573901)
            ·
              refine ⟨6046150977649075879715213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16123069273730869012573901 6046150977649075879715213)
              ·
                refine ⟨2267306616618403454893205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6046150977649075879715213 2267306616618403454893205)
                ·
                  refine ⟨106279997653987661948119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2267306616618403454893205 106279997653987661948119)
                  ·
                    rfl

theorem cell23_1862816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 6].length) (baseStart_1862816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862816 prefixEnd_1862816 := by exact prefixLift 1862816
  have htrace : WordTrace (prefixWord ++ tailWord_1862816) baseStart_1862816 baseEnd_1862816 := by
    simpa [prefixWord, tailWord_1862816, baseEnd_1862816] using wordTrace_append hprefix tailTrace_1862816
  have hstable : (prefixWord ++ tailWord_1862816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862816).length < 2 ^ (prefixWord ++ tailWord_1862816).sum := by decide
  have hdescent : baseEnd_1862816 < baseStart_1862816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862819 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1862819 : Nat := 118140960795 + 1862819 * 2 ^ 59
def prefixEnd_1862819 : Nat := 4983230072969 + 3 ^ 40 * 1862819 * 2
def baseEnd_1862819 : Nat := 956521519327852445795557

theorem tailTrace_1862819 : CollatzResearch.WordTrace tailWord_1862819 prefixEnd_1862819 956521519327852445795557 := by
  unfold tailWord_1862819
  simp only [CollatzResearch.WordTrace]
  refine ⟨67942590638332382001559511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45295060425554921334373007 67942590638332382001559511)
  ·
    refine ⟨101913885957498573002339267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67942590638332382001559511 101913885957498573002339267)
    ·
      refine ⟨152870828936247859503508901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101913885957498573002339267 152870828936247859503508901)
      ·
        refine ⟨28663280425546473656907919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152870828936247859503508901 28663280425546473656907919)
        ·
          refine ⟨42994920638319710485361879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28663280425546473656907919 42994920638319710485361879)
          ·
            refine ⟨64492380957479565728042819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42994920638319710485361879 64492380957479565728042819)
            ·
              refine ⟨96738571436219348592064229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64492380957479565728042819 96738571436219348592064229)
              ·
                refine ⟨18138482144291127861012043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96738571436219348592064229 18138482144291127861012043)
                ·
                  refine ⟨27207723216436691791518065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18138482144291127861012043 27207723216436691791518065)
                  ·
                    refine ⟨20405792412327518843638549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27207723216436691791518065 20405792412327518843638549)
                    ·
                      refine ⟨956521519327852445795557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20405792412327518843638549 956521519327852445795557)
                      ·
                        rfl

theorem cell23_1862819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1862819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862819 prefixEnd_1862819 := by exact prefixLift 1862819
  have htrace : WordTrace (prefixWord ++ tailWord_1862819) baseStart_1862819 baseEnd_1862819 := by
    simpa [prefixWord, tailWord_1862819, baseEnd_1862819] using wordTrace_append hprefix tailTrace_1862819
  have hstable : (prefixWord ++ tailWord_1862819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862819).length < 2 ^ (prefixWord ++ tailWord_1862819).sum := by decide
  have hdescent : baseEnd_1862819 < baseStart_1862819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862877 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1862877 : Nat := 118140960795 + 1862877 * 2 ^ 59
def prefixEnd_1862877 : Nat := 4983230072969 + 3 ^ 40 * 1862877 * 2
def baseEnd_1862877 : Nat := 956551301205813218870291

theorem tailTrace_1862877 : CollatzResearch.WordTrace tailWord_1862877 prefixEnd_1862877 956551301205813218870291 := by
  unfold tailWord_1862877
  simp only [CollatzResearch.WordTrace]
  refine ⟨67944706072122257907170885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45296470714748171938113923 67944706072122257907170885)
  ·
    refine ⟨12739632388522923357594541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67944706072122257907170885 12739632388522923357594541)
    ·
      refine ⟨4777362145696096259097953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12739632388522923357594541 4777362145696096259097953)
      ·
        refine ⟨3583021609272072194323465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4777362145696096259097953 3583021609272072194323465)
        ·
          refine ⟨2687266206954054145742599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3583021609272072194323465 2687266206954054145742599)
          ·
            refine ⟨4030899310431081218613899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687266206954054145742599 4030899310431081218613899)
            ·
              refine ⟨6046348965646621827920849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030899310431081218613899 6046348965646621827920849)
              ·
                refine ⟨4534761724234966370940637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6046348965646621827920849 4534761724234966370940637)
                ·
                  refine ⟨1700535646588112389102739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4534761724234966370940637 1700535646588112389102739)
                  ·
                    refine ⟨2550803469882168583654109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1700535646588112389102739 2550803469882168583654109)
                    ·
                      refine ⟨956551301205813218870291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2550803469882168583654109 956551301205813218870291)
                      ·
                        rfl

theorem cell23_1862877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1862877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862877 prefixEnd_1862877 := by exact prefixLift 1862877
  have htrace : WordTrace (prefixWord ++ tailWord_1862877) baseStart_1862877 baseEnd_1862877 := by
    simpa [prefixWord, tailWord_1862877, baseEnd_1862877] using wordTrace_append hprefix tailTrace_1862877
  have hstable : (prefixWord ++ tailWord_1862877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862877).length < 2 ^ (prefixWord ++ tailWord_1862877).sum := by decide
  have hdescent : baseEnd_1862877 < baseStart_1862877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862893 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1862893 : Nat := 118140960795 + 1862893 * 2 ^ 59
def prefixEnd_1862893 : Nat := 4983230072969 + 3 ^ 40 * 1862893 * 2
def baseEnd_1862893 : Nat := 318853172298761718756739

theorem tailTrace_1862893 : CollatzResearch.WordTrace tailWord_1862893 prefixEnd_1862893 318853172298761718756739 := by
  unfold tailWord_1862893
  simp only [CollatzResearch.WordTrace]
  refine ⟨67945289640064292639753333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45296859760042861759835555 67945289640064292639753333)
  ·
    refine ⟨6369870903756027434976875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67945289640064292639753333 6369870903756027434976875)
    ·
      refine ⟨9554806355634041152465313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6369870903756027434976875 9554806355634041152465313)
      ·
        refine ⟨7166104766725530864348985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9554806355634041152465313 7166104766725530864348985)
        ·
          refine ⟨5374578575044148148261739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7166104766725530864348985 5374578575044148148261739)
          ·
            refine ⟨8061867862566222222392609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374578575044148148261739 8061867862566222222392609)
            ·
              refine ⟨6046400896924666666794457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8061867862566222222392609 6046400896924666666794457)
              ·
                refine ⟨4534800672693500000095843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6046400896924666666794457 4534800672693500000095843)
                ·
                  refine ⟨6802201009040250000143765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534800672693500000095843 6802201009040250000143765)
                  ·
                    refine ⟨318853172298761718756739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6802201009040250000143765 318853172298761718756739)
                    ·
                      rfl

theorem cell23_1862893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1862893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862893 prefixEnd_1862893 := by exact prefixLift 1862893
  have htrace : WordTrace (prefixWord ++ tailWord_1862893) baseStart_1862893 baseEnd_1862893 := by
    simpa [prefixWord, tailWord_1862893, baseEnd_1862893] using wordTrace_append hprefix tailTrace_1862893
  have hstable : (prefixWord ++ tailWord_1862893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862893).length < 2 ^ (prefixWord ++ tailWord_1862893).sum := by decide
  have hdescent : baseEnd_1862893 < baseStart_1862893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862903 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_1862903 : Nat := 118140960795 + 1862903 * 2 ^ 59
def prefixEnd_1862903 : Nat := 4983230072969 + 3 ^ 40 * 1862903 * 2
def baseEnd_1862903 : Nat := 956564651702830117145171

theorem tailTrace_1862903 : CollatzResearch.WordTrace tailWord_1862903 prefixEnd_1862903 956564651702830117145171 := by
  unfold tailWord_1862903
  simp only [CollatzResearch.WordTrace]
  refine ⟨67945654370028064347617363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45297102913352042898411575 67945654370028064347617363)
  ·
    refine ⟨101918481555042096521426045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67945654370028064347617363 101918481555042096521426045)
    ·
      refine ⟨38219430583140786195534767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101918481555042096521426045 38219430583140786195534767)
      ·
        refine ⟨57329145874711179293302151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38219430583140786195534767 57329145874711179293302151)
        ·
          refine ⟨85993718812066768939953227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57329145874711179293302151 85993718812066768939953227)
          ·
            refine ⟨128990578218100153409929841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85993718812066768939953227 128990578218100153409929841)
            ·
              refine ⟨96742933663575115057447381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128990578218100153409929841 96742933663575115057447381)
              ·
                refine ⟨2267412507740041759158923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96742933663575115057447381 2267412507740041759158923)
                ·
                  refine ⟨3401118761610062638738385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267412507740041759158923 3401118761610062638738385)
                  ·
                    refine ⟨2550839071207546979053789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3401118761610062638738385 2550839071207546979053789)
                    ·
                      refine ⟨956564651702830117145171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2550839071207546979053789 956564651702830117145171)
                      ·
                        rfl

theorem cell23_1862903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_1862903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1862903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1862903 prefixEnd_1862903 := by exact prefixLift 1862903
  have htrace : WordTrace (prefixWord ++ tailWord_1862903) baseStart_1862903 baseEnd_1862903 := by
    simpa [prefixWord, tailWord_1862903, baseEnd_1862903] using wordTrace_append hprefix tailTrace_1862903
  have hstable : (prefixWord ++ tailWord_1862903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862903).length < 2 ^ (prefixWord ++ tailWord_1862903).sum := by decide
  have hdescent : baseEnd_1862903 < baseStart_1862903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
